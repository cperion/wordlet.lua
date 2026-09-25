-- The evaluator: one walker for concrete, normalization and residual execution.
--
-- Layers: a frame that is not residual has no builder at all, so a static attempt cannot leave
-- partial IR behind; a residual frame emits statements into the current Ir.Fn. Both share every
-- expression rule.
local D = require("wordlet.diag")
local S = require("wordlet.schema")
local IR = require("wordlet.ir")
local V = require("wordlet.value")
local Resolve = require("wordlet.resolve")

-- The evaluator is installed on the session class `session.lua` declares: every `Eval:*` method is
-- called on a session, and this module returns that class, so a caller can build one.
local Eval = require("wordlet.session")

local Ir = S.Ir
local U64Kernel = require("wordletkit.u64")
local Machine = require("wordlet.machine")

-- The terminal continuation every converted method ends on: a `nil` continuation ends the chain, and
-- the value it carries is what the direct-style caller that entered the machine sees. It is declared
-- here, before any router that closes over it -- a later `local` would leave that closing over a global.
-- The boundary answer. It forwards *every* value, because two converted methods answer with more
-- than one: `storeTarget` hands back a slot and a place, and a future `joinCallables` hands back
-- a type with two arm values.
local function done(_, ...) return nil, ... end

-- A 64-bit integer is held as two words, because a Lua number cannot hold it. These helpers keep that
-- representation at the edge of the evaluator: the rest works with plain numbers, and a value only
-- goes through them when a width of 64 is involved.

-- The words of a known integer value, sign extending a scalar one.
function wordsOf(value)
    if value.high then return value.high, value.low end
    if value.n < 0 then return 4294967295, value.n + 4294967296 end
    return 0, value.n
end

-- Whether a pair of words is a value of `ty`.
function wordsFit(ty, high, low)
    local minHigh, minLow = S.minWordsOf(ty)
    local maxHigh, maxLow = S.maxWordsOf(ty)
    local compare = ty:isSigned() and U64Kernel.sle or U64Kernel.le
    return compare(minHigh, minLow, high, low) and compare(high, low, maxHigh, maxLow)
end

-- Retags a value with a new type and representation. A runtime value keeps its expression, which is
-- where its value lives; a type that fits a Lua number also keeps a number.
function become(value, ty, high, low)
    -- A conversion produces a value of the target type, not a source literal: a literal may adopt
    -- another operand's type, but `i32(2)` is already i32, so `i32(2) + 3` must let 3 adopt i32
    -- rather than treating both sides as literals and refusing to widen across signedness.
    value.literal = nil
    if V.tag(value) == "runtime" then
        value.ty = ty
        return value
    end
    if ty:isWide() then
        value.ty, value.n, value.high, value.low = ty, nil, high, low
    elseif ty:isSigned() and low >= 2147483648 then
        value.ty, value.n, value.high, value.low = ty, low - 4294967296, nil, nil
    else
        value.ty, value.n, value.high, value.low = ty, low, nil, nil
    end
    return value
end

-- Whether every value of one integer type is a value of another, so the conversion loses nothing.
function fitsAlways(from, to)
    if from == to then return true end
    local minFromHigh, minFromLow = S.minWordsOf(from)
    local maxFromHigh, maxFromLow = S.maxWordsOf(from)
    local minToHigh, minToLow = S.minWordsOf(to)
    local maxToHigh, maxToLow = S.maxWordsOf(to)
    local compare = (from:isSigned() or to:isSigned()) and U64Kernel.sle or U64Kernel.le
    return compare(minToHigh, minToLow, minFromHigh, minFromLow)
        and compare(maxFromHigh, maxFromLow, maxToHigh, maxToLow)
end

-- The two words of a double, as unsigned, which is exact whenever the double is an integer already.
local function wordsOfDouble(d)
    local low = d % 4294967296
    local high = ((d - low) / 4294967296) % 4294967296
    return high, low
end

-- The exclusive upper bound and the inclusive lower bound of an integer type as doubles. Every 32-bit
-- bound is exact and the 64-bit bounds are powers of two, so comparing against them decides the range
-- exactly rather than approximately.
local function floatBounds(ty)
    if ty:isWide() then
        if ty:isSigned() then return 9223372036854775808.0, -9223372036854775808.0 end
        return 18446744073709551616.0, 0.0
    end
    return S.maxOf(ty) + 1, S.minOf(ty)
end

-- A readable form of an integer value's words, for a diagnostic.
function describeWords(ty, high, low)
    if ty:isWide() then return U64Kernel.tostring(high, low, ty:isSigned()) end
    return tostring(high * 4294967296 + low)
end

-- Module-level mutable storage is emitted as a file-scope object, so its ids must not look like
-- the function-local storage the builder allocates for each body.
local MODULE_STORAGE_BASE = 1048576

local ARITH = {
    ["+"] = "Add", ["-"] = "Sub", ["*"] = "Mul", ["/"] = "Div", ["%"] = "Rem", ["^"] = "Pow",
    ["<<"] = "Shl", [">>"] = "Shr", ["&"] = "BitAnd", ["|"] = "BitOr", ["~"] = "BitXor",
}
-- f64 has no remainder, power, shift or bitwise operator: those are integer operations, and IEEE
-- division already answers an infinity or a NaN rather than trapping.
local FLOAT_ARITH = { ["+"] = "Add", ["-"] = "Sub", ["*"] = "Mul", ["/"] = "Div" }
local COMPARE = { ["=="] = "Eq", ["!="] = "Ne", ["<"] = "Lt", ["<="] = "Le", [">"] = "Gt", [">="] = "Ge" }
local COMPOUND = {
    ["+="] = "+", ["-="] = "-", ["*="] = "*", ["/="] = "/", ["%="] = "%", ["^="] = "^",
    ["&="] = "&", ["|="] = "|", ["~="] = "~", ["<<="] = "<<", [">>="] = ">>",
}

-- Scopes --------------------------------------------------------------------------------------

local function scope(parent) return { parent = parent, names = {} } end

local function declare(sc, name, slot, span)
    if sc.names[name] then D.reject("duplicate", "Duplicate declaration of " .. name, span) end
    sc.names[name] = slot
    return slot
end

-- The language's own vocabulary. `PRIMITIVE_TYPES` are the fieldless types a source file names as
-- spellings (`u32`, `bool`, ...); `PRIMITIVE_WORDS` are the type constructors and values built on
-- them. They are ordinary words, not keywords, so the grammar needs no special case -- but a
-- module-level declaration must not reuse one, because that would make the language's own words
-- ambiguous with the program's. A local binding may still shadow any of them, as a local may shadow
-- any outer name.
local PRIMITIVE_TYPES = { "u8", "u16", "u32", "u64", "i32", "i64", "f64", "bool", "unit", "type" }
local PRIMITIVE_WORDS = { "string", "null", "ref", "ptr", "array", "slice", "oneof" }
local RESERVED = {}
for _, list in ipairs({ PRIMITIVE_TYPES, PRIMITIVE_WORDS }) do
    for _, name in ipairs(list) do RESERVED[name] = true end
end

-- A module-level name may not be one of the language's own words. This is a naming rule, not a
-- scoping rule: the word is already bound in every module, so the program would silently change
-- what `u32` or `oneof` means.
local function reserve(name, span)
    if RESERVED[name] then
        D.reject("reserved", name .. " is a built-in Wordlet word; choose another name", span)
    end
end

-- The module a scope belongs to: the root of its chain. A definition's names are resolved there, so
-- each module keeps its own top-level names even when several are compiled together.
local function moduleTop(sc)
    local current = sc
    while current and current.parent do current = current.parent end
    return current
end

local function lookup(sc, name)
    local current = sc
    while current do
        local slot = current.names[name]
        if slot then return slot end
        current = current.parent
    end
end

-- The values bound by an earlier partial application, then the new arguments, in written order.
local function appendArguments(bound, args)
    local values = {}
    for _, value in ipairs(bound or {}) do values[#values + 1] = value end
    for _, value in ipairs(args) do values[#values + 1] = value end
    return values
end

-- A partial application is a compile-time description, so every value bound into it is static. A
-- builtin names no parameter, so its message names none either.
local function requireStatic(values, span, def)
    for index, value in ipairs(values) do
        if not V.isStatic(value) then
            if def == nil then D.reject("static-required", "A partial argument must be static", span) end
            D.reject("static-required", "Partial application needs a static value for parameter "
                .. def.params[index].name.text, span)
        end
    end
end

-- A frame is one context per body construction. `residual` is the layer: a residual frame emits
-- into the current Ir.Fn, and a frame that is not residual runs the same rules with no builder at
-- all, so a static attempt cannot leave partial IR behind.
local Frame = {}
Frame.__index = Frame

-- An arm is a nested list inside the enclosing body: an if or match arm, or a condition's branch.
-- It runs in the same body, so it inherits every field the enclosing frame carries — the tail flag,
-- the expected result, the pending deferred actions — and only the list it builds changes. Copying
-- all fields is what keeps a field added later from being forgotten here; `terminated` is reset
-- because it describes a list, and this list has not ended.
function Frame:arm(list)
    local child = setmetatable({}, Frame)
    for key, value in pairs(self) do child[key] = value end
    child.body = list
    child.terminated = nil
    return child
end

-- Two ways to enter a body: with no builder at all (normalization, and the reference
-- interpreter's own walk), or emitting into the Ir.Fn this frame is building.
function Eval:staticFrame(sc, span)
    return setmetatable({ session = self, residual = false, scope = sc, span = span }, Frame)
end

function Eval:residualFrame(sc, span)
    return setmetatable({ session = self, residual = true, scope = sc, span = span }, Frame)
end

-- Top level -----------------------------------------------------------------------------------

function Eval:load(program)
    local top = scope(nil)
    self.top = top
    for _, decl in ipairs(program.declarations) do
        if decl.kind == "ForeignDecl" then
            reserve(decl.def.name.text, decl.span)
            local slot = declare(top, decl.def.name.text,
                { kind = "word", name = decl.def.name.text }, decl.span)
            slot.def = self:foreignDef(decl.def, top)
        elseif decl.kind == "WordDecl" then
            reserve(decl.def.name.text, decl.span)
            local slot = declare(top, decl.def.name.text, { kind = "word", name = decl.def.name.text }, decl.span)
            slot.def = self:define(decl.def, top, nil)
        elseif decl.kind == "UseDecl" then
            -- The loader resolves every import before this runs and declares the namespace itself.
            goto continue
        else
            -- Every binder of a top-level `let` gets a slot, and the slots of one definition share its
            -- evaluation so a result vector is distributed exactly as a local binding's is.
            local slots = {}
            for index, binder in ipairs(decl.def.binders) do
                reserve(binder.name.text, binder.span)
                local slot = declare(top, binder.name.text,
                    { kind = "value", name = binder.name.text, decl = decl, scope = top, binderIndex = index },
                    binder.span)
                -- A file-scope binding outlives every activation, which is what makes it a legal
                -- reference target in both modes: residual code promotes it to named module storage and
                -- the interpreter already holds its record.
                slot.atTop = true
                slots[index] = slot
            end
            for _, slot in ipairs(slots) do slot.binders = slots end
        end
        ::continue::
    end
    for _, name in ipairs(PRIMITIVE_TYPES) do
        declare(top, name, { kind = "value", name = name, value = V.type(S[name]) })
    end
    -- `ref(T)` is a type and `ref(place)` is a reference to that place. Both are the same ordinary
    -- word, dispatched on whether the argument is a type value or a place, so no new syntax is
    -- needed and the builtin is applied, supplied and checked like any other word.
    local refBuiltin = self:builtin("ref", { { name = "target" } }, function(engine, ctx, values, span)
        local target = values[1]
        local ty = engine:asType(target, span)
        if ty then return V.type(S.ref(engine:canonicalize(ty))) end
        return engine:makeReference(ctx, target, span)
    end)
    -- A reference must name a place, and only the argument expression says whether that place has
    -- an identity that outlives the reference, so `ref` needs the expression as well as the value.
    refBuiltin.refOf = true
    -- `ptr(T)` is a type and `ptr(place)` is an unchecked address to that place: one word, like `ref`,
    -- dispatched the same way. It is the only place a lifetime is deliberately written off.
    local ptrBuiltin = self:builtin("ptr", { { name = "target" } }, function(engine, ctx, values, span)
        local ty = engine:asType(values[1], span)
        if not ty then D.reject("type-required", "ptr needs an element type or a place", span) end
        S.checkRuntime(ty, span)
        return V.type(S.ptr(engine:canonicalize(ty)))
    end)
    ptrBuiltin.ptrOf = true
    declare(top, "ptr", { kind = "word", name = "ptr", def = ptrBuiltin })
    -- `null(T)` is the null `ptr(T)`. There is no null reference, so a pointer is the only thing it
    -- can make, and it needs runtime code because an address has no compile-time value.
    declare(top, "null", { kind = "word", name = "null",
        def = self:builtin("null", { { name = "type" } }, function(engine, ctx, values, span)
            local ty = engine:asType(values[1], span)
            if not ty then D.reject("type-required", "null needs an element type, as in null(u8)", span) end
            local target = engine:canonicalize(ty)
            -- `ptr(T)` is the runtime value, so the pointer is what must be representable, not `T`:
            -- a named record is a fine target even though it is not itself a runtime value.
            local pointer = S.ptr(target)
            S.checkRuntime(pointer, span)
            if not ctx.residual then
                D.reject("runtime-in-normalization",
                    "A null pointer exists only in compiled code", span)
            end
            return V.runtime(ctx.builder:nullPtr(pointer), pointer)
        end) })
    declare(top, "ref", { kind = "word", name = "ref", def = refBuiltin })
    -- `oneof` builds a sum type from its `cases` requirement: a keyed schema whose fields are the
    -- alternatives. Nothing new is needed in the grammar: member selection names a constructor and
    -- keyed application matches on the tag.
    -- `array(T, N)` is a type: N elements of T, with the length part of the type so a static index is
    -- checked while compiling and only a run-time index needs a bounds guard.
    declare(top, "array", { kind = "word", name = "array",
        -- The element is a type, so it is resolved on the type path: that is what lets a definition
        -- mention itself through an array and be told it is a type cycle rather than an eager demand.
        def = self:builtin("array", { { name = "element", isType = true }, { name = "length" } },
            function(engine, ctx, values, span)
                local element = engine:asType(values[1], span)
                if not element then
                    D.reject("type-required", "array needs an element type", span)
                end
                -- A named cell is what an open definition hands back while its own layout is being
                -- computed. It is a placeholder rather than a value, so it is allowed through here and
                -- judged by the cycle checker when the definition is sealed; anything else must be a
                -- type a value can actually have.
                if not S.hasNamed(element) then S.checkRuntime(element, span) end
                local length = values[2]
                if not V.isInteger(length) or length.ty ~= S.u32 then
                    D.reject("type-required", "array needs a length as a literal u32", span)
                end
                if length.n < 1 then
                    D.reject("array-length", "An array holds at least one element", span)
                end
                return V.type(S.array(element, length.n))
            end) })
    -- `string` is the byte slice: text is an array of bytes with a runtime length, not a separate
    -- kind of value, so it needs no rule of its own.
    declare(top, "string", { kind = "value", name = "string", value = V.type(S.string) })
    -- `slice(T)` is a type and `slice(array)` is a view of that array. One word, dispatched on
    -- whether its argument is a type value or a storage array, exactly as `ref` is.
    local sliceBuiltin = self:builtin("slice", { { name = "source" } }, function(engine, ctx, values, span)
        local element = engine:asType(values[1], span)
        if not element then
            D.reject("type-required", "slice needs an element type or an array", span)
        end
        S.checkRuntime(element, span)
        return V.type(S.slice(element))
    end)
    -- Only the argument expression says whether the view's storage outlives it, so `slice` needs
    -- the expression as well as the value, exactly as `ref` does.
    sliceBuiltin.sliceOf = true
    declare(top, "slice", { kind = "word", name = "slice", def = sliceBuiltin })
    declare(top, "oneof", { kind = "word", name = "oneof",
        def = self:builtin("oneof", { { name = "cases" } }, function(engine, ctx, values, span)
            local cases = values[1]
            if V.tag(cases) ~= "schema" then
                D.reject("type-required", "oneof needs a keyed schema of alternatives", span)
            end
            local def = cases.def
            local alternatives = {}
            for _, name in ipairs(def.fieldOrder) do alternatives[name] = def.fields[name] end
            if next(alternatives) == nil then
                D.reject("type-required", "oneof needs at least one alternative", span)
            end
            return V.type(S.sum(alternatives))
        end) })
    return top
end

-- Compiles one module. A `use`d module is loaded first by the caller, which passes its own top so
-- this module's names resolve there.
-- The harness's compile driver: load, initialise, resolve the exports, then build an instance for
-- every exported function and run the module initialiser.
function Eval:compileCPS(machine, program, loadedTop, k)
    local top = loadedTop or self:load(program)
    self.top = top
    -- Initialization is explicit and ordered, not an accident of which binding residual code reads first.
    return self:initializeModuleCPS(machine, program, top, function(m)
        local exports = { functions = {}, types = {} }
        local function overTypes(index)
            if index > #program.export.types then
                local compilation = { session = self, exports = exports, functions = {},
                    types = exports.types, foreigns = self.foreigns.order, modules = self.modules }
                local function overInstances(position)
                    if position > #exports.functions then
                        if not (compilation.modules and #compilation.modules > 0) then
                            return k(m, compilation)
                        end
                        return self:moduleInitialiserCPS(m, compilation.modules, program.span,
                            function(m2, initialiser)
                                compilation.modules.initialiser = initialiser
                                compilation.functions[#compilation.functions + 1] = {
                                    name = "init", instance = initialiser, span = program.span,
                                }
                                return k(m2, compilation)
                            end)
                    end
                    local export = exports.functions[position]
                    return self:instanceForCPS(m, export.word.def, export.span, export.word.args, nil,
                        function(m2, instance)
                            compilation.functions[#compilation.functions + 1] = { name = export.name,
                                instance = instance, span = export.span }
                            return overInstances(position + 1)
                        end)
                end
                return overInstances(1)
            end
            local item = program.export.types[index]
            return self:resolveExportItemCPS(m, item, top, function(m2, value)
                local ty = self:asType(value, item.name.span)
                -- Records and sums are both named structures with a C layout a host may need to build.
                if not ty or not (ty:isRecord() or ty:isSum()) then
                    D.reject("type-required", "Exported type " .. item.name.text
                        .. " is not a record or a sum type", item.name.span)
                end
                exports.types[#exports.types + 1] = { name = item.name.text, type = ty, span = item.span }
                return overTypes(index + 1)
            end)
        end
        local function overFunctions(index)
            if index > #program.export.functions then return overTypes(1) end
            local item = program.export.functions[index]
            return self:resolveExportItemCPS(m, item, top, function(m2, value)
                if V.tag(value) ~= "word" then
                    D.reject("function-required", "Exported function " .. item.name.text
                        .. " is not a word", item.name.span)
                end
                exports.functions[#exports.functions + 1] = { name = item.name.text, word = value,
                    span = item.name.span }
                return overFunctions(index + 1)
            end)
        end
        return overFunctions(1)
    end)
end
-- One entry point that assigns every module-level object its starting value. The host calls it
-- before any exported function; it is never called implicitly.

-- The module initialiser body: one store per module, in first-demand order, so the generated
-- `wordletinit` writes each module's storage from its concrete initial value.
function Eval:moduleInitialiserCPS(machine, modules, span, k)
    local target = "wordletinit"
    local builder = IR.builder()
    local body = {}
    local fn = { id = target, role = Ir.Body, hidden = 0, inputs = {}, params = {}, results = {},
        body = body }
    local ctx = self:residualFrame(self.top, span)
    ctx.builder, ctx.body, ctx.fn = builder, body, fn
    local function moduleAt(index)
        if index > #modules then
            builder:emit(body, Ir.Return(S.list({})))
            local instance = { key = "module-init", def = nil, target = target, status = "done",
                results = {}, inputTypes = {}, inputPlan = {}, fn = fn }
            self:registerInstance(instance)
            return k(machine, instance)
        end
        local module = modules[index]
        local fields = {}
        local function done()
            builder:store(body, Ir.Local(module.storage), builder:make(module.type, fields))
            return moduleAt(index + 1)
        end
        if module.type:isArray() then
            local list = module.initial.items or {}
            local function item(position)
                if position > #list then return done() end
                return self:expressionCPS(machine, ctx, list[position], module.type.element,
                    function(m, value)
                        fields[position] = value
                        return item(position + 1)
                    end)
            end
            return item(1)
        end
        local list = module.type.fields
        local function field(position)
            if position > #list then return done() end
            local named = list[position]
            return self:expressionCPS(machine, ctx, module.initial.fields[named.name], named.type,
                function(m, value)
                    fields[position] = value
                    return field(position + 1)
                end)
        end
        return field(1)
    end
    return moduleAt(1)
end

-- One exported item: an alias is the value of its expression, a name is a word or a demanded binding.
function Eval:resolveExportItemCPS(machine, item, top, k)
    if item.kind == "ExportAlias" then
        return self:evalExprCPS(machine, self:staticFrame(top, item.span), item.value, k)
    end
    local name = item.name.text
    local slot = lookup(top, name)
    if not slot then D.reject("unknown-name", "Unknown exported name: " .. name, item.name.span) end
    if slot.kind == "word" then return k(machine, V.word(slot.def, {}, item.span)) end
    return self:demandCPS(machine, slot, item.span, function(m, demanded)
        return k(m, demanded.value)
    end)
end

-- A module-level mutable record that runtime code refers to gets a named storage of its own. The
-- generated artifact declares one file-scope object per such binding and initialises them from
-- `wordlet_init`, which the host calls before using the exported functions.
function Eval:moduleObject(slot, span)
    if slot.module then return slot.module.object end
    local value = slot.value
    -- Module storage ids live in a disjoint range so they can never collide with the
    -- function-local storage ids the builder hands out.
    self.nextModule = self.nextModule + 1
    local storage = Ir.Storage(MODULE_STORAGE_BASE + self.nextModule)
    if value.ty:isArray() then
        local array = V.array(value.ty, nil, Ir.Local(storage))
        array.module = true
        array.backing = value
        self.modules[#self.modules + 1] = {
            storage = storage, type = value.ty, initial = value, name = slot.name,
        }
        slot.module = { object = array }
        return array
    end
    local schema = value.schema or { id = 0, fields = S.fieldsOf(value.ty),
        fieldNames = S.fieldNames(value.ty), statics = {}, readonly = {}, methods = {} }
    local object = V.object(value.ty, Ir.Local(storage), schema)
    object.module = true
    -- The interpreter reads and writes that record directly, so both modes observe one state.
    object.backing = value
    self.modules[#self.modules + 1] = {
        storage = storage, type = value.ty, initial = value, name = slot.name,
    }
    slot.module = { object = object }
    return object
end

-- Declares a `use`d module's namespace in the importing module's top scope.
function Eval:declareNamespace(top, name, value, span)
    return declare(top, name, { kind = "value", name = name, value = value }, span)
end

-- One exported function by name, for a caller that holds no export list.
function Eval:exportedValueCPS(machine, program, name, top, k)
    for _, item in ipairs(program.export.functions) do
        if item.name.text == name then
            return self:resolveExportItemCPS(machine, item, top, k)
        end
    end
    D.reject("unknown-name", "Unknown exported function: " .. tostring(name))
end
-- A builtin word whose terminal is compiler code rather than a source body. It receives the
-- supplied arguments and returns frontend values; it never runs a source terminal.
function Eval:builtin(name, parameters, intrinsic)
    self.nextDef = self.nextDef + 1
    return { id = self.nextDef, name = name, builtin = intrinsic, params = parameters or {},
        lexical = self.top, span = { file = "<builtin>", line = 1, start = 0, finish = 0 } }
end

function Eval:define(node, lexical, fields, label)
    self.nextDef = self.nextDef + 1
    local name = label or (node.name and node.name.text) or ("lambda#" .. self.nextDef)
    local keyed = node.keyed
    local keyedSet = nil
    if keyed ~= nil and #keyed > 0 then
        keyedSet = {}
        for _, param in ipairs(keyed) do keyedSet[param.name.text] = true end
    else
        keyed = nil
    end
    return {
        id = self.nextDef, name = name,
        node = node, span = (node.name and node.name.span) or node.span,
        -- A keyed word's requirements are its keyed parameters, in declaration order; `keyed` marks
        -- that they are supplied by name rather than by position.
        params = keyed or node.params, keyed = keyed, statics = {},
        result = node.result, body = node.body,
        lexical = lexical, fields = fields,
        tailSelf = node.body ~= nil and Resolve.tailCalls(node.body, name, keyedSet),
    }
end

-- Lazy top-level value bindings ----------------------------------------------------------------

-- Demand the value of a binding that no other path has computed yet. The eagerness is what makes a
-- top-level initializer compile-time execution over concrete values, so `demanding` stays set for the
-- nested demands and the outermost one restores it. A failure has to restore that state and the
-- siblings' flags before it propagates, which is what the pushed handler is for: it replaces the
-- `pcall` the direct version needed, and re-raises so an enclosing demand sees the same diagnostic.
function Eval:demandCPS(machine, slot, span, k)
    if slot.kind ~= "value" or slot.value ~= nil then return k(machine, slot) end
    local siblings = slot.binders or { slot }
    if slot.demanding then D.reject("initializer-cycle", "Eager value cycle through " .. slot.name, span) end
    for _, sibling in ipairs(siblings) do
        sibling.demanding = true
        -- A binding that its own type computation demands reserves a cell, so the definition can refer
        -- to itself through an indirection instead of forcing its layout.
        if sibling.cell == nil then
            self.nextCell = self.nextCell + 1
            sibling.cell = sibling.name .. "#" .. tostring(self.nextCell)
        end
        sibling.open = true
    end
    local ctx = self:staticFrame(slot.scope, slot.decl.span)
    -- A top-level initializer is compile-time execution over concrete values, so module storage is
    -- readable and writable here even though residual specialization must not touch it. Nested
    -- demands keep the flag set and the outermost demand restores it.
    local savedDemand = self.demanding
    self.demanding = true
    local function settled()
        self.demanding = savedDemand
        for _, sibling in ipairs(siblings) do
            sibling.demanding = nil
            sibling.open = false
        end
    end
    machine:push("demand", span, slot.name, function(_, diagnostic)
        settled()
        error(diagnostic, 0)
    end)
    return self:evalValueDefCPS(machine, ctx, slot.decl.def, function(m, result)
        machine:pop()
        settled()
        -- Several binders produce a result vector; distribute it as a local result-list binding does,
        -- filling a missing value with unit.
        local values = self:expand(result)
        for index, sibling in ipairs(siblings) do
            sibling.value = values[index] or V.unit()
        end
        for _, sibling in ipairs(siblings) do self:sealCell(sibling, span) end
        return k(m, slot)
    end)
end
-- Top-level initialization runs once, eagerly, in declaration order. The reference interpreter and
-- the compiler both call this, so they observe the same sequence of reads and mutations, and a
-- mutating initializer cannot depend on which binding happened to be referenced first.

-- Module initialization: every top-level binding is demanded in source order, so the initial state is
-- what the program wrote rather than what some later reader happened to force.
function Eval:initializeModuleCPS(machine, program, top, k)
    local function declaration(index)
        if index > #program.declarations then return k(machine) end
        local decl = program.declarations[index]
        if decl.kind ~= "ValueDecl" then return declaration(index + 1) end
        local binder = decl.def.binders[1]
        local slot = binder and lookup(top, binder.name.text)
        if not (slot and slot.atTop) then return declaration(index + 1) end
        return self:demandCPS(machine, slot, decl.span, function(m)
            return declaration(index + 1)
        end)
    end
    return declaration(1)
end
-- Seals a reserved cell with the type the binding computed. A cell that nothing referred to needs no
-- definition, and a definition that mentions its own cell by value rather than through a reference
-- has no finite layout.
function Eval:sealCell(slot, span)
    span = span or (slot.decl and slot.decl.span)
    local ty = self:asType(slot.value, span)
    if ty then
        self.types.cells[slot.cell] = ty
        self.types.byMeaning[S.encode(ty)] = S.named(slot.cell)
    end
    if ty and self.types.referenced[slot.cell] then
        -- A recursive alias must be nominal. The chain is `schema.reachesCell`: a name, or a
        -- reference or pointer to one, is a nominal chain with no layout to anchor it, so following
        -- it back to the cell itself is an infinite type. A slice registers itself before naming its
        -- element, so a slice self-reference is finite and the fold stops there.
        if S.reachesCell(ty, slot.cell, self.types.cells) then
            D.reject("type-cycle", "type " .. slot.name .. " refers to itself with no record or sum "
                .. "to give it a finite layout; a recursive type needs a record or sum boundary", span)
        end
        self:checkNoValueCycle(ty, slot, span)
    end
    return ty
end

-- A cell may only appear behind a reference. Every other occurrence would embed the definition in
-- itself, which no finite layout can represent, and the walk that decides it is `embedsCell`:
-- by-value children only, stopping at every indirection.
function Eval:checkNoValueCycle(ty, slot, span)
    if not S.embedsCell(ty) then return end
    D.reject("type-cycle", "type " .. slot.name .. " contains itself by value; a recursive type "
        .. "needs an indirection boundary, as in ref(" .. slot.name .. ") or ptr(" .. slot.name
        .. ")", span)
end

-- Result adjustment ---------------------------------------------------------------------------

function Eval:first(value)
    if V.tag(value) == "results" then return value.values[1] or V.unit() end
    return value
end
function Eval:expand(value)
    if V.tag(value) == "results" then return value.values end
    return { value }
end

-- A returned value list. Each expression is a step, and the last one may produce a result vector,
-- which is spliced in place exactly as the direct version did.
function Eval:evalListCPS(machine, ctx, exprs, k)
    local values = {}
    local function item(index)
        if index > #exprs then return k(machine, values) end
        return self:evalExpectedCPS(machine, ctx, exprs[index], ctx.expectedResult, function(m, value)
            if index < #exprs then
                values[#values + 1] = self:first(value)
            else
                for _, part in ipairs(self:expand(value)) do values[#values + 1] = part end
            end
            return item(index + 1)
        end)
    end
    return item(1)
end

-- Materialisation -------------------------------------------------------------------------------

-- A record value or object becomes an immutable Make of its fields.

-- A record's construction expression. A record that has not demanded a place is already its Make, so
-- crossing a boundary copies that immutable expression instead of reading each field back.
-- A record's construction expression. A record that has not demanded a place is already its Make, so
-- crossing a boundary copies that immutable expression instead of reading each field back.
function Eval:recordExprCPS(machine, ctx, value, k)
    -- A record that has not demanded a place is already its construction expression, so crossing a
    -- boundary copies that immutable Make instead of reading each field back and rebuilding it.
    if value.expr then return k(machine, value.expr) end
    local ty = value.ty
    local fields = {}
    local function field(index)
        if index > #ty.fields then return k(machine, ctx.builder:make(ty, fields)) end
        local named = ty.fields[index]
        return self:fieldExprCPS(machine, ctx, value, named.name, function(m, expr)
            fields[index] = expr
            return field(index + 1)
        end)
    end
    return field(1)
end
-- A returned value must not refer to storage that dies with this activation.
function Eval:checkReturn(values, span)
    for _, value in ipairs(values) do
        if V.tag(value) == "ref" and value.tied then D.reject("ref-escape", self:refEscapeMessage(), span) end
        if self:isBorrowed(value) then
            D.reject("borrow-escape",
                "A value that refers to this activation's storage cannot be returned; the borrow "
                .. "would outlive it", span)
        end
    end
end

-- One field as an expression: a projection of the Make, or a read of storage.
function Eval:fieldExprCPS(machine, ctx, value, name, k)
    if V.tag(value) == "record" then
        return self:expressionCPS(machine, ctx, value.fields[name], nil, k)
    end
    local ty = S.field(value.ty, name)
    -- A field of an unmaterialised record is a pure projection of its construction expression; once a
    -- demand clears that expression, and for a spilled SSA value, storage is read instead.
    if value.expr then return k(machine, V.runtime(ctx.builder:get(value.expr, name, ty), ty)) end
    local place = Ir.Project(value.place, Ir.Field(name))
    local read = ctx.builder:read(ctx.body, ty, place)
    return k(machine, ctx.builder:ref(read, ty))
end

-- Wraps a payload in its alternative. Under the interpreter the payload is a value; in residual
-- code it becomes ConstructVariant, which the backend lowers to a tag plus a union member.

-- A variant value, tagged and (in residual code) constructed.
function Eval:makeVariantCPS(machine, ctx, ctor, payload, span, k)
    -- A unit alternative carries no payload, but the frontend value still holds the unit value so
    -- that knownness and matching treat it like any other alternative.
    local unit = ctor.caseType == S.unit and payload == nil
    local value = payload or V.unit()
    if not ctx.residual then
        return k(machine, V.variant(ctor.sum, ctor.case, value))
    end
    local id = ctx.builder:valueId()
    local function emit(payloadExpr)
        ctx.builder:emit(ctx.body, Ir.ConstructVariant(id, ctor.sum, ctor.case, payloadExpr))
        return k(machine, V.variant(ctor.sum, ctor.case, value, ctx.builder:ref(id, ctor.sum)))
    end
    if unit then return emit(nil) end
    return self:expressionCPS(machine, ctx, payload, ctor.caseType, function(m, payloadExpr)
        return emit(payloadExpr)
    end)
end

-- `value { case = handler, ... }`: every alternative must be covered. A value whose tag is known
-- selects one handler; an opaque variant tests the tag and joins the arms.

-- A sum match. Handler expressions are evaluated in written order, except that a known tag skips
-- unselected lambda literals entirely: constructing a closure would otherwise elaborate its base
-- instance before selection. Non-lambda expressions retain their evaluation/checking behavior.
-- Only the selected handler is invoked for a known tag; an opaque tag elaborates every arm.
function Eval:evalMatchCPS(machine, ctx, base, expr, span, k)
    span = span or expr.span
    local handlers, order = {}, {}
    local selected = V.tag(base) == "variant" and base.case or nil
    local selectedPlan
    local function handler(index)
        if index > #expr.fields then
            for _, name in ipairs(S.casesOf(base.ty)) do
                if handlers[name] == nil then
                    D.reject("variant-match", "Matching must handle every alternative, including " .. name,
                        expr.span)
                end
            end
            for _, name in ipairs(order) do
                if not (selectedPlan and name == selected) and handlers[name] ~= false
                    and not (V.tag(handlers[name]) == "word"
                    or V.tag(handlers[name]) == "closure" or V.tag(handlers[name]) == "method") then
                    D.reject("callable-required", "A match handler must be callable", expr.span)
                end
            end
            if selected then
                local payload = base.payload
                if payload == nil then payload = V.unit() end
                if selectedPlan then
                    return self:invokePreparedLambdaCPS(machine, ctx, selectedPlan, { payload }, span, k)
                end
                return self:supplyCPS(machine, ctx, handlers[selected], { payload }, span, k)
            end
            if not ctx.residual then
                D.reject("runtime-in-normalization", "Matching an opaque variant needs runtime code", span)
            end
            return self:matchResidualCPS(machine, ctx, base, handlers, span, k)
        end
        local entry = expr.fields[index]
        local name = entry.name.text
        if not S.caseOf(base.ty, name) then
            D.reject("unknown-member", "Sum type has no alternative " .. name, entry.name.span)
        end
        if handlers[name] ~= nil then
            D.reject("duplicate", "Alternative " .. name .. " is handled twice", entry.name.span)
        end
        if selected and name ~= selected and entry.value.kind == "Lambda" then
            -- false records syntactic coverage, without capture planning, annotations or body work.
            -- It is distinct from nil (missing), including for duplicate detection above.
            handlers[name] = false
            order[#order + 1] = name
            return handler(index + 1)
        end
        if name == selected and not ctx.residual and entry.value.kind == "Lambda" then
            self:step(entry.value.span)
            return self:prepareLambdaCPS(machine, ctx, entry.value, nil, function(m, plan)
                -- Ineligible environments keep ordinary construction at the written position.
                if #plan.borrowedOrder > 0 or #plan.runtimeOrder > 0 then
                    return self:completeLambdaCPS(m, plan, entry.value.span, function(m2, value)
                        handlers[name] = value
                        order[#order + 1] = name
                        return handler(index + 1)
                    end)
                end
                -- This private plan marks coverage; it never enters the source value channel.
                -- Captures/annotations happen HERE, not after later handler expressions run.
                selectedPlan, handlers[name] = plan, plan
                order[#order + 1] = name
                return handler(index + 1)
            end)
        end
        return self:evalExprCPS(machine, ctx, entry.value, function(m, value)
            handlers[name] = value
            order[#order + 1] = name
            return handler(index + 1)
        end)
    end
    return handler(1)
end


-- The opaque case: test the tag for each alternative, projecting the payload inside its own arm,
-- and join the results through one slot. The last alternative needs no test.
-- Whether two values are the same fully-known scalar. Only scalars have a comparison here; an
-- aggregate's knownness is structural and would not make its components interchangeable.
function Eval:sameKnownScalar(a, b)
    if not (V.isKnown(a) and V.isKnown(b)) or a.ty ~= b.ty then return false end
    local tag = a.tag
    if tag == "int" then
        if a.high ~= nil or b.high ~= nil then return a.high == b.high and a.low == b.low end
        return a.n == b.n
    end
    if tag == "bool" then return a.b == b.b end
    if tag == "float" then
        -- Signed zeros compare equal but are observably different under division.
        return a.n == b.n and (a.n ~= 0 or 1 / a.n == 1 / b.n)
    end
    if tag == "unit" then return true end
    if tag == "string" then return a.bytes == b.bytes end
    return false
end

-- The residual form of a match: one arm list per alternative, one slot per result, one switch on the
-- tag. Each arm's handler is called on the machine, and the arm statements wait for all of them, so the
-- stores are a driver over a flattened (piece, position) list rather than nested loops.
function Eval:matchResidualCPS(machine, ctx, base, handlers, span, k)
    local builder = ctx.builder
    local variant = sumValueId(base)
    local names = S.casesOf(base.ty)
    local pieces, resultTypes = {}, nil
    local function finish()
        -- One slot per result, so a match may yield a result vector rather than only one value.
        local places = {}
        for index, ty in ipairs(resultTypes) do
            places[index] = Ir.Local(builder:var(ctx.body, ty, nil))
        end
        local pending = {}
        for _, piece in ipairs(pieces) do
            if not piece.terminated then
                for position, value in ipairs(piece.values) do
                    pending[#pending + 1] = { piece = piece, position = position, value = value }
                end
            end
        end
        local function store(index)
            if index > #pending then
                -- One switch on the tag. The last alternative carries the fallback flag and is emitted
                -- as C's `default`, so the branch is total and a dense alternative set lowers to a jump
                -- table rather than a chain of compares.
                local cases = {}
                for position, piece in ipairs(pieces) do
                    cases[position] = Ir.Case(piece.name, position == #pieces, S.list(piece.list))
                end
                builder:emit(ctx.body, Ir.Switch(variant, base.ty, S.list(cases)))
                local out = {}
                for position, ty in ipairs(resultTypes) do
                    out[position] = V.runtime(builder:ref(builder:read(ctx.body, ty, places[position]), ty), ty)
                end
                if #out == 1 then return k(machine, out[1]) end
                return k(machine, V.results(out))
            end
            local item = pending[index]
            return self:expressionCPS(machine, item.piece.ctx, item.value, resultTypes[item.position],
                function(m, expr)
                    builder:store(item.piece.list, places[item.position], expr)
                    return store(index + 1)
                end)
        end
        return store(1)
    end
    local function armAt(index)
        if index > #names then return finish() end
        local name = names[index]
        local arm = {}
        local armCtx = ctx:arm(arm)
        local caseType = S.caseOf(base.ty, name)
        local args
        if caseType == S.unit then
            -- The handler still takes one (erased) unit parameter, so the arity matches; the value
            -- itself is never materialised.
            args = { V.unit() }
        else
            local id = builder:valueId()
            builder:emit(arm, Ir.VariantPayload(id, variant, base.ty, name))
            args = { V.runtime(builder:ref(id, caseType), caseType) }
        end
        -- A handler is a callable, so it may return a result vector; the match forwards it.
        return self:supplyCPS(machine, armCtx, handlers[name], args, span, function(m, produced)
            local values = self:expand(produced)
            if resultTypes == nil then
                resultTypes = {}
                for position, value in ipairs(values) do resultTypes[position] = value.ty end
            elseif #values ~= #resultTypes then
                D.reject("branch-result", "Every arm of a match must produce the same number of results: "
                    .. #resultTypes .. " and " .. #values, span)
            else
                for position, value in ipairs(values) do
                    if value.ty ~= resultTypes[position] then
                        D.reject("branch-result", "Every arm of a match must produce the same type: "
                            .. S.encode(resultTypes[position]) .. " and " .. S.encode(value.ty), span)
                    end
                end
            end
            pieces[#pieces + 1] = { name = name, list = arm, ctx = armCtx, values = values,
                terminated = armCtx.terminated }
            return armAt(index + 1)
        end)
    end
    return armAt(1)
end
function sumValueId(value)
    if value.expr and value.expr.kind == "Ref" then return value.expr.value end
    D.bug("sum-value", "An opaque sum value must be an SSA reference")
end

-- An owning callable selected at run time cannot become a non-retaining signature value: the view
-- would have to point at the environment that carries the tag, and a view does not retain it.
function Eval:rejectTaggedErase(span)
    D.reject("callable-erase",
        "A callable selected at run time cannot be erased into a signature, because a view does not "
        .. "retain the environment that carries the tag; call it where it was selected, or select the "
        .. "arm before erasing it", span)
end

-- A callable that reaches storage outside itself cannot travel by value; it is passed as a
-- non-retaining view instead, so the borrow stays tracked to its activation.
function Eval:borrowsStorage(value)
    return V.tag(value) == "closure" and #(value.plan.borrowedOrder or {}) > 0
end

-- References --------------------------------------------------------------------------------------
-- A reference names a place instead of copying it. Only two targets provably outlive every use of a
-- reference: module-level storage, and a place that belongs to an enclosing activation. Anything
-- else is a local or a temporary of this activation, and the reference would outlive it.

-- A named cell resolves to the definition it reserved. Every other type is already its own meaning,
-- so this is the one place recursion has to be unwound for inspection.
function Eval:resolveType(ty, span)
    if ty:isNamed() then
        local cell = self.types.cells[ty.cell]
        if not cell then
            D.bug("type-cell", "A named type cell has no definition: " .. tostring(ty.cell))
        end
        return cell
    end
    return ty
end

-- A sealed recursive definition is named, so every occurrence of that type in a reference has to be
-- the same nominal thing: otherwise the type written inside the definition and the type of an
-- instance built from it would not compare equal.
function Eval:canonicalize(ty)
    local named = self.types.byMeaning and self.types.byMeaning[S.encode(ty)]
    if named then return named end
    if ty:isPtr() then
        local target = self:canonicalize(ty.target)
        if target ~= ty.target then return S.ptr(target) end
        return ty
    end
    if ty:isRef() then
        local target = self:canonicalize(ty.target)
        if target ~= ty.target then return S.ref(target) end
    end
    return ty
end

-- The type an address points at, unwinding the cell a recursive definition reserved. A reference
-- and a raw pointer name their target the same way, so one unwinding serves both.
function Eval:pointeeType(ty)
    local target = S.environmentOf(ty.target)
    if target:isNamed() then target = self:resolveType(target) end
    return target
end

-- Classifies a reference target: "module" for file-scope storage, "enclosing" for a place that
-- belongs to an enclosing activation, and nil for anything this activation owns.
function Eval:referenceTarget(value)
    if V.tag(value) == "record" then
        -- A statically evaluated closure binds its captured receiver as a record value; the closure
        -- itself is what makes that record an enclosing owner rather than a local of this body.
        return value.enclosing and "enclosing" or nil
    end
    if V.tag(value) ~= "object" then return nil end
    -- Module storage is a named file-scope object, so it outlives every activation. A borrowed
    -- capture or a place parameter is the other legal target, and it is marked as enclosing storage
    -- where it is bound rather than being recognised from the shape of its place.
    if value.module or (value.schema and value.schema.module) then return "module" end
    if value.enclosing then return "enclosing" end
    return nil
end

-- A reference names a place, so selecting or storing through it selects that place. A frontend
-- reference therefore behaves exactly like the instance it names.
function Eval:placeObject(value)
    if V.tag(value) ~= "ref" then return nil end
    local target = S.environmentOf(self:resolveType(value.ty.target))
    local schema = value.schema
    if not schema and target:isRecord() then
        schema = { fields = S.fieldsOf(target), fieldNames = S.fieldNames(target),
            statics = {}, readonly = {}, methods = {}, type = target }
    end
    local object = V.object(target, value.place, schema, value.tied)
    object.backing = value.record
    -- Reaching through the reference is reaching the storage it names, so the module rule applies.
    object.module = value.module
    return object
end

-- The place a reference value names, spilling a reference that only exists as an SSA value into
-- storage so it has an address to go through.

-- One dereference of an address.
function Eval:derefPlaceCPS(machine, ctx, value, span, k)
    -- An address is a pointer; `value.place` is where that pointer lives, so the target is
    -- one dereference further on. The pointee type travels with the place, like every other typed
    -- IR node, so the verifier needs no type-cell table to check it.
    local pointee = S.environmentOf(self:pointeeType(value.ty))
    if value.place then return k(machine, Ir.Deref(value.place, pointee)) end
    if not ctx.residual then
        D.reject("runtime-in-normalization", "A runtime reference needs runtime code", span)
    end
    return self:expressionCPS(machine, ctx, value, value.ty, function(m, expr)
        local storage = ctx.builder:var(ctx.body, value.ty, expr)
        return k(m, Ir.Deref(Ir.Local(storage), pointee))
    end)
end

-- `ref(x)`: a reference to the place `x` names. A file-scope binding is module storage, which the
-- interpreter already holds as a record and residual code promotes to a named object, so both modes
-- classify it the same way.
-- The words that build a type out of other types. A definition written with one of these is a type
-- definition, so a demand that arrives while it is open is the recursion knot rather than a value
-- demand; a definition written any other way is a value, and a value that demands itself is an
-- initializer cycle.
local TYPE_CONSTRUCTORS = { ref = true, ptr = true, slice = true, array = true, oneof = true }

-- A binding that is a direct alias of a type constructor -- `let my_ref = ref` -- is a type
-- constructor too, so `let node = my_ref(node)` still recognises the recursion knot. The alias is
-- followed structurally rather than demanded, so this decides without evaluating anything.
local function isTypeConstructor(scope, name, seen)
    if TYPE_CONSTRUCTORS[name] then return true end
    seen = seen or {}
    if seen[name] then return false end
    seen[name] = true
    local slot = lookup(scope, name)
    if not slot or slot.kind ~= "value" or not slot.decl then return false end
    local def = slot.decl.def
    if #def.binders ~= 1 or #def.values ~= 1 then return false end
    local value = def.values[1]
    if value.kind ~= "Reference" then return false end
    return isTypeConstructor(scope, value.name.text, seen)
end

function Eval:isTypeDefinition(slot)
    local def = slot.decl and slot.decl.def
    if not def or #def.binders ~= 1 or #def.values ~= 1 then return false end
    local value = def.values[1]
    if value.kind == "SchemaExpr" then return true end
    return value.kind == "Apply" and value.callee.kind == "Reference"
        and isTypeConstructor(slot.scope or self.top, value.callee.name.text)
end

-- Where a place expression's storage comes from: "module" for a file-scope binding, "enclosing" for
-- storage that belongs to an enclosing activation, and nil for storage this activation owns.

-- Where a place's storage comes from: module storage, the enclosing activation, or nowhere in
-- particular. The walk down a selection chain is a tail call, so a long chain costs one frame.
-- Where a place's storage comes from: module storage, the enclosing activation, or nowhere in
-- particular. The walk down a selection chain is a tail call, so a long chain costs one frame.
function Eval:placeOriginCPS(machine, ctx, expr, k)
    if expr.kind == "Reference" then
        local slot = lookup(ctx.scope, expr.name.text)
        if not slot then return k(machine, nil) end
        if slot.atTop then
            -- A type or a scalar binding has no storage to name.
            return self:demandCPS(machine, slot, expr.span, function(m, demanded)
                local held = demanded.value
                if held and (V.tag(held) == "record" or V.tag(held) == "array") then
                    return k(m, "module")
                end
                return k(m, nil)
            end)
        end
        if slot.kind == "param" then return k(machine, "enclosing") end
        local record = slot.record
        if record and record.module then return k(machine, "module") end
        if record and record.enclosing then return k(machine, "enclosing") end
        return k(machine, nil)
    end
    if expr.kind == "FieldSelect" or expr.kind == "IndexExpr" then
        return self:placeOriginCPS(machine, ctx, expr.base, k)
    end
    return k(machine, nil)
end
-- `ptr(place)` takes the address of a place and writes off its lifetime. Unlike a reference there is no
-- target rule to check, and that is the point: from here the program is responsible, so the one place
-- a lifetime is dropped is spelled rather than inferred.

-- `ptr(x)`: a pointer type when `x` is a type, an address when it is a place. Two of the branches need
-- a child value, so each is a continuation; the address itself is one answered through `k`.
-- `ptr(x)`: a pointer type when `x` is a type, an address when it is a place. The place is probed
-- first -- asking is not an error -- and only when it declines is the expression evaluated to find an
-- instance to spill, which is what the alias case needs.
-- `ptr(x)`: a pointer type when `x` is a type, an address when it is a place. The place is probed
-- first -- asking is not an error -- and only when it declines is the expression evaluated to find an
-- instance to spill, which is what the alias case needs.
function Eval:evalPtrCPS(machine, ctx, expr, k)
    local function afterSlot(m)
        -- Only a non-place expression can be a type, and evaluating a place would read it: taking an
        -- address must not also load what it addresses.
        if expr.kind ~= "Reference" and expr.kind ~= "FieldSelect" and expr.kind ~= "IndexExpr" then
            return self:evalExprCPS(m, ctx, expr, function(m2, value)
                local asType = self:asType(value, expr.span)
                if asType then return k(m2, V.type(S.ptr(self:canonicalize(asType)))) end
                D.reject("type-required", "ptr needs an element type or a place to address", expr.span)
            end)
        end
        if not ctx.residual then
            D.reject("runtime-in-normalization", "A raw pointer exists only in compiled code", expr.span)
        end
        -- A place expression names storage directly, so the address is that place and nothing is read.
        return self:placeOfOrNilCPS(m, ctx, expr, expr.span, function(m2, reached)
            local function answer(m3, place)
                local target = self:canonicalize(place.ty)
                local pointer = S.ptr(target)
                return k(m3, V.runtime(ctx.builder:addr(place.place, pointer), pointer))
            end
            if reached and reached.place then return answer(m2, reached) end
            -- A local binding to an instance is an alias, so its storage is what the address names;
            -- that storage is created here when the instance only exists as a value so far.
            return self:evalExprCPS(m2, ctx, expr, function(m3, held)
                local tag = V.tag(held)
                if tag == "record" then
                    return self:recordPlaceCPS(m3, ctx, held, expr.span, function(m4, place)
                        return answer(m4, { place = place, ty = held.ty })
                    end)
                end
                if tag == "array" then
                    return self:arrayPlaceCPS(m3, ctx, held, expr.span, function(m4, place)
                        return answer(m4, { place = place, ty = held.ty })
                    end)
                end
                D.reject("not-a-place", "ptr needs a place to address", expr.span)
            end)
        end)
    end
    if expr.kind == "Reference" then
        local slot = lookup(ctx.scope, expr.name.text)
        -- `ptr(Node)` inside Node's own definition must not demand Node's layout: a pointer is an
        -- indirection boundary exactly as a reference is, so it names the cell the definition
        -- reserved and the recursion stays finite.
        if slot and slot.open and slot.value == nil and slot.cell and self:isTypeDefinition(slot) then
            self.types.referenced[slot.cell] = true
            return k(machine, V.type(S.ptr(S.named(slot.cell))))
        end
        if slot then
            return self:demandCPS(machine, slot, expr.span, function(m, demanded)
                local held = demanded.value and self:asType(demanded.value, expr.span) or nil
                if held then return k(m, V.type(S.ptr(self:canonicalize(held)))) end
                return afterSlot(m)
            end)
        end
    end
    return afterSlot(machine)
end
-- `ref(x)`: a type when `x` is one, a reference to storage otherwise. The place classification below
-- is the direct walker (`placeOrigin`/`placeOf`/`asType`), which is why only the fallback evaluation
-- is a continuation.
-- `ref(x)`: a type when `x` is one, a reference to storage otherwise. The place is probed first, and
-- the fallback -- evaluate the expression, then reference a named or local object -- is shared by every
-- path that does not settle as a place.
-- `ref(x)`: a type when `x` is one, a reference to storage otherwise. The place is probed first, and
-- the fallback -- evaluate the expression, then reference a named or local object -- is shared by every
-- path that does not settle as a place.
function Eval:evalRefCPS(machine, ctx, expr, k)
    local slot
    if expr.kind == "Reference" then
        slot = lookup(ctx.scope, expr.name.text)
        -- `ref(Node)` inside Node's own definition must not demand Node's layout: it refers to the
        -- cell that definition reserved, which is what makes the recursion finite.
        if slot and slot.open and slot.value == nil and slot.cell and self:isTypeDefinition(slot) then
            self.types.referenced[slot.cell] = true
            return k(machine, V.type(S.ref(S.named(slot.cell))))
        end
    end
    local function fallback(m)
        return self:evalExprCPS(m, ctx, expr, function(m2, value)
            local ty = self:asType(value, expr.span)
            if ty then return k(m2, V.type(S.ref(self:canonicalize(ty)))) end
            if slot and slot.atTop and V.tag(value) == "record" then
                -- A file-scope binding has an identity that outlives every activation, so a reference to
                -- it is a reference to named module storage whichever mode built it.
                return self:makeReferenceCPS(m2, ctx, self:moduleObject(slot, expr.span), expr.span, k)
            end
            return self:makeReferenceCPS(m2, ctx, value, expr.span, k)
        end)
    end
    local function afterHeldType(m)
        -- A place expression names storage directly, so the reference is that place.
        if expr.kind ~= "Reference" and expr.kind ~= "FieldSelect" and expr.kind ~= "IndexExpr" then
            return fallback(m)
        end
        return self:placeOriginCPS(m, ctx, expr, function(m2, origin)
            return self:placeOfOrNilCPS(m2, ctx, expr, expr.span, function(m3, reached)
                if reached and not reached.place and reached.concrete ~= nil then
                    -- The place exists as a compile-time value with no storage of its own, which is how
                    -- the interpreter holds a module array's element. Taking an address needs an
                    -- address, and only compiled code gives one, so say that rather than blaming the
                    -- target's lifetime.
                    D.reject("runtime-in-normalization",
                        "A reference needs storage here, and this place has none while interpreting; "
                        .. "compiling the program gives it one", expr.span)
                end
                if reached and reached.place then
                    local container = reached.container
                    local isModule = origin == "module" or (container ~= nil and container.module == true)
                    -- A container whose provenance is not known here is treated as enclosing, which is
                    -- the conservative reading: it cannot be proven to be module storage, so it must not
                    -- escape.
                    local isEnclosing = origin == "enclosing"
                        or (container ~= nil and (container.enclosing == true or container.retaining == true))
                    if isModule or isEnclosing then
                        local made = V.ref(S.ref(self:canonicalize(reached.ty)), reached.place, nil,
                            isEnclosing, reached.value)
                        -- Building the reference is just an address, which is how a recursive structure is
                        -- built; reading or writing through it is what runtime code does.
                        made.module = isModule
                        return k(m3, made)
                    end
                end
                return fallback(m3)
            end)
        end)
    end
    if not slot then return afterHeldType(machine) end
    return self:demandCPS(machine, slot, expr.span, function(m, demanded)
        local heldType = demanded.value and self:asType(demanded.value, expr.span) or nil
        if heldType then return k(m, V.type(S.ref(self:canonicalize(heldType)))) end
        return afterHeldType(m)
    end)
end
-- A reference to an enclosing owner cannot outlive that activation, so it and anything holding it
-- stay inside.
function Eval:refEscapeMessage()
    return "A reference to a place in an enclosing activation cannot escape it; use it where the "
        .. "place is still live, or name module storage instead"
end


-- A reference to named storage. No evaluation happens here, so this is one answer through `k`.
function Eval:makeReferenceCPS(machine, ctx, target, span, k)
    if V.tag(target) == "ref" then
        D.reject("ref-target",
            "A reference is not itself a place to reference: the second reference would need the "
            .. "first one to have storage of its own, which it does not", span)
    end
    local kind = self:referenceTarget(target)
    if not kind then
        D.reject("ref-target",
            "A reference may only name module storage or a place that encloses it; a local or a "
            .. "temporary of this activation does not outlive the reference", span)
    end
    -- A reference also carries the frontend value it names, when there is one: normalize code reads
    -- and writes that directly, and residual code uses the place.
    local held = V.tag(target) == "record" and target or target.backing
    return k(machine, V.ref(S.ref(self:canonicalize(target.ty)), target.place, target.schema,
        kind == "enclosing", held))
end

-- Arrays -----------------------------------------------------------------------------------------
-- An array literal takes its type from its elements, or from the annotation it is checked against,
-- which is what an empty literal needs. A residual array owns fresh local storage, so its elements
-- are writable and a read goes to that storage rather than to the values it was built from.

-- An array literal: every element is evaluated on the machine, in written order, so a long literal
-- is tail calls rather than one host frame per element.
function Eval:evalArrayCPS(machine, ctx, expr, expected, k)
    return self:evalArrayElementsCPS(machine, ctx, expr, expected, {}, 1, k)
end

-- One element per step. The recursive call is a method like any other, and it is named `*CPS`
-- because it follows the protocol: it answers a pair through `k` in tail position.
function Eval:evalArrayElementsCPS(machine, ctx, expr, expected, items, index, k)
    if index > #expr.items then
        return self:finishArrayCPS(machine, ctx, expr, expected, items, k)
    end
    return self:evalExprCPS(machine, ctx, expr.items[index], function(m, value)
        items[index] = value
        return self:evalArrayElementsCPS(m, ctx, expr, expected, items, index + 1, k)
    end)
end

-- The type checks and the residual spill, once every element is known. Split out so the element walk
-- above is one small recursive step per element.

-- An array literal once its elements are evaluated: the annotation supplies the type, or the elements
-- do, and a residual literal becomes a Make that storage can later spill.
function Eval:finishArrayCPS(machine, ctx, expr, expected, items, k)
    -- An array literal consumes an annotation only when the annotation is an array type, and there
    -- is usually none: `evalExpr` reaches this with no expectation at all.
    local ty = expected and expected:isArray() and expected or nil
    if not ty then
        if #items == 0 then
            D.reject("type-required",
                "An empty array literal needs an annotation that gives its element type and length",
                expr.span)
        end
        local element = items[1].ty
        for _, item in ipairs(items) do
            if item.ty ~= element then
                D.reject("type-mismatch", "array elements must share one type: " .. S.encode(element)
                    .. " and " .. S.encode(item.ty), expr.span)
            end
        end
        ty = S.array(element, #items)
    end
    if #items ~= ty.length then
        D.reject("array-length", "An array of length " .. tostring(ty.length) .. " needs "
            .. tostring(ty.length) .. " elements", expr.span)
    end
    for _, item in ipairs(items) do self:requireType(item, ty.element, expr.span) end
    if not ctx.residual then return k(machine, V.array(ty, items)) end
    local exprs, borrowed = {}, false
    local function element(index)
        if index > #items then
            -- The Make is the value until an element is addressed (an index or a view). `body` is where
            -- that spill goes, so a demand from inside an arm still reaches storage from the outer scope.
            return k(machine, V.array(ty, nil, nil, borrowed, ctx.builder:make(ty, exprs), ctx.body))
        end
        local item = items[index]
        return self:expressionCPS(machine, ctx, item, ty.element, function(m, value)
            exprs[index] = value
            if self:isBorrowed(item) then borrowed = true end
            return element(index + 1)
        end)
    end
    return element(1)
end
-- The shim for `evalExpected`, which is still direct: one boundary frame when an array literal is in
-- an annotated position, and it goes when that family converts.

-- The place an array value's elements live at. A value that only exists as an SSA value is spilled
-- into storage once, which is what lets a parameter or a call result be indexed.
-- `slice(array)` is a runtime-length view of an array: the address of its first element and its
-- length. The view borrows the storage it names, so the lifetime rules of a reference apply to it.
-- `slice(T)` is a type and `slice(x)` a view, and neither child is recursive: everything below is
-- the direct walker, so each answer is a value through `k` and nothing nests. Its caller is still
-- `evalApply`, which is why the direct name stays as a shim for one boundary frame.
-- `slice(array)` is a runtime-length view of an array: the address of its first element and its
-- length. The view borrows the storage it names, so the lifetime rules of a reference apply to it.
-- `slice(T)` is a type and `slice(x)` a view, and everything below is the direct walker, so each answer
-- is a value through `k`.
function Eval:evalSliceCPS(machine, ctx, expr, k)
    -- `slice(Node)` inside Node's own definition must not demand Node's layout: a slice is a pointer
    -- and a length, so its size does not depend on its element either. It names the cell the
    -- definition reserved, exactly as a pointer or a reference does.
    if expr.kind == "Reference" then
        local slot = lookup(ctx.scope, expr.name.text)
        if slot and slot.open and slot.value == nil and slot.cell and self:isTypeDefinition(slot) then
            self.types.referenced[slot.cell] = true
            return k(machine, V.type(S.slice(S.named(slot.cell))))
        end
    end
    return self:containerOfCPS(machine, ctx, expr, expr.span, function(m, container)
        -- `slice(T)` is a type, exactly as `ref(T)` is; only a non-type argument names a view.
        local element = self:asType(container.value, expr.span)
        if element then
            S.checkRuntime(element, expr.span)
            return k(m, V.type(S.slice(self:canonicalize(element))))
        end
        local ty = container.ty
        if not ty:isArray() then
            D.reject("type-mismatch", "slice needs an array, found " .. S.encode(ty or S.unit), expr.span)
        end
        -- A reference to module storage may leave the activation; a view of anything else may not.
        local tied = not (container.container and container.container.module)
        if not ctx.residual then
            local held = container.value
            if not (V.tag(held) == "array" and held.items) then
                D.reject("runtime-in-normalization", "A runtime slice must be built in runtime code",
                    expr.span)
            end
            -- A view names storage rather than being storage, so a view of module storage is not a
            -- compile-time constant: folding it would bake the read into the output. Module
            -- initialization and the reference interpreter execute over that storage, so for them it
            -- is the value; elsewhere the call is compiled instead.
            if container.container and container.container.module
                and not (ctx.session.run or ctx.session.demanding) then
                D.reject("runtime-in-normalization",
                    "A view of module storage is built where it is used, not folded while compiling",
                    expr.span)
            end
            return k(m, V.slice(S.slice(ty.element), held, 0, ty.length, tied))
        end
        local function withPlace(m2, place)
            -- Both halves of a view are pure: an address and a length need no storage of their own.
            local data = ctx.builder:addr(Ir.Index(place, ctx.builder:u32(0), ty.element),
                S.ref(ty.element))
            local view = ctx.builder:make(S.slice(ty.element), { data, ctx.builder:u32(ty.length) })
            return k(m2, V.runtime(view, S.slice(ty.element), tied, place))
        end
        if container.place then return withPlace(m, container.place) end
        if not container.value then
            D.reject("not-a-place", "slice needs an array with storage", expr.span)
        end
        return self:arrayPlaceCPS(m, ctx, container.value, expr.span, withPlace)
    end)
end
-- The length of a slice value, when the compiler knows it.
function Eval:sliceCount(value)
    if V.tag(value) == "string" then return #value.bytes end
    if V.tag(value) == "slice" then return value.count end
    return nil
end

-- One element of a slice value at a known index.
function Eval:sliceElement(value, index)
    if V.tag(value) == "string" then return V.u8(value.bytes:byte(index + 1)) end
    if V.tag(value) == "slice" then
        local items = value.source and value.source.items
        if not items then return nil end
        return items[value.start + index + 1]
    end
    return nil
end

-- The place of an array, spilling it when it only exists as an SSA value.
function Eval:arrayPlaceCPS(machine, ctx, value, span, k)
    if value.place then
        -- A demand for a place invalidates the construction expression; storage is authoritative.
        value.expr = nil
        return k(machine, value.place)
    end
    if not ctx.residual then
        D.reject("runtime-in-normalization", "A runtime array needs runtime code", span)
    end
    -- The spill goes into the list the value was built in, so it dominates every use even when the
    -- demand comes from inside an arm.
    return self:expressionCPS(machine, ctx, value, value.ty, function(m, init)
        local storage = ctx.builder:var(value.body or ctx.body, value.ty, init)
        local place = Ir.Local(storage)
        -- A compile-time value is shared and immutable, so it never remembers a spill: another mode or
        -- capture reading the same value must not see a `place` a residual compilation gave it.
        if not value.items then value.place = place end
        value.expr = nil
        return k(m, place)
    end)
end

-- The place a record value's fields live at. A record that only exists as an SSA value is spilled
-- into storage once, which is what lets a call result be written through its fields.

-- The place of a record, spilling it when it only exists as an SSA value.
function Eval:recordPlaceCPS(machine, ctx, value, span, k)
    if value.place then
        -- A demand for a place invalidates the construction expression: storage is authoritative
        -- from here on, so a later store must be visible to every read. A spilled `ir` keeps its SSA
        -- expression as its representation.
        if V.tag(value) == "object" then value.expr = nil end
        return k(machine, value.place)
    end
    if not ctx.residual then
        D.reject("runtime-in-normalization", "A runtime record needs runtime code", span)
    end
    -- A value that only exists as an SSA value is spilled once; the place is initialized from its
    -- expression and storage is authoritative afterwards. The spill goes into the list the value was
    -- built in, so it dominates every use even when the demand comes from inside an arm.
    return self:expressionCPS(machine, ctx, value, value.ty, function(m, init)
        local storage = ctx.builder:var(value.body or ctx.body, value.ty, init)
        local place = Ir.Local(storage)
        -- A compile-time record is shared and immutable, so it never remembers a spill: another mode or
        -- capture reading the same value must not see a `place` a residual compilation gave it.
        if not value.fields then value.place = place end
        if V.tag(value) == "object" then value.expr = nil end
        return k(m, place)
    end)
end

-- An array expression. A value backed by storage is read whole, which is a struct copy in C; a
-- compile-time array is built from its elements.

-- An array's construction expression, element by element.
-- An array's construction expression, element by element.
function Eval:arrayExprCPS(machine, ctx, value, k)
    -- A residual literal that has not demanded a place is already its construction expression.
    if value.expr then return k(machine, value.expr) end
    if not value.items then
        D.bug("array-value", "An array with neither storage nor elements has no representation")
    end
    local exprs = {}
    local function element(index)
        if index > #value.items then
            return k(machine, ctx.builder:make(value.ty, exprs))
        end
        return self:expressionCPS(machine, ctx, value.items[index], value.ty.element,
            function(m, expr)
                exprs[index] = expr
                return element(index + 1)
            end)
    end
    return element(1)
end
-- A name no binding declares. There is no "known but unimplemented" state: a name is either bound
-- or it is not.
function Eval:unknownName(name, span)
    D.reject("unknown-name", "Unknown name: " .. name, span)
end

-- The place an lvalue expression names, without reading it. Every assignable target and every
-- reference target is a chain of selections over a root, so this is the one place that knows how to
-- reach storage. A concrete result describes a compile-time container; a residual one is an
-- `Ir.Place` with the type it refers to.
--   { concrete = "field", record = <value>, name = <field>, ty = <ty> }
--   { concrete = "index", array = <value>, index = <n>, ty = <ty> }
--   { place = <Ir.Place>, ty = <ty> }
-- The shim: `evalRef`, `evalPtr`, `containerOf`, `derefContainer` and the statement path all reach
-- this by name.

-- The place an expression names, or a rejection. The three index cases each evaluate the index before
-- they can name storage, so each is a continuation; the slice and array cases are separate
-- continuations because the container's type decides which route applies.
-- The place walk. Each branch names storage from the base selection inward, so the base is a
-- continuation and the emission order of the original is kept exactly: an index is materialised, the
-- guard is emitted, and only then is storage named -- a spill emitted before the guard would reorder
-- the C.
function Eval:placeOfCPS(machine, ctx, expr, span, k)
    if expr.kind == "Reference" then
        local slot = lookup(ctx.scope, expr.name.text)
        if not slot then self:unknownName(expr.name.text, expr.name.span) end
        if slot.atTop then
            -- The binding is demanded first: its named storage is built from the value it computes.
            return self:demandCPS(machine, slot, expr.name.span, function(m, demanded)
                local held = demanded.value
                if not held or (V.tag(held) ~= "record" and V.tag(held) ~= "array") then
                    D.reject("not-a-place", "Only a record or an array instance is storage: "
                        .. expr.name.text, expr.name.span)
                end
                local object = self:moduleObject(demanded, expr.name.span)
                -- `backing` is the value the storage stands for, which is what normalize code reads;
                -- `container` is the object whose storage holds the selection, which is what the borrow
                -- rules inspect.
                return k(m, { place = object.place, ty = object.ty, concrete = object.backing,
                    value = object.backing, container = object })
            end)
        end
        if slot.kind == "concrete-field" then
            return k(machine, { concrete = "field", record = slot.record, name = slot.name, ty = slot.ty })
        end
        if slot.kind == "concrete-index" then
            return k(machine, { concrete = "index", array = slot.array, index = slot.index, ty = slot.ty })
        end
        if slot.kind == "field" then return k(machine, { place = slot.place, ty = slot.ty }) end
        if slot.kind == "param" then return k(machine, { place = Ir.Local(slot.storage), ty = slot.ty }) end
        D.reject("not-a-place", "Only storage can be a place: " .. expr.name.text, expr.name.span)
    end
    if expr.kind == "FieldSelect" then
        return self:containerOfCPS(machine, ctx, expr.base, expr.base.span, function(m, selected)
            return self:derefContainerCPS(m, ctx, selected, expr.span, function(m2, container)
                local name = expr.field.text
                local target = self:resolveType(S.environmentOf(container.ty))
                local ty = S.field(target, name)
                if not ty then D.reject("unknown-member", "Record has no field " .. name, expr.field.span) end
                local function withBase(m3, basePlace)
                    local place = basePlace and Ir.Project(basePlace, Ir.Field(name)) or nil
                    local held = container.concrete
                    if type(held) == "table" and held.tag == "record" and held.fields then
                        return k(m3, { concrete = "field", record = held, name = name, ty = ty,
                            place = place, value = held.fields[name], container = container.container })
                    end
                    if not place or not ctx.residual then
                        D.reject("runtime-in-normalization",
                            "A field of run-time storage is only reachable from runtime code", expr.span)
                    end
                    return k(m3, { place = place, ty = ty, container = container.container })
                end
                local base = container.place
                if ctx.residual and container.value
                    and (not base or (V.tag(container.value) == "object" and container.value.expr)) then
                    return self:recordPlaceCPS(m2, ctx, container.value, expr.span, function(m3, place)
                        return withBase(m3, place)
                    end)
                end
                return withBase(m2, base)
            end)
        end)
    end
    if expr.kind == "IndexExpr" then
        return self:containerOfCPS(machine, ctx, expr.base, expr.base.span, function(m, base)
            -- An unchecked pointer is indexed by address, before any dereference: `p[i]` is the element
            -- at `p + i`, so the pointer's target is that element rather than a container to index into.
            -- Dereferencing first, the way a reference is handled, would read the element and then try to
            -- index it.
            if base.ty and base.ty:isPtr() then
                local element = self:pointeeType(base.ty)
                return self:evalExprCPS(m, ctx, expr.index, function(m2, index)
                    self:requireType(index, S.u32, expr.index.span)
                    if not ctx.residual then
                        D.reject("runtime-in-normalization", "A pointer element needs runtime code", expr.span)
                    end
                    return self:containerExprCPS(m2, ctx, base, function(m3, view)
                        return self:expressionCPS(m3, ctx, index, S.u32, function(m4, indexExpr)
                            -- No length and so no guard: that is the whole difference from the slice
                            -- index below.
                            return k(m4, { place = ctx.builder:ptrIndex(view, indexExpr, element),
                                ty = element })
                        end)
                    end)
                end)
            end
            return self:derefContainerCPS(m, ctx, base, expr.span, function(m2, container)
                if container.ty:isSlice() then
                    local element = container.ty.element
                    return self:evalExprCPS(m2, ctx, expr.index, function(m3, index)
                        self:requireType(index, S.u32, expr.index.span)
                        local count = self:sliceCount(container.value)
                        if V.isKnown(index) and V.isInteger(index) and count then
                            if index.n >= count then
                                D.reject("index-range", "Index " .. tostring(index.n) .. " is outside a slice "
                                    .. "of length " .. tostring(count), expr.span)
                            end
                            local held = self:sliceElement(container.value, index.n)
                            if held and not ctx.residual then
                                return k(m3, { concrete = "element", value = held, ty = element,
                                    readonly = true })
                            end
                        end
                        if not ctx.residual then
                            D.reject("runtime-in-normalization",
                                "A run-time slice index needs runtime code", expr.span)
                        end
                        return self:containerExprCPS(m3, ctx, container, function(m4, view)
                            return self:expressionCPS(m4, ctx, index, S.u32, function(m5, indexExpr)
                                -- A run-time index is checked before it is used, exactly as an array's is.
                                ctx.builder:emit(ctx.body, Ir.Trap(ctx.builder:bin("Ge", indexExpr,
                                    ctx.builder:sliceLength(view, S.u32), S.bool), "index-range"))
                                return k(m5, { place = ctx.builder:sliceIndex(view, indexExpr, element),
                                    ty = element, readonly = true })
                            end)
                        end)
                    end)
                end
                if not container.ty:isArray() then
                    D.reject("type-mismatch",
                        "Expected an array but found " .. S.encode(container.ty or S.unit), expr.span)
                end
                local length, element = container.ty.length, container.ty.element
                return self:evalExprCPS(m2, ctx, expr.index, function(m3, index)
                    -- A narrower integer index widens, which is free.
                    self:requireType(index, S.u32, expr.index.span)
                    if V.isKnown(index) and V.isInteger(index) then
                        if index.n >= length then
                            D.reject("index-range", "Index " .. tostring(index.n) .. " is outside an array of "
                                .. "length " .. tostring(length), expr.span)
                        end
                        -- A place needs a builder, so only residual code builds one; normalize code
                        -- either uses the value it names or reports that this storage is runtime-only.
                        local function withBase(m4, basePlace)
                            local place = (basePlace and ctx.residual)
                                and Ir.Index(basePlace, ctx.builder:u32(index.n), element) or nil
                            local held = container.concrete
                            if type(held) == "table" and held.tag == "array" and held.items then
                                return k(m4, { concrete = "index", array = held, index = index.n,
                                    ty = element, place = place, value = held.items[index.n + 1],
                                    container = container.container })
                            end
                            if not place or not ctx.residual then
                                D.reject("runtime-in-normalization",
                                    "An element of run-time storage is only reachable from runtime code",
                                    expr.span)
                            end
                            return k(m4, { place = place, ty = element, container = container.container })
                        end
                        local base = container.place
                        if ctx.residual and container.value
                            and (not base or (V.tag(container.value) == "array" and container.value.expr)) then
                            return self:arrayPlaceCPS(m3, ctx, container.value, expr.span,
                                function(m4, place)
                                    return withBase(m4, place)
                                end)
                        end
                        return withBase(m3, base)
                    end
                    if not ctx.residual then
                        D.reject("runtime-in-normalization", "A run-time index needs runtime code", expr.span)
                    end
                    -- A run-time index is checked before it is used, exactly as a run-time divisor is.
                    return self:expressionCPS(m3, ctx, index, S.u32, function(m4, indexExpr)
                        ctx.builder:emit(ctx.body, Ir.Trap(ctx.builder:bin("Ge", indexExpr,
                            ctx.builder:u32(length), S.bool), "index-range"))
                        local function answer(m5, place)
                            -- The container travels too: `ref(r[i])` has to be able to see that the element
                            -- it names is in module storage, even when the route to it is a run-time index.
                            return k(m5, { place = Ir.Index(place, indexExpr, element), ty = element,
                                container = container.container })
                        end
                        if container.place then return answer(m4, container.place) end
                        return self:arrayPlaceCPS(m4, ctx, container.value, expr.span, answer)
                    end)
                end)
            end)
        end)
    end
    D.reject("not-a-place", "This expression does not name storage", span or expr.span)
end

-- The place walk as a *probe*: `pcall(function() return self:placeOf(...) end)` asked whether an
-- expression names storage without treating a refusal as an error. A pushed handler that answers `nil`
-- is the same question, so the three probes in `evalPtrCPS`, `evalRefCPS` and `containerOfCPS` share
-- this.
function Eval:placeOfOrNilCPS(machine, ctx, expr, span, k)
    machine:push("place-probe", span, nil, function(m, diagnostic)
        if not D.is(diagnostic) then error(diagnostic, 0) end
        return k(m, nil)
    end)
    return self:placeOfCPS(machine, ctx, expr, span, function(m, reached)
        machine:pop()
        return k(m, reached)
    end)
end

-- A selection whose container is a reference selects through it: the reference names the instance,
-- so the container becomes that instance. A runtime reference is a pointer, so its place is one
-- dereference further on, and it is conservatively retaining because the storage it points at is not
-- known here.

-- A selection off a reference or a pointer: the container's place holds the pointer, so the target is
-- one dereference further on. A frontend reference already names the target place, which is why that
-- case is settled before the pointer cases are tried.
-- A selection off a reference or a pointer: the container's place holds the pointer, so the target is
-- one dereference further on. A frontend reference already names the target place, which is why that
-- case is settled before the pointer cases are tried.
function Eval:derefContainerCPS(machine, ctx, container, span, k)
    local held = container.value
    if type(held) == "table" and V.tag(held) == "ref" then
        local object = self:placeObject(held)
        if not object then return k(machine, container) end
        return k(machine, { concrete = object.backing, value = object.backing, place = object.place,
            ty = object.ty, container = object })
    end
    if held and held.ty and held.ty:isRef() and V.tag(held) == "runtime" then
        local target = self:pointeeType(held.ty)
        if not ctx.residual then
            return k(machine, { place = nil, ty = target, container = { retaining = true } })
        end
        return self:derefPlaceCPS(machine, ctx, held, span, function(m, place)
            return k(m, { place = place, ty = target, container = { retaining = true } })
        end)
    end
    -- A selection directly off a reference field or a runtime reference: the place holds the
    -- pointer, so the target is one dereference further on. This is checked after the value cases,
    -- because a frontend reference already names the target place.
    if container.ty and container.ty:isPtr() then
        -- The pointer is a value, so it is spilled once to reach the record it addresses; from there the
        -- selection is the same route a reference takes.
        local target = self:pointeeType(container.ty)
        if not ctx.residual then
            D.reject("runtime-in-normalization", "A pointer field needs runtime code", span)
        end
        if container.place then
            return k(machine, { place = Ir.Deref(container.place, target), ty = target,
                container = { retaining = true } })
        end
        return self:containerExprCPS(machine, ctx, container, function(m, expr)
            local storage = ctx.builder:var(ctx.body, container.ty, expr)
            return k(m, { place = Ir.Deref(Ir.Local(storage), target), ty = target,
                container = { retaining = true } })
        end)
    end
    if container.ty and container.ty:isRef() then
        local target = self:pointeeType(container.ty)
        if not container.place then return k(machine, container) end
        return k(machine, { place = Ir.Deref(container.place, target), ty = target,
            container = { retaining = true } })
    end
    return k(machine, container)
end
-- The container an element or field selection starts from: a compile-time value, or a place with the
-- type it refers to. A selection over a selection does not read the intermediate value.
-- The value a resolved container stands for, as an IR expression: the value it carries when there is
-- one, and otherwise a read of the place it was resolved to. A container that came from `placeOf` has
-- no value attached, so a consumer that needs the expression must be able to read one; assuming a value
-- is there is what turned `slice(ptr(u8))` into an internal Lua error rather than a diagnostic.

-- Either the value the container holds or a read of its place.
-- Either the value the container holds or a read of its place.
function Eval:containerExprCPS(machine, ctx, container, k)
    if container.value then
        return self:expressionCPS(machine, ctx, container.value, container.ty, k)
    end
    if container.place then
        local read = ctx.builder:read(ctx.body, container.ty, container.place)
        return k(machine, ctx.builder:ref(read, container.ty))
    end
    D.bug("container-value", "A container has neither a value nor a place")
end

-- What a selection names: its place, the value it holds, or both. The place walk is asked first, and
-- only when it declines is the expression evaluated -- which is why that evaluation is the one
-- continuation here.
-- What a selection names: its place, the value it holds, or both. The place walk is asked first, and
-- only when it declines is the expression evaluated -- which is the shared fallback here.
function Eval:containerOfCPS(machine, ctx, expr, span, k)
    local function fallback(m)
        return self:evalExprCPS(m, ctx, expr, function(m2, value)
            if value.place then
                return k(m2, { value = value, place = value.place, ty = value.ty })
            end
            return k(m2, { concrete = value, value = value, ty = value.ty })
        end)
    end
    if expr.kind ~= "Reference" and expr.kind ~= "FieldSelect" and expr.kind ~= "IndexExpr" then
        return fallback(machine)
    end
    return self:placeOfOrNilCPS(machine, ctx, expr, span, function(m, reached)
        if not reached then return fallback(m) end
        -- The value the selection names travels too, so a reference in it can be dereferenced.
        if reached.concrete == "field" then
            local held = reached.record.fields[reached.name]
            return k(m, { concrete = held, value = held, ty = reached.ty, place = reached.place,
                container = reached.container })
        end
        if reached.concrete == "index" then
            local held = reached.array.items[reached.index + 1]
            return k(m, { concrete = held, value = held, ty = reached.ty, place = reached.place,
                container = reached.container })
        end
        -- A container that has both keeps both: a read uses the value and a reference uses the
        -- place, so a chain of selections does not have to choose here.
        return k(m, { place = reached.place, ty = reached.ty, concrete = reached.concrete,
            value = reached.value, container = reached.container or reached.value })
    end)
end
-- `a[i]`: an element read, through the place it names.
-- An index reaches storage through `placeOf`, which is the direct walker for now, so every answer
-- here is a value through `k` rather than a nested chain.
-- An element read. Residual code reads the storage it names; normalize code reads the value directly.
-- Residual specialization must not bake a snapshot of module storage, but the reference interpreter
-- (`session.run`) and a top-level initializer demand (`session.demanding`) both execute over concrete
-- state, so they read it directly.
function Eval:evalIndexCPS(machine, ctx, expr, k)
    return self:placeOfCPS(machine, ctx, expr, expr.span, function(m, reached)
        local function answer(m2, origin)
            if not ctx.residual and (ctx.session.run or ctx.session.demanding or origin ~= "module") then
                if reached.concrete == "element" then return k(m2, reached.value) end
                if reached.concrete == "index" then
                    return k(m2, reached.array.items[reached.index + 1])
                end
                if reached.concrete == "field" then
                    return k(m2, reached.record.fields[reached.name] or V.unit())
                end
            end
            if not ctx.residual then
                D.reject("runtime-in-normalization", "Element is runtime storage", expr.span)
            end
            local read = ctx.builder:read(ctx.body, reached.ty, reached.place)
            return k(m2, V.runtime(ctx.builder:ref(read, reached.ty), reached.ty, nil, reached.place))
        end
        -- The route is only asked when nothing else has decided: `or` short-circuiting in the original
        -- is why an interpreter run never asks.
        if ctx.residual or ctx.session.run or ctx.session.demanding then
            return answer(m, nil)
        end
        return self:placeOriginCPS(m, ctx, expr, function(m2, origin)
            return answer(m2, origin)
        end)
    end)
end
-- Callable arms of a tagged callable -----------------------------------------------------------
-- A conditional whose arms are two different callable code identities joins into one tagged
-- callable: the tag names the code to run and the payload is that code's environment. Each arm is
-- registered under the identity that names it in the type, so a call site can dispatch from the
-- type alone.

function Eval:isCallableValue(value)
    local tag = V.tag(value)
    return tag == "word" or tag == "closure"
end

-- The identity, environment type and visible signature of one callable arm. A word needs a fully
-- declared signature, because its call site has no annotation to fall back on.

-- The arm descriptor of one callable, plus the key that identifies it and the signature the two arms
-- share. Three values travel back, which is why the machine's value channel is a vector.
function Eval:callableArmCPS(machine, value, span, k)
    if V.tag(value) == "word" then
        local def, bound = value.def, value.args or {}
        local sc = scope(def.lexical)
        local inputs = {}
        local function parameter(index)
            if index > #def.params then
                return self:declaredResultCPS(machine, def, sc, span, function(m, results)
                    if not results then
                        D.reject("callable-branch", "Word " .. tostring(def.name)
                            .. " needs declared result types to be selected at run time", span)
                    end
                    for _, item in ipairs(results) do S.checkRuntime(item, span) end
                    local key = V.encode(value)
                    if not key then
                        D.reject("callable-branch", "A word selected at run time needs static arguments",
                            span)
                    end
                    self.arms[key] = { kind = "word", def = def, bound = bound }
                    return k(m, key, S.unit, S.sig(inputs, results))
                end)
            end
            return self:requirementCPS(machine, def, index, sc, span, function(m, ty)
                S.checkRuntime(ty, span)
                inputs[index] = S.inValue(ty)
                return parameter(index + 1)
            end)
        end
        return parameter(1)
    end
    local plan = value.plan
    if #(plan.borrowedOrder or {}) > 0 then
        D.reject("callable-branch",
            "A closure that borrows storage cannot be selected at run time, because a tagged callable "
            .. "holds its environments by value; return the receiver and select its method instead", span)
    end
    local parts = { plan.ty.entry }
    for _, arg in ipairs(value.bound or {}) do
        local encoded = V.encode(arg)
        if not encoded then
            D.reject("callable-branch",
                "A partially applied closure selected at run time needs static arguments", span)
        end
        parts[#parts + 1] = encoded
    end
    local key = table.concat(parts, "|")
    self.arms[key] = { kind = "closure", plan = plan, bound = value.bound or {} }
    return k(machine, key, plan.envTy, plan.sig)
end
-- The tagged representation of one arm: the tag names the code, the payload is its environment.
function Eval:taggedArmValue(ty, key, value, span)
    local envTy = S.caseOf(ty, key)
    if envTy == S.unit then return V.variant(ty, key, V.unit()) end
    local plan = value.plan
    if #plan.runtimeOrder ~= #(plan.envNames or {}) then
        D.bug("tagged-arm", "A tagged environment must match the plan's runtime captures")
    end
    local fields = {}
    for index, envName in ipairs(plan.envNames) do
        fields[envName] = plan.runtime[plan.runtimeOrder[index]]
    end
    return V.variant(ty, key, V.record(envTy, fields))
end

-- Joins two callable arms, rejecting a shape mismatch rather than inventing a representation.

-- Two callable arms joined into one tagged callable. Both arms must be callable the same way, which is
-- what the shared signature checks.
function Eval:joinCallablesCPS(machine, yesValue, noValue, span, k)
    return self:callableArmCPS(machine, yesValue, span, function(m, keyA, envA, sigA)
        return self:callableArmCPS(m, noValue, span, function(m2, keyB, envB, sigB)
            -- Two signatures are one interned `Ty.Sig` value when they are the same shape.
            if sigA ~= sigB then
                D.reject("callable-branch", "Both arms must be callable the same way: "
                    .. S.encode(sigA) .. " and " .. S.encode(sigB), span)
            end
            local ty = S.tagged(sigA, { [keyA] = envA, [keyB] = envB })
            return k(m2, ty, self:taggedArmValue(ty, keyA, yesValue, span),
                self:taggedArmValue(ty, keyB, noValue, span))
        end)
    end)
end
-- Calls one arm. A residual tagged value projects that arm's environment out of the payload; the
-- arm's own code then runs as an ordinary direct call, exactly as a non-tagged callable would.

-- One arm of a tagged callable. A word arm calls an instance; a closure arm rebuilds the environment
-- out of the variant payload and calls the closure, which is why the arm descriptor is keyed.
function Eval:callTaggedArmCPS(machine, ctx, name, variantId, taggedTy, args, span, k)
    local descriptor = self.arms[name]
    if not descriptor then D.bug("tagged-arm", "Tagged callable has no arm " .. name) end
    local envTy = S.caseOf(taggedTy, name)
    if descriptor.kind == "word" then
        if envTy ~= S.unit then D.bug("tagged-arm", "A word arm carries no environment") end
        local values = {}
        for _, item in ipairs(descriptor.bound) do values[#values + 1] = item end
        for _, item in ipairs(args) do values[#values + 1] = item end
        return self:callInstanceCPS(machine, ctx, descriptor.def, values, span, nil, k)
    end
    local plan = descriptor.plan
    local merged = {}
    for _, item in ipairs(descriptor.bound) do merged[#merged + 1] = item end
    for _, item in ipairs(args) do merged[#merged + 1] = item end
    local envExprs = {}
    if envTy ~= S.unit then
        local id = ctx.builder:valueId()
        ctx.builder:emit(ctx.body, Ir.VariantPayload(id, variantId, taggedTy, name))
        local payload = ctx.builder:ref(id, envTy)
        local envTys = {}
        for _, field in ipairs(S.environmentOf(envTy).fields) do envTys[field.name] = field.type end
        for _, envName in ipairs(plan.envNames) do
            envExprs[#envExprs + 1] = ctx.builder:get(payload, envName, envTys[envName])
        end
    end
    return self:invokeClosureCPS(machine, ctx, plan, envExprs, merged, span, nil, k)
end

-- Materialises a value for a runtime position. `want` is the destination type when the context
-- knows it, which is what lets an unrepresentable callable be rejected with a source diagnostic
-- instead of building mistyped IR.
-- The shim: `recordExpr`, `arrayExpr`, `constructRecord`, the place walk and the call spine all
-- reach this by name, so it is the single most-called scaffold site during the stretch.

-- A value as a runtime expression. Most of the work is one builder call, so nearly every answer is
-- direct; the nested `expression` calls (a variant payload, a closure environment) go through the shim
-- because the value's own nesting, not the program's recursion, bounds them.
function Eval:expressionCPS(machine, ctx, value, want, k)
    local tag = V.tag(value)
    if want and (want:isSig() or want:isView()) and value.ty and value.ty:isTagged() then
        self:rejectTaggedErase(ctx.span)
    end
    if (tag == "closure" or tag == "word" or tag == "method") and want
        and (want:isSig() or want:isView()) then
        if not ctx.residual then
            D.reject("runtime-in-normalization", "A view needs runtime code", ctx.span)
        end
        return self:makeViewCPS(machine, ctx, value, want:isView() and want.visible or want, k)
    end
    if tag == "runtime" then
        if value.cast then
            value.cast = nil
            value.expr = ctx.builder:convert(value.expr, value.ty)
        end
        return k(machine, value.expr)
    end
    if tag == "string" then return k(machine, ctx.builder:const(value.ty, Ir.Str(value.bytes))) end
    if tag == "float" then return k(machine, ctx.builder:float(value.ty, value.n)) end
    if tag == "slice" then
        if value.expr then return k(machine, value.expr) end
        D.reject("runtime-in-normalization", "A compile-time slice has no runtime representation", ctx.span)
    end
    if tag == "int" then
        if value.high then return k(machine, ctx.builder:int64(value.ty, value.high, value.low)) end
        return k(machine, ctx.builder:int(value.ty, value.n))
    end
    if tag == "bool" then return k(machine, ctx.builder:bool(value.b)) end
    if tag == "record" or tag == "object" then return self:recordExprCPS(machine, ctx, value, k) end
    if tag == "array" then
        if value.expr then return k(machine, value.expr) end
        if value.place then
            -- Storage is authoritative, so reading the array whole copies its current elements.
            local read = ctx.builder:read(ctx.body, value.ty, value.place)
            return k(machine, ctx.builder:ref(read, value.ty))
        end
        if not ctx.residual then
            D.reject("runtime-in-normalization", "An array needs runtime code", ctx.span)
        end
        return self:arrayExprCPS(machine, ctx, value, k)
    end
    if tag == "ref" then
        if value.place == nil then
            D.reject("ref-target", "A reference to a compile-time value has no address; it can only "
                .. "be used where the value itself is", ctx.span)
        end
        if not ctx.residual then
            D.reject("runtime-in-normalization", "A reference needs runtime code", ctx.span)
        end
        return k(machine, ctx.builder:addr(value.place, value.ty))
    end
    if tag == "variant" then
        -- A variant already emitted under runtime code refers to its own instruction.
        if value.expr then return k(machine, value.expr) end
        if not ctx.residual then
            D.reject("runtime-in-normalization", "A sum value needs runtime code", ctx.span)
        end
        local caseType = S.caseOf(value.ty, value.case)
        local id = ctx.builder:valueId()
        local function emit(payload)
            ctx.builder:emit(ctx.body, Ir.ConstructVariant(id, value.ty, value.case, payload))
            return k(machine, ctx.builder:ref(id, value.ty))
        end
        if caseType == S.unit then return emit(nil) end
        return self:expressionCPS(machine, ctx, value.payload, caseType, function(m, payload)
            return emit(payload)
        end)
    end
    if tag == "closure" then
        local plan = value.plan
        if #plan.borrowedOrder > 0 then
            D.reject("borrow-escape",
                "A closure capturing mutable storage or a method cannot escape its activation; call it "
                .. "where it was created, or pass the receiver instead", ctx.span)
        end
        if #plan.runtimeOrder == 0 then
            -- Pure code: nothing to retain, so the representation is an invocation pointer with no
            -- environment. Its type stays the callable type, so a call in this compilation is still
            -- direct; only a value that crosses a boundary goes through the pointer.
            return self:callableInstanceCPS(machine, { plan = plan }, value.bound or {}, ctx.span,
                function(m, instance)
                    local id = ctx.builder:valueId()
                    ctx.builder:emit(ctx.body, Ir.View(id, plan.ty, instance.target, S.list({})))
                    return k(m, ctx.builder:ref(id, plan.ty))
                end)
        end
        -- The value's type is the callable type; its representation is the environment record.
        local fields = {}
        local function field(index)
            if index > #plan.runtimeOrder then
                return k(machine, ctx.builder:make(plan.ty, fields))
            end
            return self:expressionCPS(machine, ctx, plan.runtime[plan.runtimeOrder[index]], nil,
                function(m, expr)
                    fields[index] = expr
                    return field(index + 1)
                end)
        end
        return field(1)
    end
    D.reject("residual-value", "A " .. S.encode(value.ty or S.unit) .. " value cannot cross into runtime storage",
        ctx.span)
end

-- A callable argument satisfies a signature requirement when its shape matches. Results are
-- compared only when the callable's own result types are already known.
function Eval:sigMatches(a, b)
    if #a.inputs ~= #b.inputs or #a.results ~= #b.results then return false end
    for index = 1, #a.inputs do
        if a.inputs[index] ~= b.inputs[index] then return false end
    end
    for index = 1, #a.results do
        if a.results[index] ~= b.results[index] then return false end
    end
    return true
end

function Eval:callableMatches(value, sig)
    local tag = V.tag(value)
    if tag == "closure" then
        local own = value.plan.sig
        if #own.results == 0 then
            return #own.inputs == #sig.inputs
        end
        return self:sigMatches(own, sig)
    end
    return nil   -- named words are checked by their own calling requirement
end

-- A value type that satisfies a signature requirement: a callable whose visible shape matches.
function Eval:typeMatchesSignature(ty, sig)
    if ty:isOwned() then return self:sigMatches(ty.visible, sig) end
    return false
end

-- A declared signature result must be satisfied by a callable of matching shape. A tagged callable
-- has that shape and still cannot be returned as a signature, because a view cannot retain the
-- environment that carries its tag, so that case reports the erasure rather than a shape mismatch.
function Eval:requireResultSignature(actual, sig, span)
    if actual and actual.ty and actual.ty:isTagged() and self:sigMatches(actual.ty.visible, sig) then
        self:rejectTaggedErase(span)
    end
    if not actual or not self:typeMatchesSignature(actual.ty, sig) then
        D.reject("callable-shape", "The returned callable does not match the declared result signature", span)
    end
end

-- Checks a value against a requirement. A signature requirement is satisfied by a callable whose
-- shape matches, which is what lets an unannotated lambda be checked against it.
function Eval:requireAgainst(value, ty, span)
    local wanted = (ty:isSig() and ty) or (ty:isView() and ty.visible) or nil
    if wanted and value.ty and value.ty:isTagged() then
        self:rejectTaggedErase(span)
    end
    if wanted and (V.tag(value) == "closure" or V.tag(value) == "word" or V.tag(value) == "method") then
        if self:callableMatches(value, wanted) == false then
            D.reject("callable-shape", "Callable does not match the required signature", span)
        end
        return
    end
    if ty:isView() and V.tag(value) == "runtime" and value.ty == ty then return end
    self:requireType(value, ty, span)
end

-- A value is borrowed when it refers to storage owned by the current activation: a mutable
-- instance, a view bound to a local adapter, or an aggregate containing one.
function Eval:isBorrowed(value)
    local tag = V.tag(value)
    if tag == "ref" then return value.tied == true end
    -- A slice is a view of storage, so it is as tied to its activation as the place it views.
    if tag == "slice" then return value.tied == true end
    if tag == "array" then return value.borrowed == true end
    if tag == "object" or tag == "record" or tag == "runtime" then return value.borrowed == true end
    if tag == "closure" then return #(value.plan.borrowedOrder or {}) > 0 end
    return false
end

-- Converts a value to another integer width. Widening is implicit because a wider integer holds
-- every value of a narrower one. Narrowing is only implicit for a known value that fits, which is
-- what lets a literal satisfy a narrower annotation; anything else needs an explicit conversion.
-- A conversion between integer types. Changing signedness at one width reinterprets the bits, which
-- is defined and needs no check; any other change that cannot lose a value is implicit, and one that
-- can is accepted only for a known value that fits.
function Eval:convert(value, ty, span)
    if ty:isF64() then
        -- An integer becomes a double implicitly only when the double is exact: rounding can lose a
        -- value, so the rounding is written `f64(x)` where it happens.
        if not value.ty:isInteger() then return nil end
        local from = value.ty
        if V.isKnown(value) then
            local high, low = wordsOf(value)
            local rounded
            -- Only a signed wide value is negative: the same bits are a large positive u64.
            if from:isWide() and from:isSigned() and U64Kernel.slt(high, low, 0, 0) then
                rounded = -U64Kernel.tofloat(U64Kernel.neg(high, low))
            elseif from:isWide() then
                rounded = U64Kernel.tofloat(high, low)
            else
                rounded = value.n
            end
            local backHigh, backLow = wordsOfDouble(rounded)
            if backHigh == high and backLow == low then return V.f64(rounded) end
            D.reject("numeric-range", "Value " .. describeWords(from, high, low)
                .. " is not exactly an f64; write f64(x) to round it", span)
        end
        if from:isWide() then return nil end
        -- Every value of a 32-bit or narrower type is exactly a double.
        if V.tag(value) == "runtime" then
            value.cast = true
            value.ty = S.f64
            return value
        end
        return V.f64(value.n)
    end
    local from = value.ty
    if from == ty then return value end
    if not (from:isInteger() and ty:isInteger()) then return nil end
    if S.widthOf(from) == S.widthOf(ty) then
        -- The same width with a different signedness: the bits are the value.
        if from:isSigned() == ty:isSigned() then return nil end
        if V.tag(value) == "runtime" then value.cast = true end
        if V.isKnown(value) then return become(value, ty, wordsOf(value)) end
        return become(value, ty, 0, 0)
    end
    if fitsAlways(from, ty) then
        -- Nothing can be lost, so the conversion is applied where the value is materialised.
        if V.tag(value) == "runtime" then value.cast = true end
        if V.isKnown(value) then return become(value, ty, wordsOf(value)) end
        return become(value, ty, 0, 0)
    end
    if V.isKnown(value) then
        local high, low = wordsOf(value)
        if wordsFit(ty, high, low) then return become(value, ty, high, low) end
        D.reject("numeric-range", "Value " .. describeWords(from, high, low) .. " does not fit in "
            .. S.encode(ty), span)
    end
    return nil
end

function Eval:requireType(value, ty, span)
    if value.ty == ty then return end
    if self:convert(value, ty, span) then return end
    if value.ty:isInteger() and ty:isInteger() then
        D.reject("numeric-range", "Expected " .. S.encode(ty) .. " but found " .. S.encode(value.ty)
            .. "; narrow a run-time value with an explicit conversion such as "
            .. S.encode(ty):lower() .. "(x)", span)
    end
    D.reject("type-mismatch", "Expected " .. S.display(ty) .. " but found " .. S.display(value.ty), span)
end

-- Expressions ---------------------------------------------------------------------------------

-- The converted router: every arm either answers through `k` or tail-calls a converted family, so the
-- dispatch itself costs no host frame. An unconverted family answers with a value, which is one host
-- frame per family *call* rather than per step, and that line becomes a tail call as it converts.
function Eval:evalExprCPS(machine, ctx, expr, k)
    self:step(expr.span)
    -- Tail position belongs to this node alone, so it is taken here and handed back only to a construct
    -- whose child really is the returned expression: a call that is the whole expression, and the arms
    -- of a conditional. An operand of `+`, an index or an argument is never a tail position, so a
    -- self-call there stays a real call instead of becoming a back edge whose result is unit.
    local tail = ctx.tail
    ctx.tail = false
    local kind = expr.kind
    if kind == "U32Literal" then
        -- A literal adapts to another operand's type when it fits, which is decided from the syntax.
        local literal = V.u32(expr.value)
        literal.literal = true
        return k(machine, literal)
    elseif kind == "U64Literal" then
        -- A literal that does not fit a word is a 64-bit literal, held as its two words.
        local literal = V.int64(S.u64, expr.high, expr.low)
        literal.literal = true
        return k(machine, literal)
    elseif kind == "BoolLiteral" then return k(machine, V.bool(expr.value))
    elseif kind == "UnitLiteral" then return k(machine, V.unit())
    elseif kind == "Reference" then return self:evalReferenceCPS(machine, ctx, expr, k)
    elseif kind == "UnaryExpr" then return self:evalUnary(machine, ctx, expr, k)
    elseif kind == "BinaryExpr" then return self:evalBinaryCPS(machine, ctx, expr, k)
    elseif kind == "Condition" then
        ctx.tail = tail
        return self:evalConditionCPS(machine, ctx, expr, nil, k)
    elseif kind == "Apply" then
        ctx.tail = tail
        return self:evalApplyCPS(machine, ctx, expr, k)
    elseif kind == "SchemaExpr" then return self:evalSchemaCPS(machine, ctx, expr, k)
    elseif kind == "StringLiteral" then return k(machine, V.string(S.string, expr.bytes))
    elseif kind == "FloatLiteral" then return k(machine, V.f64(expr.value))
    elseif kind == "ArrayExpr" then return self:evalArrayCPS(machine, ctx, expr, nil, k)
    elseif kind == "IndexExpr" then return self:evalIndexCPS(machine, ctx, expr, k)
    elseif kind == "RecordSupply" then
        ctx.tail = tail
        return self:evalSupplyCPS(machine, ctx, expr, k)
    elseif kind == "FieldSelect" then return self:evalFieldSelectCPS(machine, ctx, expr, k)
    elseif kind == "Lambda" then return self:evalLambdaCPS(machine, ctx, expr, nil, k)
    elseif kind == "SignatureExpr" then return self:evalSignatureCPS(machine, ctx, expr, k)
    end
    D.todo("expression", "Unsupported expression form: " .. tostring(kind), expr.span)
end

-- A signature is a static value: a calling requirement, never runtime data.
-- A signature is a static value built from its annotations; `typeOf` is still the direct walker, so
-- each of these calls is one frame for the whole signature, not one per input.
-- A signature expression. An input carries the value/place distinction, so each becomes an InValue;
-- the result list is a single type or a list of them, and both are resolved on the type path.
function Eval:evalSignatureCPS(machine, ctx, expr, k)
    -- A signature's inputs carry the value/place distinction, so each becomes an InValue here.
    local inputs = {}
    local function input(index)
        if index > #expr.inputs then
            local results = {}
            if expr.results.kind == "Single" then
                return self:typeOfCPS(machine, expr.results.type, ctx.scope, expr.span, function(m, ty)
                    return k(m, V.type(S.sig(inputs, { ty })))
                end)
            end
            local function result(position)
                if position > #expr.results.types then
                    return k(machine, V.type(S.sig(inputs, results)))
                end
                return self:typeOfCPS(machine, expr.results.types[position], ctx.scope, expr.span,
                    function(m, ty)
                        results[position] = ty
                        return result(position + 1)
                    end)
            end
            return result(1)
        end
        return self:typeOfCPS(machine, expr.inputs[index], ctx.scope, expr.span, function(m, ty)
            inputs[index] = S.inValue(ty)
            return input(index + 1)
        end)
    end
    return input(1)
end
-- A name used as a value. A top-level binding is demanded on the way; in residual code an aggregate
-- file-scope binding is reached through its named storage instead.
function Eval:evalReferenceCPS(machine, ctx, expr, k)
    local name = expr.name.text
    local slot = lookup(ctx.scope, name)
    if not slot then self:unknownName(name, expr.name.span) end
    if slot.kind == "value" then
        return self:demandCPS(machine, slot, expr.name.span, function(m, demanded)
            if slot.atTop and (ctx.residual or not (ctx.session.run or ctx.session.demanding))
                and (V.tag(demanded.value) == "record"
                    or (V.tag(demanded.value) == "array" and demanded.value.place == nil)) then
                -- Both residual code and normalization must see this as module storage, not its
                -- initial contents. Only initialization and the reference interpreter execute over
                -- the concrete state. readFieldValue/indexing enforce the storage permission.
                return k(m, self:moduleObject(demanded, expr.name.span))
            end
            return k(m, demanded.value)
        end)
    end
    if slot.kind == "word" then
        return k(machine, V.word(slot.def, {}, expr.name.span))
    end
    if slot.kind == "field" then
        return k(machine, self:readFieldValue(ctx, slot, expr.name.span))
    end
    if slot.kind == "concrete-field" then
        return k(machine, slot.record.fields[slot.name] or V.unit())
    end
    if slot.kind == "param" then
        if not ctx.residual then
            D.reject("runtime-in-normalization", "Parameter " .. slot.name .. " is runtime storage",
                expr.name.span)
        end
        local read = ctx.builder:read(ctx.body, slot.ty, Ir.Local(slot.storage))
        return k(machine, V.runtime(ctx.builder:ref(read, slot.ty), slot.ty))
    end
    D.bug("binding", "Unknown binding kind " .. tostring(slot.kind))
end
-- Reads an implicit receiver field (or a bound local field place).
function Eval:readFieldValue(ctx, slot, span)
    if slot.static then return slot.static end
    if not ctx.residual then
        -- Normalize code reads the frontend value a borrowed or module place stands for directly.
        local record = slot.record and slot.record.backing
        -- A module object is read the same way, but only where reading it is the point: module
        -- initialization and the reference interpreter both execute over concrete state, while
        -- residual specialization must not bake a snapshot of module storage into the output.
        if record and record.fields
            and (not slot.record.module or ctx.session.run or ctx.session.demanding) then
            local held = record.fields[slot.name]
            if held == nil then D.bug("module-field", "Module storage has no field " .. slot.name) end
            return held
        end
        D.reject("runtime-in-normalization", "Field " .. slot.name .. " is runtime storage", span)
    end
    -- A field of a record that still holds its construction expression is a pure projection; a
    -- record that demanded a place reads storage so a store is observed.
    if slot.record and slot.record.expr then
        return V.runtime(ctx.builder:get(slot.record.expr, slot.name, slot.ty), slot.ty)
    end
    local read = ctx.builder:read(ctx.body, slot.ty, slot.place)
    -- The place travels with the value: a reference read from storage needs it to reach its target.
    return V.runtime(ctx.builder:ref(read, slot.ty), slot.ty, nil, slot.place)
end

-- Arithmetic and comparison on IEEE-754 doubles. Both sides must be f64 once a literal has adopted the
-- other side's type, exactly as an integer operation needs one width: an integer that is not a literal
-- needs an explicit conversion, because rounding it may lose a value. IEEE decides the rest, so a
-- division by zero is an infinity or a NaN rather than a trap and a NaN comparison is false.

-- An f64 operation: known operands fold here, runtime ones become one IR operation over two
-- materialised operands.
function Eval:floatOpCPS(machine, ctx, op, left, right, leftSpan, rightSpan, span, k)
    for _, side in ipairs({ { left, leftSpan }, { right, rightSpan } }) do
        local value, where = side[1], side[2]
        if value.ty ~= S.f64 then
            if value.ty:isInteger() and value.literal then
                -- A literal adopts f64, which is what lets `2.0 * 3` read as it looks.
                self:requireType(value, S.f64, where)
            else
                D.reject("type-mismatch", "A float operation needs two f64 values, found "
                    .. S.encode(left.ty or S.unit) .. " and " .. S.encode(right.ty or S.unit)
                    .. "; convert one side explicitly", span)
            end
        end
    end
    local irOp = FLOAT_ARITH[op] or COMPARE[op]
    if not irOp then
        D.reject("type-mismatch", "Operator " .. op .. " has no meaning for f64", span)
    end
    if V.isKnown(left) and V.isKnown(right) then
        local a, b = left.n, right.n
        if op == "+" then return k(machine, V.f64(a + b)) end
        if op == "-" then return k(machine, V.f64(a - b)) end
        if op == "*" then return k(machine, V.f64(a * b)) end
        if op == "/" then return k(machine, V.f64(a / b)) end
        local result
        if op == "==" then result = a == b
        elseif op == "!=" then result = a ~= b
        elseif op == "<" then result = a < b
        elseif op == "<=" then result = a <= b
        elseif op == ">" then result = a > b
        else result = a >= b end
        return k(machine, V.bool(result))
    end
    local ty = COMPARE[op] and S.bool or S.f64
    return self:expressionCPS(machine, ctx, left, nil, function(m, leftExpr)
        return self:expressionCPS(m, ctx, right, nil, function(m2, rightExpr)
            return k(m2, V.runtime(ctx.builder:bin(irOp, leftExpr, rightExpr, ty), ty))
        end)
    end)
end
-- The terminal continuation is `done`, declared with the machine require above.


-- A direct-style caller enters a converted method here. The chain runs on the session's machine -- one
-- per session, so a builtin that re-enters evaluation gets a second stack instead of corrupting this
-- one -- and answers a value. The host frame this costs is one per *boundary*, not one per step, so it
-- shrinks as the conversion proceeds and disappears with the last unconverted caller.
function Eval:drive(ctx, entry)
    local machine = ctx.session.machine
    if not machine then
        machine = Machine.new(ctx.session)
        ctx.session.machine = machine
    end
    return machine:call(entry)
end


-- The module-initialization entry, which the reference interpreter uses. It drives the converted walk
-- once, so the harness never needs the machine's protocol.
function Eval:initializeModule(program, top)
    return self:drive(self:staticFrame(top, nil), function(machine)
        return self:initializeModuleCPS(machine, program, top, done)
    end)
end

-- The export-resolution entry, which the loader uses for one exported item at a time.
function Eval:resolveExportItem(item, top)
    return self:drive(self:staticFrame(top, item.span), function(machine)
        return self:resolveExportItemCPS(machine, item, top, done)
    end)
end

-- The compile entry, which the harness and the tests call. It is not called from inside the
-- evaluator: it starts the machine's loop once and hands back the compilation.
function Eval:compile(program, loadedTop)
    return self:drive(self:staticFrame(nil, nil), function(machine)
        return self:compileCPS(machine, program, loadedTop, done)
    end)
end

-- The harness's compile driver: load, initialise, resolve the exports, then build an instance for

-- The harness's entry into a word: `interpret` supplies an exported word with concrete arguments and
-- gets a value back. It is deliberately *not* one of the scaffold shims -- nothing inside the evaluator
-- calls it -- so it outlives them, and it is the one place outside the evaluator where the machine's
-- loop is started.
-- The harness's other entry: the exported word a name refers to. Like `supplyTop` it exists for
-- callers outside the evaluator and is not called from inside it.
function Eval:exportedTop(program, name, top)
    return self:drive(self:staticFrame(top, nil), function(machine)
        return self:exportedValueCPS(machine, program, name, top, done)
    end)
end

function Eval:supplyTop(ctx, callee, args, span)
    return self:drive(ctx, function(machine)
        return self:supplyCPS(machine, ctx, callee, args, span, done)
    end)
end

-- Unary (`-x`, `not x`, `~x`). Its only child is the operand, so the CPS shape is one continuation
-- that applies the operator -- the shape every other expression family follows:
--
--     return evalExprCPS(machine, ctx, child, function(m, value) ... return k(m, result) end)
--
-- During the migration the child still comes from the direct walker below, which costs host frames for
-- the operand's own nesting (bounded by the source expression) and none on the machine's path.
-- A unary operator. The operand is one step, and the three cases that need it as IR each materialise
-- it in their own continuation, so the operator itself costs a step and no frames.
function Eval:evalUnary(machine, ctx, expr, k)
    return self:evalExprCPS(machine, ctx, expr.operand, function(m, value)
        local op = expr.operator
        if op == "not" then
            self:requireType(value, S.bool, expr.operand.span)
            if V.tag(value) == "bool" then return k(m, V.bool(not value.b)) end
            return self:expressionCPS(m, ctx, value, nil, function(m2, operand)
                return k(m2, V.runtime(ctx.builder:un("Not", operand, S.bool), S.bool))
            end)
        end
        if value.ty:isF64() then
            -- Only negation applies to a float; complement and shift are integer operations.
            if op ~= "-" then
                D.reject("type-mismatch", "Negation is the only unary operator f64 has, not " .. op,
                    expr.operand.span)
            end
            if V.isKnown(value) then return k(m, V.f64(-value.n)) end
            return self:expressionCPS(m, ctx, value, nil, function(m2, operand)
                return k(m2, V.runtime(ctx.builder:un("Neg", operand, S.f64), S.f64))
            end)
        end
        if not value.ty:isInteger() then
            D.reject("type-mismatch", "Expected an integer but found " .. S.encode(value.ty),
                expr.operand.span)
        end
        local ty = value.ty
        if V.isInteger(value) then
            if ty:isWide() then
                local high, low = wordsOf(value)
                if op == "-" then return k(m, V.int64(ty, U64Kernel.neg(high, low))) end
                return k(m, V.int64(ty, U64Kernel.bnot(high, low)))
            end
            local n = op == "-" and wrap(ty, -value.n) or wrap(ty, bit.bnot(value.n))
            return k(m, V.int(ty, n))
        end
        return self:expressionCPS(m, ctx, value, nil, function(m2, operand)
            return k(m2, V.runtime(ctx.builder:un(op == "-" and "Neg" or "BitNot", operand, ty), ty))
        end)
    end)
end
-- Both operands are evaluated on the machine, so a chain of operators (`a + b + c`) is tail calls.
-- This is where expression depth stops costing host frames: the nested `evalExprCPS` calls below are
-- in tail position and the driver reuses the frame.
function Eval:evalBinaryCPS(machine, ctx, expr, k)
    local op = expr.operator
    if op == "and" or op == "or" then
        return self:evalShortCircuit(machine, ctx, expr, k)
    end
    return self:evalExprCPS(machine, ctx, expr.left, function(m, left)
        return self:evalExprCPS(m, ctx, expr.right, function(m2, right)
            return self:binaryOpCPS(m2, ctx, op, left, right, expr.left.span, expr.right.span,
                expr.span, k)
        end)
    end)
end

-- One implementation of every binary operator, shared by expressions and compound stores.

-- Both operands as IR, then one operation. Seven places want exactly this, so it is a method rather
-- than seven nested continuation pairs.
function Eval:binaryOperandsCPS(machine, ctx, left, right, irOp, ty, k)
    return self:expressionCPS(machine, ctx, left, nil, function(m, leftExpr)
        return self:expressionCPS(m, ctx, right, nil, function(m2, rightExpr)
            return k(m2, V.runtime(ctx.builder:bin(irOp, leftExpr, rightExpr, ty), ty))
        end)
    end)
end

function Eval:binaryOpCPS(machine, ctx, op, left, right, leftSpan, rightSpan, span, k)
    if left.ty:isPtr() or right.ty:isPtr() then
        -- Two addresses of one element type compare by address. A pointer has no order and no integer
        -- value, so nothing else about it is offered.
        if (op ~= "==" and op ~= "!=") or left.ty ~= right.ty then
            D.reject("type-mismatch", "A pointer compares only with a pointer of one element type, found "
                .. S.encode(left.ty or S.unit) .. " and " .. S.encode(right.ty or S.unit), span)
        end
        if not ctx.residual then
            D.reject("runtime-in-normalization", "A pointer comparison needs runtime code", span)
        end
        return self:binaryOperandsCPS(machine, ctx, left, right, COMPARE[op], S.bool, k)
    end
    if left.ty:isF64() or right.ty:isF64() then
        return self:floatOpCPS(machine, ctx, op, left, right, leftSpan, rightSpan, span, k)
    end
    leftSpan, rightSpan, span = leftSpan or ctx.span, rightSpan or ctx.span, span or ctx.span
    if (op == "==" or op == "!=") and left.ty:isString() and right.ty:isString() then
        -- Strings compare by content: a byte sequence has no identity a program can observe, so
        -- pointer equality would be a surprising answer rather than the useful one.
        if V.tag(left) == "string" and V.tag(right) == "string" then
            return k(machine, V.bool((left.bytes == right.bytes) == (op == "==")))
        end
        if not ctx.residual then
            D.reject("runtime-in-normalization", "A run-time string comparison needs runtime code", span)
        end
        return self:binaryOperandsCPS(machine, ctx, left, right, COMPARE[op], S.bool, k)
    end
    if (op == "==" or op == "!=") and left.ty:isBool() and right.ty:isBool() then
        -- A bool compares by value. The operation is not ordered: section 7 offers bool only
        -- equality, exactly as it offers only equality for unit.
        if V.isKnown(left) and V.isKnown(right) then
            return k(machine, V.bool((left.b == right.b) == (op == "==")))
        end
        return self:binaryOperandsCPS(machine, ctx, left, right, COMPARE[op], S.bool, k)
    end
    if (op == "==" or op == "!=") and left.ty:isUnit() and right.ty:isUnit() then
        -- unit has one value and no runtime representation, so both operands already ran for their
        -- effects and the answer is known: unit equals unit.
        return k(machine, V.bool(op == "=="))
    end
    if COMPARE[op] then
        -- A comparison widens both sides, which is always safe and never narrows.
        if left.ty:isInteger() and right.ty:isInteger() and left.ty ~= right.ty then
            local wider
            if left.literal and not right.literal and wordsFit(right.ty, wordsOf(left)) then
                wider = right.ty
            elseif right.literal and not left.literal and wordsFit(left.ty, wordsOf(right)) then
                wider = left.ty
            else
                wider = S.widerThan(left.ty, right.ty)
            end
            if not wider then
                D.reject("type-mismatch", "A comparison needs one integer type, found "
                    .. S.encode(left.ty) .. " and " .. S.encode(right.ty)
                    .. "; convert one side explicitly", span)
            end
            self:requireType(left, wider, leftSpan)
            self:requireType(right, wider, rightSpan)
        end
        if not left.ty:isInteger() or left.ty ~= right.ty then
            D.reject("type-mismatch", "Comparison needs two integers of one width, found "
                .. S.encode(left.ty or S.unit) .. " and " .. S.encode(right.ty or S.unit), span)
        end
        if V.isInteger(left) and V.isInteger(right) then
            local a, b = left.n, right.n
            local result
            if op == "==" then result = a == b
            elseif op == "!=" then result = a ~= b
            elseif op == "<" then result = a < b
            elseif op == "<=" then result = a <= b
            elseif op == ">" then result = a > b
            else result = a >= b end
            return k(machine, V.bool(result))
        end
        return self:binaryOperandsCPS(machine, ctx, left, right, COMPARE[op], S.bool, k)
    end
    local irOp = ARITH[op]
    if not irOp then D.bug("operator", "Unknown binary operator " .. tostring(op)) end
    -- A shift takes its amount as a plain u32; every other operator needs both sides at one width.
    if op == "<<" or op == ">>" then
        if not left.ty:isInteger() then
            D.reject("type-mismatch", "A shift needs an integer to shift, found "
                .. S.encode(left.ty or S.unit), leftSpan)
        end
        self:requireType(right, S.u32, rightSpan)
    else
        if not left.ty:isInteger() or not right.ty:isInteger() then
            D.reject("type-mismatch", "Arithmetic needs two integers, found "
                .. S.encode(left.ty or S.unit) .. " and " .. S.encode(right.ty or S.unit), span)
        end
        -- Which width the result has is decided by what is written, not by what is known, so the
        -- interpreter and the generated code agree: a literal adopts the other operand's width when
        -- it fits, and otherwise the wider width wins.
        if left.ty ~= right.ty then
            local ty
            if left.literal and not right.literal then
                if wordsFit(right.ty, wordsOf(left)) then ty = right.ty end
            elseif right.literal and not left.literal then
                if wordsFit(left.ty, wordsOf(right)) then ty = left.ty end
            else
                ty = S.widerThan(left.ty, right.ty)
            end
            if not ty then
                D.reject("type-mismatch", "Arithmetic needs one integer type, found "
                    .. S.encode(left.ty) .. " and " .. S.encode(right.ty)
                    .. "; convert one side explicitly", span)
            end
            self:requireType(left, ty, leftSpan)
            self:requireType(right, ty, rightSpan)
        end
    end
    local ty = left.ty
    if (op == "/" or op == "%") and V.isInteger(right) and right.n == 0 then
        D.reject("division-zero", "Known zero divisor", rightSpan)
    end
    if ty:isWide() and V.isInteger(left) and V.isInteger(right) then
        local ah, al = wordsOf(left)
        local bh, bl = wordsOf(right)
        local high, low
        if op == "+" then high, low = U64Kernel.add(ah, al, bh, bl)
        elseif op == "-" then high, low = U64Kernel.sub(ah, al, bh, bl)
        elseif op == "*" then high, low = U64Kernel.mul(ah, al, bh, bl)
        elseif op == "/" then
            if ty:isSigned() then high, low = U64Kernel.sdivmod(ah, al, bh, bl)
            else high, low = U64Kernel.divmod(ah, al, bh, bl) end
        elseif op == "%" then
            if ty:isSigned() then _, _, high, low = U64Kernel.sdivmod(ah, al, bh, bl)
            else _, _, high, low = U64Kernel.divmod(ah, al, bh, bl) end
        elseif op == "^" then high, low = U64Kernel.pow(ah, al, bh, bl)
        elseif op == "<<" then high, low = U64Kernel.shl(ah, al, bl)
        elseif op == ">>" then
            if ty:isSigned() then high, low = U64Kernel.sar(ah, al, bl)
            else high, low = U64Kernel.shr(ah, al, bl) end
        elseif op == "&" then high, low = U64Kernel.band(ah, al, bh, bl)
        elseif op == "|" then high, low = U64Kernel.bor(ah, al, bh, bl)
        else high, low = U64Kernel.bxor(ah, al, bh, bl) end
        return k(machine, V.int64(ty, high, low))
    end
    if V.isInteger(left) and V.isInteger(right) then
        local x, y = left.n, right.n
        local result
        if op == "+" then result = wrap(ty, x + y)
        elseif op == "-" then result = wrap(ty, x - y)
        elseif op == "*" then result = mulExact(ty, x, y)
        elseif op == "/" then result = ty:isSigned() and signedDiv(ty, x, y) or math.floor(x / y)
        elseif op == "%" then
            result = ty:isSigned() and signedRem(ty, x, y) or x - y * math.floor(x / y)
        elseif op == "^" then
            if ty:isSigned() and y < 0 then
                D.reject("numeric-range", "A signed power needs a power that is not negative", span)
            end
            result = pow(ty, x, y)
        elseif op == "<<" then result = wrap(ty, x * 2 ^ y)
        elseif op == ">>" then
            -- A signed shift is arithmetic: it keeps the sign bit.
            result = math.floor(x / 2 ^ y)
        elseif op == "&" then result = wrap(ty, bit.band(x, y))
        elseif op == "|" then result = wrap(ty, bit.bor(x, y))
        else result = wrap(ty, bit.bxor(x, y)) end
        return k(machine, V.int(ty, result))
    end
    local builder = ctx.builder
    return self:expressionCPS(machine, ctx, left, nil, function(m2, leftExpr)
        return self:expressionCPS(m2, ctx, right, nil, function(m3, rightExpr)
            -- A signed power with a negative exponent has no result, so a run-time one is checked first.
            if op == "^" and ty:isSigned() then
                if V.isKnown(right) and right.n < 0 then
                    D.reject("numeric-range", "A signed power needs a power that is not negative", rightSpan)
                end
                if not V.isKnown(right) then
                    builder:emit(ctx.body, Ir.Trap(builder:bin("Lt", rightExpr,
                        builder:int(right.ty, 0), S.bool), "numeric-range"))
                end
            end
            if (op == "/" or op == "%") and not V.isInteger(right) then
                builder:trap(ctx.body, builder:bin("Eq", rightExpr, builder:u32(0), S.bool),
                    "division-zero")
            end
            return k(m3, V.runtime(builder:bin(irOp, leftExpr, rightExpr, ty), ty))
        end)
    end)
end

-- `a and b` / `a or b`: the left side decides whether the right side runs at all, so each answer is
-- its own continuation. The right side of the residual form is evaluated under the arm's frame, which
-- is the one place a continuation has to carry a *different* ctx (`yesCtx`) than its caller's.
-- `a and b` / `a or b`: the left side decides whether the right side runs at all, so each answer is
-- its own continuation. The right side of the residual form is evaluated under the arm's frame, which
-- is the one place a continuation has to carry a *different* ctx (`yesCtx`) than its caller's.
function Eval:evalShortCircuit(machine, ctx, expr, k)
    return self:evalExprCPS(machine, ctx, expr.left, function(m, left)
        self:requireType(left, S.bool, expr.left.span)
        local isOr = expr.operator == "or"
        if V.tag(left) == "bool" then
            local short = isOr and left.b or (not isOr and not left.b)
            if short then return k(m, V.bool(isOr)) end
            return self:evalExprCPS(m, ctx, expr.right, function(m2, right)
                self:requireType(right, S.bool, expr.right.span)
                return k(m2, right)
            end)
        end
        return self:expressionCPS(m, ctx, left, nil, function(m2, test)
            local yesList, noList = {}, {}
            local yesCtx = ctx:arm(yesList)
            return self:evalExprCPS(m2, yesCtx, expr.right, function(m3, yesValue)
                self:requireType(yesValue, S.bool, expr.right.span)
                local builder = ctx.builder
                local storage = builder:var(ctx.body, S.bool, nil)
                local place = Ir.Local(storage)
                return self:expressionCPS(m3, yesCtx, yesValue, nil, function(m4, yesExpr)
                    builder:store(yesList, place, yesExpr)
                    builder:store(noList, place, builder:bool(isOr))
                    builder:emit(ctx.body, Ir.If(test, S.list(yesList), S.list(noList)))
                    return k(m4, V.runtime(builder:ref(builder:read(ctx.body, S.bool, place), S.bool),
                        S.bool))
                end)
            end)
        end)
    end)
end
-- Evaluates an expression in an expected-signature position. Only a lambda (or a conditional
-- choosing between lambdas) consumes the expectation; anything else evaluates normally.

-- Evaluates an expression in an expected-signature position. Every arm is a tail call into a converted
-- method, so the expectation costs no frame of its own: this is the router's expectation-aware twin.
function Eval:evalExpectedCPS(machine, ctx, expr, expected, k)
    if expected == nil then return self:evalExprCPS(machine, ctx, expr, k) end
    if expr.kind == "Lambda" then return self:evalLambdaCPS(machine, ctx, expr, expected, k) end
    if expr.kind == "ArrayExpr" then return self:evalArrayCPS(machine, ctx, expr, expected, k) end
    if expr.kind == "Condition" then return self:evalConditionCPS(machine, ctx, expr, expected, k) end
    return self:evalExprCPS(machine, ctx, expr, k)
end


-- `if then else` as an expression. The test is one step on the machine; what follows stays in one
-- frame because the arms are `evalExpected` (not yet converted), and every terminal answer goes
-- through `k` so the caller is not made to return through this frame.
function Eval:evalConditionCPS(machine, ctx, expr, expected, k)
    -- The test is not a tail position; both arms are.
    local tail = ctx.tail
    ctx.tail = false
    return self:evalExprCPS(machine, ctx, expr.test, function(m, test)
        self:requireType(test, S.bool, expr.test.span)
        if V.tag(test) == "bool" then
            ctx.tail = tail
            return self:evalExpectedCPS(m, ctx, test.b and expr.yes or expr.no, expected, k)
        end
        local builder = ctx.builder
        return self:expressionCPS(m, ctx, test, nil, function(m2, testExpr)
            local yesList, noList = {}, {}
            -- Both arms are tail positions, so each arm context inherits the flag.
            ctx.tail = tail
            local yesCtx, noCtx = ctx:arm(yesList), ctx:arm(noList)
            ctx.tail = false
            return self:evalExpectedCPS(m2, yesCtx, expr.yes, expected, function(m3, yesValue)
                local yesTerminated = yesCtx.terminated or false
                return self:evalExpectedCPS(m3, noCtx, expr.no, expected, function(m4, noValue)
                    local noTerminated = noCtx.terminated or false
                    return self:evalConditionJoin(m4, ctx, expr, yesCtx, noCtx, yesValue, yesTerminated,
                        noValue, noTerminated, yesList, noList, testExpr, builder, k)
                end)
            end)
        end)
    end)
end

-- Join a logical result vector, preserving equal static components and erasing unit. Materialize
-- under each arm's own context, then emit the control once (not once per result component).
function Eval:evalConditionJoin(m, ctx, expr, yesCtx, noCtx, yesValue, yesTerminated, noValue,
        noTerminated, yesList, noList, testExpr, builder, k)
    local function emit()
        if #yesList > 0 or #noList > 0 then
            builder:emit(ctx.body, Ir.If(testExpr, S.list(yesList), S.list(noList)))
        end
    end
    if yesTerminated and noTerminated then
        emit() -- Both paths transfer, but their stores/effects/back edges must still run.
        ctx.terminated = true
        return k(m, V.unit())
    end
    local yes, no = self:expand(yesValue), self:expand(noValue)
    if not yesTerminated and not noTerminated and #yes ~= #no then
        D.reject("branch-result", "Conditional arms return different numbers of results: "
            .. #yes .. " and " .. #no, expr.span)
    end
    local count = yesTerminated and #no or #yes
    local result, slots = {}, {}
    local function finish(mm)
        emit()
        for index = 1, count do
            local slot = slots[index]
            if slot then
                local read = builder:read(ctx.body, slot.ty, slot.place)
                result[index] = V.runtime(builder:ref(read, slot.ty), slot.ty, slot.borrowed)
            end
        end
        if count == 0 then return k(mm, V.unit()) end
        if count == 1 then return k(mm, result[1]) end
        return k(mm, V.results(result))
    end
    local component
    component = function(mm, index)
        if index > count then return finish(mm) end
        local a, b = yes[index], no[index]
        local function bind(m2)
            local value = yesTerminated and b or a
            local other = noTerminated and a or b
            local sameTypeValue = V.tag(value) == "type" and V.tag(other) == "type"
                and value.value == other.value
            local oneArm = yesTerminated or noTerminated
            local known = oneArm and (V.tag(value) == "type" or self:sameKnownScalar(value, value))
                or (not oneArm and (sameTypeValue or self:sameKnownScalar(a, b)))
            if known then
                result[index] = value
                return component(m2, index + 1)
            end
            local ty = value.ty
            if not ty or ty == S.type then
                D.reject("branch-result", "Conditional static results need one common value", expr.span)
            end
            local place = Ir.Local(builder:var(ctx.body, ty, nil))
            slots[index] = {ty = ty, place = place,
                borrowed = (not yesTerminated and self:isBorrowed(a))
                    or (not noTerminated and self:isBorrowed(b))}
            local function second(m3)
                if noTerminated then return component(m3, index + 1) end
                return self:expressionCPS(m3, noCtx, b, nil, function(m4, valueExpr)
                    builder:store(noList, place, valueExpr)
                    return component(m4, index + 1)
                end)
            end
            if yesTerminated then return second(m2) end
            return self:expressionCPS(m2, yesCtx, a, nil, function(m3, valueExpr)
                builder:store(yesList, place, valueExpr)
                return second(m3)
            end)
        end
        if yesTerminated or noTerminated then return bind(mm) end
        local ac, bc = self:isCallableValue(a), self:isCallableValue(b)
        if ac and bc and not (a.ty and a.ty == b.ty) then
            return self:joinCallablesCPS(mm, a, b, expr.span, function(m2, _, joinedA, joinedB)
                a, b = joinedA, joinedB
                return bind(m2)
            end)
        end
        if a.ty ~= b.ty then
            D.reject("branch-result", "Conditional arms have different types: "
                .. (a.ty and S.encode(a.ty) or "a bare callable") .. " and "
                .. (b.ty and S.encode(b.ty) or "a bare callable"), expr.span)
        end
        return bind(mm)
    end
    return component(m, 1)
end
-- Schemas and records -------------------------------------------------------------------------

-- A schema literal: data fields, methods, and no bound fields yet.
-- A schema expression is one call: `newSchema` builds it, and the router reaches this on the machine.
function Eval:evalSchemaCPS(machine, ctx, expr, k)
    return self:newSchemaCPS(machine, ctx, expr, nil, nil, nil, k)
end

-- Builds a schema, or a specialised copy of `base` with extra static (readonly) fields.

-- A schema literal: the members are walked in written order, and a field's type is resolved on the
-- type path, which is what lets a schema mention a cell its own definition reserved.
function Eval:newSchemaCPS(machine, ctx, expr, statics, readonly, base, k)
    self.nextDef = self.nextDef + 1
    local def = {
        id = self.nextDef, span = expr.span, node = expr,
        statics = statics or {}, readonly = readonly or {},
        fields = {}, fieldOrder = {}, methods = {},
    }
    if base then
        for name, ty in pairs(base.fields) do def.fields[name] = ty end
        for _, name in ipairs(base.fieldOrder) do def.fieldOrder[#def.fieldOrder + 1] = name end
        for name, method in pairs(base.methods) do def.methods[name] = method end
        def.type, def.fieldNames = base.type, base.fieldNames
        return k(machine, V.schema(def))
    end
    local function finish()
        local names = {}
        for name in pairs(def.fields) do names[#names + 1] = name end
        local fields = {}
        for _, name in ipairs(names) do fields[name] = def.fields[name] end
        def.type = S.record(fields)
        def.fieldNames = names
        return k(machine, V.schema(def))
    end
    local function memberAt(index)
        if index > #expr.members then return finish() end
        local member = expr.members[index]
        if member.kind ~= "FieldMember" then
            local name = member.def.name.text
            if def.fields[name] or def.methods[name] then
                D.reject("duplicate", "Duplicate schema member " .. name, member.def.name.span)
            end
            local method = self:define(member.def, ctx.scope, def)
            def.methods[name] = method
            return memberAt(index + 1)
        end
        local name = member.name.text
        return self:typeOfCPS(machine, member.type, ctx.scope, member.span, function(m, ty)
            -- A field declared as a signature is represented by the borrowed callable ABI: the
            -- field holds an invocation pointer and an environment pointer, not callable code.
            if ty:isSig() then ty = S.view(ty) end
            if def.fields[name] or def.methods[name] then
                D.reject("duplicate", "Duplicate schema member " .. name, member.name.span)
            end
            def.fields[name] = ty
            def.fieldOrder[#def.fieldOrder + 1] = name
            return memberAt(index + 1)
        end)
    end
    return memberAt(1)
end
-- `Schema { field = value }`: either a partial (static) supply or a construction.

-- Keyed supply `S { ... }`: a variant payload, a match, a keyed callable, or a schema instance. The
-- two field walks are local drivers answering through `k`; `makeVariant`, `constructRecord`, `newSchema`
-- and `applyKeyed` are still direct, so each is one answer through `k`.
function Eval:evalSupplyCPS(machine, ctx, expr, k)
    -- The tail position belongs to a keyed invocation, not to the base or the supplied values.
    local tail = ctx.tail
    ctx.tail = false
    return self:evalExprCPS(machine, ctx, expr.schema, function(m, base)
        if V.tag(base) == "ctor" then
            -- A sum alternative with a record payload is built like a record, then tagged.
            if #expr.fields == 0 and base.caseType == S.unit then
                return self:makeVariantCPS(m, ctx, base, nil, expr.span, k)
            end
            if not base.caseType:isRecord() then
                D.reject("variant-payload",
                    "Alternative " .. base.case .. " does not take a record; apply it to one value instead",
                    expr.span)
            end
            local values = {}
            local function payload(index)
                if index > #expr.fields then
                    for _, field in ipairs(base.caseType.fields) do
                        if values[field.name] == nil then
                            D.reject("variant-payload", "Alternative " .. base.case .. " is missing field "
                                .. field.name, expr.span)
                        end
                    end
                    return self:constructRecordCPS(machine, ctx, base.caseType, values, nil,
                        function(m, record)
                            return self:makeVariantCPS(m, ctx, base, record, expr.span, k)
                        end)
                end
                local field = expr.fields[index]
                local name = field.name.text
                if not S.field(base.caseType, name) then
                    D.reject("unknown-member", "Alternative " .. base.case .. " has no field " .. name,
                        field.name.span)
                end
                if values[name] ~= nil then
                    D.reject("duplicate", "Field " .. name .. " is supplied twice", field.name.span)
                end
                return self:evalExprCPS(machine, ctx, field.value, function(mm, value)
                    values[name] = value
                    return payload(index + 1)
                end)
            end
            return payload(1)
        end
        if V.tag(base) == "variant" or (V.tag(base) == "runtime" and base.ty:isSum()) then
            return self:evalMatchCPS(machine, ctx, base, expr, nil, k)
        end
        if V.tag(base) == "word" and base.def.keyed then
            return self:applyKeyedCPS(m, ctx, base, expr.fields, expr.span, tail, k)
        end
        if V.tag(base) ~= "schema" then
            D.reject("schema-required", "Keyed supply needs a schema on the left", expr.schema.span)
        end
        local def = base.def
        local supplied = {}
        local function afterFields()
            -- A field is still runtime if the base did not bind it statically.
            local missing = {}
            for _, name in ipairs(def.fieldOrder) do
                if supplied[name] == nil and def.statics[name] == nil then missing[#missing + 1] = name end
            end
            if #missing > 0 then
                -- Partial supply: every supplied field must be static, and becomes readonly.
                local statics, readonly = {}, {}
                for name, value in pairs(def.statics) do statics[name], readonly[name] = value, true end
                for name, value in pairs(supplied) do
                    if not V.isStatic(value) then
                        D.reject("static-required",
                            "Partial schema supply needs a static value for field " .. name, expr.span)
                    end
                    statics[name], readonly[name] = value, true
                end
                return self:newSchemaCPS(machine, ctx, def.node, statics, readonly, def, k)
            end

            -- Saturated construction: the instance owns mutable storage for every data field.
            local values = {}
            for name, value in pairs(def.statics) do values[name] = value end
            for name, value in pairs(supplied) do values[name] = value end
            for _, name in ipairs(def.fieldOrder) do
                if values[name] == nil then D.bug("schema-fields", "A data field was not supplied") end
            end
            local ty = def.type
            if not ctx.residual then
                -- Static evaluation builds a concrete record; it is not runtime storage.
                local fields = {}
                for _, name in ipairs(def.fieldNames) do fields[name] = values[name] end
                return k(machine, V.record(ty, fields, def))
            end
            return self:constructRecordCPS(machine, ctx, ty, values, def, k)
        end
        -- The supplied fields are evaluated in written order, one CPS step each, and the rest of the
        -- body runs once they are all in -- which is why the terminal branch calls it.
        local function field(index)
            if index > #expr.fields then return afterFields() end
            local entry = expr.fields[index]
            local name = entry.name.text
            if not def.fields[name] then
                D.reject("unknown-member", "Schema has no field " .. name, entry.name.span)
            end
            if supplied[name] ~= nil or def.statics[name] ~= nil then
                D.reject("duplicate", "Field " .. name .. " is supplied twice", entry.name.span)
            end
            return self:evalExprCPS(machine, ctx, entry.value, function(mm, value)
                supplied[name] = value
                return field(index + 1)
            end)
        end
        return field(1)
    end)
end

-- Builds a record value of `ty` from a field-name keyed supply. `def` supplies methods and static
-- bindings when the record came from a source schema; it is absent for a sum alternative.

-- A record built from a field-name keyed supply.
-- A record built from a field-name keyed supply.
function Eval:constructRecordCPS(machine, ctx, ty, values, def, k)
    if not ctx.residual then
        local fields = {}
        for _, name in ipairs(S.fieldNames(ty)) do fields[name] = values[name] or V.unit() end
        return k(machine, V.record(ty, fields, def))
    end
    local exprs, borrowed = {}, false
    local function fieldAt(index)
        if index > #ty.fields then
            -- The Make is the value until a place is demanded (a field store, a reference, or a borrowed
            -- receiver). `body` is where that spill goes, so a demand from inside an arm still names
            -- storage the outer scope remembers. No storage exists until something needs an address.
            return k(machine, V.object(ty, nil, def, borrowed, nil, ctx.builder:make(ty, exprs), ctx.body))
        end
        local field = ty.fields[index]
        local fieldValue = values[field.name] or V.unit()
        -- A signature-typed field is a view whose environment points at a local adapter, so an
        -- instance holding one is itself tied to this activation.
        if self:isBorrowed(fieldValue) or field.type:isView() then borrowed = true end
        return self:expressionCPS(machine, ctx, fieldValue, field.type, function(m, expr)
            exprs[index] = expr
            return fieldAt(index + 1)
        end)
    end
    return fieldAt(1)
end
-- Field selection: the base is the one child, so its evaluation is a continuation and every answer
-- below goes through `k`. The member rules themselves are unchanged and still run inline.
function Eval:evalFieldSelectCPS(machine, ctx, expr, k)
    return self:evalExprCPS(machine, ctx, expr.base, function(m, value)
        local name = expr.field.text
        -- Selection through a reference selects from the instance it names, so the reference is read
        -- as that instance and the ordinary member rules apply.
        local base = self:placeObject(value) or value
        if base.ty and base.ty:isSlice() and name == "length" then
            local known = self:sliceCount(base)
            if known then return k(m, V.u32(known)) end
            if not ctx.residual then
                D.reject("runtime-in-normalization", "A runtime slice length needs runtime code", expr.span)
            end
            return self:expressionCPS(m, ctx, base, base.ty, function(m2, data)
                return k(m2, V.runtime(ctx.builder:sliceLength(data, S.u32), S.u32))
            end)
        end
        local tag = V.tag(base)
        if tag == "object" then
            local def = base.schema
            if def.methods[name] then return k(m, V.method(def.methods[name], base)) end
            if def.fields[name] then
                return k(m, self:readFieldValue(ctx, self:fieldSlot(def, base, name), expr.span))
            end
            D.reject("unknown-member", "Value has no member " .. name, expr.field.span)
        elseif tag == "record" then
            if base.schema and base.schema.methods[name] then
                return k(m, V.method(base.schema.methods[name], base))
            end
            if base.fields[name] ~= nil then return k(m, base.fields[name]) end
            D.reject("unknown-member", "Record has no field " .. name, expr.field.span)
        elseif tag == "schema" then
            if base.def.methods[name] then return k(m, V.method(base.def.methods[name], nil)) end
            D.reject("unknown-member", "Schema has no member " .. name, expr.field.span)
        elseif tag == "namespace" then
            local member = base.members[name]
            if not member then
                D.reject("unknown-member", "Module " .. tostring(base.module) .. " does not export " .. name,
                    expr.field.span)
            end
            return k(m, member)
        elseif tag == "type" and base.value:isSum() then
            -- A sum type's member names a constructor for one alternative.
            local caseType = S.caseOf(base.value, name)
            if not caseType then
                D.reject("unknown-member", "Sum type has no alternative " .. name, expr.field.span)
            end
            return k(m, V.ctor(base.value, name, caseType))
        elseif tag == "runtime" and (base.ty:isRef() or base.ty:isPtr()) then
            -- A reference and a raw pointer reach the record they address the same way, so the field
            -- is the same projection one dereference on; only the lifetime rule differs, and a
            -- pointer has none to check.
            local ty = S.field(self:pointeeType(base.ty), name)
            if not ty then D.reject("unknown-member", "Record has no field " .. name, expr.field.span) end
            return self:derefPlaceCPS(m, ctx, base, expr.span, function(m2, deref)
                local place = Ir.Project(deref, Ir.Field(name))
                local read = ctx.builder:read(ctx.body, ty, place)
                return k(m2, V.runtime(ctx.builder:ref(read, ty), ty))
            end)
        elseif tag == "runtime" and base.ty:isRecord() then
            local ty = S.field(base.ty, name)
            if not ty then D.reject("unknown-member", "Record has no field " .. name, expr.field.span) end
            if not ctx.residual then
                D.reject("runtime-in-normalization", "Cannot read a runtime record field here", expr.span)
            end
            -- A record value spilled into storage for a store must read through that storage, so a
            -- store and a later read observe the same instance instead of the pre-spill value.
            if base.place then
                local place = Ir.Project(base.place, Ir.Field(name))
                local read = ctx.builder:read(ctx.body, ty, place)
                return k(m, V.runtime(ctx.builder:ref(read, ty), ty, nil, place))
            end
            return k(m, V.runtime(ctx.builder:get(base.expr, name, ty), ty))
        end
        D.reject("member-required", "Cannot select from " .. S.encode(base.ty or S.unit), expr.span)
    end)
end

function Eval:fieldSlot(def, object, name)
    -- A compile-time object has no storage, so the place is only built when there is one; such a
    -- slot is read and written through the frontend value instead.
    return { kind = "field", name = name, ty = def.fields[name],
        place = object.place and Ir.Project(object.place, Ir.Field(name)) or nil, record = object,
        static = def.statics[name], readonly = def.readonly[name] and true or false }
end

-- Stores -------------------------------------------------------------------------------------

-- An assignment. The target resolves once, and for a compound operator the old value is read before
-- the right-hand side runs, which is what makes `x += f()` see the value `x` had.
function Eval:execStoreCPS(machine, ctx, stmt, k)
    return self:storeTargetCPS(machine, ctx, stmt.target, function(m, slot, place)
        if slot.readonly then
            D.reject("readonly-field", "Field " .. slot.name .. " was bound by static supply and cannot be assigned",
                stmt.target.span)
        end
        local operator = stmt.operator
        if operator == "=" then
            return self:evalExprCPS(m, ctx, stmt.value, function(m2, value)
                self:requireAgainst(value, slot.ty, stmt.value.span)
                return self:writeSlotCPS(m2, ctx, slot, place, value, k)
            end)
        end
        local binary = COMPOUND[operator]
        if not binary then D.bug("operator", "Unknown assignment operator " .. tostring(operator)) end
        -- The target is evaluated once, the old value read once, then the RHS runs.
        return self:readSlotCPS(m, ctx, slot, stmt.target.span, function(m2, old)
            return self:evalExprCPS(m2, ctx, stmt.value, function(m3, value)
                return self:binaryOpCPS(m3, ctx, binary, old, value, stmt.target.span,
                    stmt.value.span, stmt.span, function(m4, combined)
                        return self:writeSlotCPS(m4, ctx, slot, place, combined, k)
                    end)
            end)
        end)
    end)
end

-- Resolves a store target to a place, plus the slot describing it.

-- Resolves a store target to a slot plus its place. `placeOf` may evaluate an index expression, so it
-- is the one continuation; what the place turned out to be then decides the borrow and module rules.
function Eval:storeTargetCPS(machine, ctx, target, k)
    if target.kind ~= "Reference" and target.kind ~= "FieldSelect" and target.kind ~= "IndexExpr" then
        D.reject("not-a-place", "Only storage can be assigned", target.span)
    end
    -- A binding is immutable, so only a place beneath one can be written.
    if target.kind == "Reference" then
        local slot = lookup(ctx.scope, target.name.text)
        if not slot then D.reject("unknown-name", "Unknown name: " .. target.name.text, target.name.span) end
        if slot.kind ~= "field" and slot.kind ~= "concrete-field"
            and slot.kind ~= "concrete-index" then
            D.reject("not-a-place", "Only record fields and array elements can be assigned",
                target.span)
        end
    end
    return self:placeOfCPS(machine, ctx, target, target.span, function(m, reached)
      local function withOrigin(m2, origin)
        -- A store in residual code goes to storage. Normalize code writes the concrete value it names so
        -- a later read observes it: a local or enclosing aggregate, or module storage under the reference
        -- interpreter (`session.run`), which executes the program rather than specialising it. Module
        -- storage is runtime state, so compile-time initialization and residual specialization never
        -- write it; a mutating top-level initializer rejects instead of baking a moved start value.
        -- `placeOrigin` names the route a *name* spells, so a write through a local binding that holds a
        -- reference to module storage looks like a local write. What the place turned out to be is the
        -- other half of the question, and without it such a write is folded away with its effect lost.
        local modules = origin == "module"
            or (reached.container ~= nil and reached.container.module == true)
        -- Module storage is runtime state: residual specialization never writes it, because such a store
        -- would not appear in the generated code. Initialization (`session.moduleDemand`) and the reference
        -- interpreter (`session.run`) execute over concrete state and do write it.
        if not ctx.residual and modules
            and not (ctx.session.run or ctx.session.demanding) then
            D.reject("runtime-in-normalization",
                "Module storage is runtime state, so only module initialization may write it", target.span)
        end
        if not ctx.residual then
            if reached.concrete == "field" then
                return k(m, { kind = "concrete-field", name = reached.name, record = reached.record,
                    ty = reached.ty }, nil)
            end
            if reached.concrete == "index" then
                return k(m, { kind = "concrete-index", array = reached.array, index = reached.index,
                    ty = reached.ty }, nil)
            end
        end
        -- A slice is a view of storage someone else owns, not storage of its own, and a string
        -- literal's bytes are read-only. A write therefore names the array the view came from.
        if reached.readonly then
            D.reject("not-a-place", "A slice is a read-only view; write the array it views instead",
                target.span)
        end
        if not reached.place then
            D.bug("not-a-place", "A store target in residual code must be storage")
        end
        -- The container is the object or array whose storage is selected, so the borrow rules can see
        -- whether it is module storage or a borrowed receiver.
        return k(m, { kind = "field", name = target.kind == "IndexExpr" and "[index]" or "field",
            ty = reached.ty, place = reached.place, static = nil, readonly = false,
            record = reached.container, retaining = (reached.container and reached.container.enclosing)
                and true or false }, reached.place)
      end
      if ctx.residual then return withOrigin(m, nil) end
      return self:placeOriginCPS(m, ctx, target, function(m2, origin)
          return withOrigin(m2, origin)
      end)
    end)
end

-- Either a residual IR place or a concrete interpreter field. The span is only consulted by the
-- residual branch: a concrete read has no IR to reject.

-- A field or element read. `readFieldValue` is a leaf -- it builds IR or returns a concrete value --
-- so its answer is direct and this costs no frame of its own.
function Eval:readSlotCPS(machine, ctx, slot, span, k)
    if slot.kind == "concrete-field" then return k(machine, slot.record.fields[slot.name] or V.unit()) end
    if slot.kind == "concrete-index" then return k(machine, slot.array.items[slot.index + 1]) end
    return k(machine, self:readFieldValue(ctx, slot, span))
end

-- A store. The concrete cases write the frontend value directly; the residual case materialises the
-- value first, which is the one continuation here.
function Eval:writeSlotCPS(machine, ctx, slot, place, value, k)
    if slot.kind == "concrete-index" then
        slot.array.items[slot.index + 1] = value
        if self:isBorrowed(value) then slot.array.borrowed = true end
        return k(machine)
    end
    if slot.kind == "concrete-field" then
        slot.record.fields[slot.name] = value
        if self:isBorrowed(value) then slot.record.borrowed = true end
        return k(machine)
    end
    -- Assigning callable code to a signature-typed field builds a view whose environment is a
    -- local adapter, so the assignment is a borrow even when the code itself is not.
    local becomesBorrowed = self:isBorrowed(value) or slot.ty:isView()
    if V.tag(value) == "ref" and value.tied and (slot.retaining or (slot.record and slot.record.module)) then
        D.reject("ref-escape", self:refEscapeMessage(), ctx.span)
    end
    if becomesBorrowed and (slot.retaining or (slot.record and slot.record.module)) then
        D.reject("borrow-escape",
            "Module storage outlives the activation that made this borrow, so it cannot hold one",
            ctx.span)
    end
    return self:expressionCPS(machine, ctx, value, slot.ty, function(m, expr)
        ctx.builder:store(ctx.body, place, expr)
        -- Storing a borrow into an instance makes that instance non-retaining too.
        if becomesBorrowed and slot.record then slot.record.borrowed = true end
        return k(m)
    end)
end


-- Closure application: a static closure is evaluated now; otherwise a direct call carries the
-- captured environment as leading arguments. A closure folds only in normalize code, where folding is
-- the only way to produce a value, so it has no residual-mode probe to swallow and does not go
-- through `foldOrBuild`.

-- Closure application: a static closure is evaluated now; otherwise a direct call carries the captured
-- environment as leading arguments. A closure folds only in normalize code, where folding is the only
-- way to produce a value, so it has no residual-mode probe to swallow and does not go through
-- `foldOrBuild`.
function Eval:invokeClosureCPS(machine, ctx, plan, envExprs, values, span, bound, k)
    local def = plan.def
    local merged = appendArguments(bound, values)
    if #merged > #def.params then D.reject("arity", "Overapplication is not supported", span) end
    if #merged < #def.params then
        -- Partial application of a closure binds static arguments, exactly as for a named word.
        requireStatic(merged, span, def)
        return k(machine, V.closure(plan, merged))
    end
    if envExprs == nil and #plan.runtimeOrder == 0 then
        local allKnown = true
        for _, value in ipairs(merged) do if not V.isKnown(value) then allKnown = false end end
        if allKnown and not ctx.residual then
            return self:evaluateClosureStaticallyCPS(machine, plan, merged, span, k)
        end
    end
    if not ctx.residual then
        D.reject("runtime-in-normalization", "This closure call needs runtime code", span)
    end
    local callable = { plan = plan, env = self:closureEnvironment(plan, envExprs) }
    return self:callClosureCPS(machine, ctx, callable, merged, span, k)
end

-- Binds a known callable's hidden inputs in a local adapter and yields a view value.

-- A signature-typed view: an invocation pointer plus the environment slots it needs. No evaluation
-- edge is recursive except the capture slots, which are direct because `expression` is reached through
-- its shim.
-- A signature-typed view: an invocation pointer plus the environment slots it needs. Each branch builds
-- its slots, and `finish` emits the view once they are in.
function Eval:makeViewCPS(machine, ctx, value, sig, k)
    local viewType = S.view(sig)
    local tag = V.tag(value)
    local function finish(entry, slots)
        local id = ctx.builder:valueId()
        ctx.builder:emit(ctx.body, Ir.View(id, viewType, entry, S.list(slots)))
        -- The environment points at a local adapter, so the view is not retaining. The `Ir.BorrowArg`
        -- slots above are what record that: the checker sees the borrowed places through them.
        return k(machine, ctx.builder:ref(id, viewType))
    end
    if tag == "closure" then
        local plan = value.plan
        return self:callableInstanceCPS(machine, { plan = plan }, value.bound or {}, ctx.span,
            function(m, instance)
                local entry = instance.target
                local slots = {}
                local function captureAt(index)
                    if index > #plan.runtimeOrder then
                        for _, name in ipairs(plan.borrowedOrder) do
                            slots[#slots + 1] = Ir.BorrowArg(plan.borrowed[name].place)
                        end
                        return finish(entry, slots)
                    end
                    local capture = plan.runtime[plan.runtimeOrder[index]]
                    return self:expressionCPS(m, ctx, capture, capture.ty, function(m2, expr)
                        slots[#slots + 1] = Ir.ValueArg(expr)
                        return captureAt(index + 1)
                    end)
                end
                return captureAt(1)
            end)
    end
    if tag == "word" then
        return self:instanceForCPS(machine, value.def, ctx.span, value.args, nil, function(m, instance)
            return finish(instance.target, {})
        end)
    end
    if tag ~= "method" then D.bug("c-view", "Only known code can be bound into a view") end
    -- A method value borrows its receiver, which is exactly the hidden prefix of its instance.
    local def = value.def
    return self:instanceForCPS(machine, def, ctx.span, {}, value.receiver, function(m, instance)
        local sc = scope(def.lexical)
        local inputs = {}
        local function requirement(index)
            if index > #def.params then
                if not self:sigMatches(S.sig(inputs, instance.results), sig) then
                    D.reject("callable-shape", "Method " .. tostring(def.name)
                        .. " does not match the required signature", ctx.span)
                end
                return self:recordPlaceCPS(m, ctx, value.receiver, ctx.span, function(m2, place)
                    return finish(instance.target, { Ir.BorrowArg(place) })
                end)
            end
            return self:requirementCPS(m, def, index, sc, ctx.span, function(m2, ty)
                inputs[index] = S.inValue(ty)
                return requirement(index + 1)
            end)
        end
        return requirement(1)
    end)
end
-- An opaque callable is invoked through its view: the environment pointer plus the argument list.
-- A runtime callable is a value whose representation names code, so what it can be called as is
-- read from its type: an Owned value carries a known environment, a View is opaque code, and a
-- Tagged value is a tag plus the environment of the arm that tag names. This is the one dispatch the
-- three former entry points (`applyOwned`, `applyView`, `applyTagged`) each had in front of them.

-- Applying a callable whose code is not known at the call site: a materialised owned closure, an opaque
-- view, or a tagged callable. The last two build IR, so their argument and result lists are drivers.
function Eval:invokeRuntimeCPS(machine, ctx, value, args, span, k)
    local tag, ty = V.tag(value), value.ty
    if tag == "runtime" and ty and ty:isOwned() then
        local plan = self:planOf(ty, span)
        if #plan.borrowedOrder > 0 then
            D.bug("borrowed-callable-value",
                "A closure with borrowed captures must not have a materialised value")
        end
        if S.environmentOf(ty) == S.unit then
            -- Pure code carries no environment, so there is nothing to project: the call is direct.
            return self:invokeClosureCPS(machine, ctx, plan, {}, args, span, value.bound, k)
        end
        local envTys = {}
        for _, field in ipairs(ty.environment.fields or {}) do envTys[field.name] = field.type end
        local envExprs = {}
        for _, name in ipairs(plan.envNames) do
            envExprs[#envExprs + 1] = ctx.builder:get(value.expr, name, envTys[name])
        end
        return self:invokeClosureCPS(machine, ctx, plan, envExprs, args, span, nil, k)
    end
    if tag == "runtime" and ty and ty:isView() then
        -- An opaque callable is invoked through its view: the environment pointer plus the argument
        -- list.
        if not ctx.residual then
            D.reject("runtime-in-normalization", "An opaque callable needs runtime code", span)
        end
        local sig = ty.visible
        if #args ~= #sig.inputs then D.reject("arity", "Opaque callable arity mismatch", span) end
        local operands = {}
        local function operand(index)
            if index > #sig.inputs then
                local results = {}
                for _ = 1, #sig.results do results[#results + 1] = ctx.builder:valueId() end
                ctx.builder:emit(ctx.body, Ir.Indirect(S.list(results), value.expr, S.list(operands)))
                if #sig.results == 0 then return k(machine, V.unit()) end
                if #sig.results == 1 then
                    return k(machine, V.runtime(ctx.builder:ref(results[1], sig.results[1]), sig.results[1]))
                end
                local out = {}
                for position, resultTy in ipairs(sig.results) do
                    out[position] = V.runtime(ctx.builder:ref(results[position], resultTy), resultTy)
                end
                return k(machine, V.results(out))
            end
            local input = sig.inputs[index]
            if input.kind ~= "InValue" then
                D.todo("view-input", "Only by-value callable inputs are supported", span)
            end
            self:requireType(args[index], input.type, span)
            return self:expressionCPS(machine, ctx, args[index], nil, function(m, expr)
                operands[#operands + 1] = Ir.ValueArg(expr)
                return operand(index + 1)
            end)
        end
        return operand(1)
    end
    if (tag == "runtime" or tag == "variant") and ty and ty:isTagged() then
        -- A call on a tagged callable: test the tag, then run that arm's code directly. Every arm
        -- shares the one visible signature, so the results join through a slot per result.
        if not ctx.residual then
            D.reject("runtime-in-normalization", "A tagged call needs runtime code", span)
        end
        local function withExpr(m, expr)
            if expr.kind ~= "Ref" then D.bug("tagged-call", "A tagged callable must be an SSA value") end
            local variantId = expr.value
            local builder = ctx.builder
            local results = ty.visible.results
            local slots = {}
            for index = 1, #results do slots[index] = builder:var(ctx.body, results[index], nil) end
            local pieces = {}
            local function armAt(index, names)
                if not names then names = S.casesOf(ty) end
                if index > #names then
                    -- Every arm's statements are in place, so the tag tests can be layered innermost
                    -- first, and the joined slots are read after them.
                    local pending = {}
                    for _, piece in ipairs(pieces) do
                        if not piece.terminated then
                            local values = self:expand(piece.value)
                            if #values ~= #results then
                                D.bug("tagged-arity", "A tagged arm returned the wrong number of results")
                            end
                            for position, item in ipairs(values) do
                                pending[#pending + 1] = { piece = piece, position = position, value = item }
                            end
                        end
                    end
                    local function store(position)
                        if position > #pending then
                            local child = pieces[#pieces].list
                            for position2 = #pieces - 1, 1, -1 do
                                local piece = pieces[position2]
                                local parent = {}
                                local id = builder:valueId()
                                builder:emit(parent, Ir.VariantMatches(id, variantId, ty, piece.name))
                                builder:emit(parent, Ir.If(builder:ref(id, S.bool), S.list(piece.list),
                                    S.list(child)))
                                child = parent
                            end
                            for _, stmt in ipairs(child) do ctx.body[#ctx.body + 1] = stmt end
                            local out = {}
                            for index2, resultTy in ipairs(results) do
                                local place = Ir.Local(slots[index2])
                                out[index2] = V.runtime(builder:ref(builder:read(ctx.body, resultTy, place),
                                    resultTy), resultTy)
                            end
                            if #out == 0 then return k(m, V.unit()) end
                            if #out == 1 then return k(m, out[1]) end
                            return k(m, V.results(out))
                        end
                        local item = pending[position]
                        return self:expressionCPS(m, item.piece.ctx, item.value, results[item.position],
                            function(m2, ir)
                                builder:store(item.piece.list, Ir.Local(slots[item.position]), ir)
                                return store(position + 1)
                            end)
                    end
                    return store(1)
                end
                local name = names[index]
                local arm = {}
                local armCtx = ctx:arm(arm)
                return self:callTaggedArmCPS(machine, armCtx, name, variantId, ty, args, span,
                    function(m2, result)
                        pieces[#pieces + 1] = { name = name, list = arm, ctx = armCtx, value = result,
                            terminated = armCtx.terminated }
                        return armAt(index + 1, names)
                    end)
            end
            return armAt(1)
        end
        local expr = value.expr
        if expr ~= nil then return withExpr(machine, expr) end
        -- A tagged value built in this expression has not been emitted yet.
        return self:expressionCPS(machine, ctx, value, ty, withExpr)
    end
    D.reject("callable-required", "Only words, methods and closures can be applied", span)
end
-- Evaluating a capture-free closure with known arguments produces a value, not a call.

-- Compile-time execution of a closure body over concrete arguments.
function Eval:evaluateClosureStaticallyCPS(machine, plan, args, span, k)
    local sc = scope(plan.def.lexical)
    for _, name in ipairs(plan.borrowedOrder) do
        local borrowed = plan.borrowed[name]
        if not borrowed.record then
            D.bug("borrowed-capture", "A statically evaluated closure must borrow a concrete record")
        end
        -- The receiver belongs to the enclosing activation, so a reference to it is an enclosing
        -- owner rather than a local of this body. The flag is set on a copy: the captured value is
        -- shared and must stay as it is everywhere else.
        local held = borrowed.record
        if V.tag(held) == "record" and not held.enclosing then
            held = V.record(held.ty, held.fields, held.schema)
            held.enclosing = true
        end
        local value = borrowed.kind == "method" and V.method(borrowed.method, held) or held
        declare(sc, name, { kind = "value", name = name, value = value }, span)
    end
    for name, value in pairs(plan.static) do
        declare(sc, name, { kind = "value", name = name, value = value }, span)
    end
    for index, param in ipairs(plan.def.params) do
        local value = self:copyArgument(args[index])
        self:requireAgainst(value, plan.paramTypes[index], param.span)
        declare(sc, param.name.text, { kind = "value", name = param.name.text, value = value }, param.span)
    end
    return self:execBodyCPS(machine, self:staticFrame(sc, span), plan.def.body, span,
        function(m, result)
            if #result == 0 then return k(m, V.unit()) end
            if #result == 1 then return k(m, result[1]) end
            return k(m, V.results(result))
        end)
end

-- Closures ------------------------------------------------------------------------------------
--
-- A closure is a lambda definition plus captured bindings. Captures that are static become part of
-- the code identity; the rest form a by-value environment that is passed to the compiled lambda as
-- leading hidden inputs. Because the environment type carries the code key, an IR value of that
-- type is directly callable: no function pointer is needed while the code is known.

local function envFieldName(index) return string.format("c%02d", index) end

-- Materialises the value a free name refers to at closure-creation time.

-- The value a closure captures by name. A binding is demanded if it has never been computed.
function Eval:captureValueCPS(machine, ctx, name, span, k)
    local slot = lookup(ctx.scope, name)
    if not slot then D.reject("unknown-name", "Unknown captured name: " .. name, span) end
    if slot.kind == "value" then
        return self:demandCPS(machine, slot, span, function(m, demanded)
            return k(m, demanded.value or V.unit())
        end)
    end
    if slot.kind == "concrete-field" then
        return k(machine, slot.record.fields[slot.name] or V.unit())
    end
    if slot.kind == "field" or slot.kind == "param" then
        if not ctx.residual then
            D.reject("runtime-in-normalization", "Cannot capture runtime storage " .. name, span)
        end
        -- Reading a field captures its value; the field path must not be flattened to the root.
        local place = slot.kind == "field" and slot.place or Ir.Local(slot.storage)
        local read = ctx.builder:read(ctx.body, slot.ty, place)
        return k(machine, V.runtime(ctx.builder:ref(read, slot.ty), slot.ty))
    end
    if slot.kind == "word" then return k(machine, V.word(slot.def, {}, span)) end
    D.bug("capture", "Unknown capture binding kind " .. tostring(slot.kind))
end
-- A first-class lambda needs a checked callable type. Immediate static use can instead consume
-- the prepared captures/parameters directly, without first constructing an unused residual ABI.
function Eval:evalLambdaCPS(machine, ctx, expr, expected, k)
    return self:prepareLambdaCPS(machine, ctx, expr, expected, function(m, plan)
        return self:completeLambdaCPS(m, plan, expr.span, k)
    end)
end

function Eval:completeLambdaCPS(machine, plan, span, k)
    self.plans[plan.key] = plan
    return self:callableInstanceCPS(machine, { plan = plan }, {}, span, function(m, base)
        plan.sig = S.sig(plan.inputs, base.results)
        plan.ty = S.owned(plan.key, plan.sig, plan.envTy)
        return k(m, V.closure(plan))
    end)
end

-- A prepared plan is compiler data, NOT an untyped source closure or a provisional result. If the
-- use is partial, residual or borrows storage, finish the ordinary callable and use normal supply.
-- Arguments are already evaluated and are never replayed by that fallback.
function Eval:invokePreparedLambdaCPS(machine, ctx, plan, args, span, k)
    local concrete = not ctx.residual and #args == #plan.def.params
        and #plan.runtimeOrder == 0 and #plan.borrowedOrder == 0
    for _, value in ipairs(args) do
        local tag = V.tag(value)
        -- Keep aggregates, references and callable requirements on the checked-base path for now.
        -- Known contents alone are not proof of value-copy/lifetime or callable-interface safety.
        local atom = tag == "int" or tag == "float" or tag == "bool" or tag == "unit" or tag == "string"
        concrete = concrete and atom
    end
    if concrete then
        return self:invokeClosureCPS(machine, ctx, plan, nil, args, span, nil, k)
    end
    return self:completeLambdaCPS(machine, plan, span, function(m, value)
        return self:supplyCPS(m, ctx, value, args, span, k)
    end)
end

-- Prepare in written order: capture snapshots/borrows, then parameter annotations. No body is
-- executed and no result signature is claimed until invocation or completeLambdaCPS demands it.
function Eval:prepareLambdaCPS(machine, ctx, expr, expected, k)
    local order = Resolve.captures(expr)

    local plan = { def = self:define(expr, moduleTop(ctx.scope), nil, "|lambda|"), order = order,
        static = {},
        runtime = {}, runtimeOrder = {}, captures = order }
    plan.def.lambda = true
    plan.borrowed, plan.borrowedOrder = {}, {}
    local function capture(index)
        if index > #order then
            local inputs = {}
            -- Declared before the driver that calls it: a local declared later is not in scope for a
            -- closure created earlier, and the call would silently become a global one.
            local afterParameters
            afterParameters = function(inputs)
                -- Resolved parameter types travel with the plan: a contextually typed lambda has no annotation
                -- to re-evaluate when its body is compiled.
                plan.paramTypes = {}
                for position, input in ipairs(inputs) do plan.paramTypes[position] = input.type end
                plan.inputs = S.list(inputs)
                plan.envNames = {}
                local envFields = {}
                for position, name in ipairs(plan.runtimeOrder) do
                    plan.envNames[position] = envFieldName(position)
                    envFields[envFieldName(position)] = plan.runtime[name].ty
                end
                plan.envTy = #plan.runtimeOrder > 0 and S.record(envFields) or S.unit
                plan.key = "closure:" .. tostring(plan.def.id)
                for _, name in ipairs(order) do
                    local static, borrowed = plan.static[name], plan.borrowed[name]
                    if borrowed then
                        -- A record borrow is keyed by its schema identity; an array borrow has no schema, so its
                        -- type is the identity.
                        local shape = tostring(borrowed.kind) .. ":"
                            .. (borrowed.schema and tostring(borrowed.schema.id) or S.encode(borrowed.ty))
                        if borrowed.method then shape = shape .. ":" .. tostring(borrowed.method.id) end
                        plan.key = plan.key .. "|" .. name .. "=@" .. shape
                    else
                        plan.key = plan.key .. (static and ("|" .. name .. "=" .. (V.encode(static) or "?"))
                            or ("|" .. name .. "=#"))
                    end
                end
                return k(machine, plan)
            end
            local function parameter(position)
                if position > #expr.params then
                    return afterParameters(inputs)
                end
                local param = expr.params[position]
                if not param.annotation then
                    -- Contextual typing: the expected signature supplies the missing annotation.
                    if expected == nil then
                        D.todo("lambda-annotation",
                            "A lambda parameter without a type annotation needs an expected signature; either "
                            .. "annotate it or pass the lambda where a signature is required", param.span)
                    end
                    if #expr.params > #expected.inputs then
                        D.reject("callable-shape", "The lambda takes more parameters than its expected signature",
                            expr.span)
                    end
                    local input = expected.inputs[position]
                    if input.kind ~= "InValue" then
                        D.todo("lambda-annotation", "A lambda parameter cannot be a borrowed place", param.span)
                    end
                    inputs[position] = input
                    return parameter(position + 1)
                end
                return self:typeOfCPS(machine, param.annotation, ctx.scope, expr.span, function(m, ty)
                    inputs[position] = S.inValue(ty)
                    return parameter(position + 1)
                end)
            end
            return parameter(1)
        end
        local name = order[index]
        return self:captureValueCPS(machine, ctx, name, expr.span, function(m, value)
        local tag = V.tag(value)
        if V.isStatic(value) then
            if V.isInteger(value) or tag == "float" then value = self:copyArgument(value) end
            plan.static[name] = value
            return capture(index + 1)
        end
        if not (tag == "object" or tag == "method" or tag == "record" or tag == "array") then
            if tag == "closure" then
                -- A nested borrowed closure would need a place for a callable environment.
                D.reject("borrow-escape",
                    "Capturing a borrowed closure needs a callable environment, which is not supported; "
                    .. "capture its receiver instead", expr.span)
            end
            if not ctx.residual then
                D.reject("runtime-in-normalization", "This closure captures runtime value " .. name,
                    expr.span)
            end
            plan.runtimeOrder[#plan.runtimeOrder + 1] = name
            plan.runtime[name] = value
            return capture(index + 1)
        end
        -- A mutable instance or a method view is borrowed, never copied: the closure is tied to
            -- the activation that created it. In residual code the place travels as a place input;
            -- under the interpreter a concrete aggregate is simply referred to. An array is a mutable
            -- instance too, so it borrows like a record rather than travelling by value.
            local object = tag == "method" and value.receiver or value
            if not object then
                D.reject("missing-receiver", "A captured method needs its receiver", expr.span)
            end
            -- A borrow needs an address, so a value still carrying its construction expression
            -- materialises here. The closure is then non-retaining, and returning it escapes.
            local function withPlace(m2, place)
                plan.borrowedOrder[#plan.borrowedOrder + 1] = name
                if object.ty:isArray() then
                    plan.borrowed[name] = { kind = "array", ty = object.ty, place = place,
                        record = place == nil and object or nil }
                else
                    local schema = object.schema
                    plan.borrowed[name] = {
                        kind = tag == "method" and "method" or "object",
                        ty = object.ty, schema = schema or { id = 0, fields = S.fieldsOf(object.ty),
                            fieldNames = S.fieldNames(object.ty), statics = {}, readonly = {}, methods = {} },
                        place = place, record = place == nil and object or nil,
                        method = tag == "method" and value.def or nil,
                    }
                end
                if ctx.residual and not place then
                    D.reject("runtime-in-normalization", "Cannot capture runtime storage " .. name,
                        expr.span)
                end
                return capture(index + 1)
            end
            if not ctx.residual then return withPlace(m, object.place) end
            if object.ty:isArray() then
                return self:arrayPlaceCPS(m, ctx, object, expr.span, withPlace)
            end
            return self:recordPlaceCPS(m, ctx, object, expr.span, withPlace)
        end)
    end
    return capture(1)
end

-- Resolves the plan behind an Owned type, which is how a returned or passed closure is called.
function Eval:planOf(ty, span)
    local plan = self.plans and self.plans[ty.entry]
    if not plan then
        D.todo("opaque-callable",
            "A callable value whose code is not known in this compilation needs a function-pointer ABI, "
            .. "which is not implemented", span)
    end
    return plan
end

-- The instance key adds the call's static arguments to the closure's code identity.
function Eval:callableKey(plan, args)
    local parts = { plan.key }
    for index = 1, #plan.def.params do
        local value = args[index]
        if value ~= nil and V.isStatic(value) then
            local encoded = V.encode(value)
            if not encoded then D.bug("callable-key", "A static callable argument has no encoding") end
            parts[#parts + 1] = encoded
        else
            -- Matches instanceKey: unsupplied and ordinary runtime arguments agree, while a
            -- runtime callable is distinguished by its code identity.
            local ty = value and value.ty
            parts[#parts + 1] = (ty and ty:isOwned()) and ("!" .. ty.entry) or "*"
        end
    end
    return table.concat(parts, "/")
end

-- The environment arguments, in the order the lambda instance expects: by-value captures first,
-- then borrowed places.
function Eval:closureEnvironment(plan, envExprs)
    local entries = {}
    for _, name in ipairs(plan.runtimeOrder) do
        if envExprs then
            entries[#entries + 1] = { kind = "value", expr = envExprs[name] or envExprs[#entries + 1] }
        else
            entries[#entries + 1] = { kind = "value", value = plan.runtime[name] }
        end
    end
    for _, name in ipairs(plan.borrowedOrder) do
        entries[#entries + 1] = { kind = "place", place = plan.borrowed[name].place }
    end
    return entries
end

-- Environment arguments precede the declared parameters for the compiled lambda.
function Eval:callClosureCPS(machine, ctx, callable, args, span, k)
    return self:callableInstanceCPS(machine, callable, args, span, function(m, instance)
        if instance.status == "building" and not instance.results then
            D.reject("recursive-result", "Recursive closure needs an explicit result annotation", span)
        end
        return self:emitCallableCallCPS(m, ctx, instance, callable.env, args, span, k)
    end)
end

-- A call through a known callable: the environment arguments come first, then the declared parameters
-- in signature order.
-- A call through a known callable: the environment arguments come first, then the declared parameters
-- in signature order. Three local drivers -- environment, parameters, answer -- keep every step a tail
-- call, so a call costs no host frames of its own.
function Eval:emitCallableCallCPS(machine, ctx, instance, envArgs, args, span, k)
    local builder = ctx.builder
    local operands = {}
    local function answer()
        local runtime = instance.runtimeResults or self:runtimeResults(instance.results)
        local results = {}
        for _ = 1, #runtime do results[#results + 1] = builder:valueId() end
        builder:emit(ctx.body, Ir.Call(S.list(results), instance.target, S.list(operands)))
        local ir = {}
        for index, ty in ipairs(runtime) do
            ir[index] = V.runtime(builder:ref(results[index], ty), ty)
        end
        local out = self:logicalResults(instance.results, ir)
        if #out == 0 then return k(machine, V.unit()) end
        if #out == 1 then return k(machine, out[1]) end
        return k(machine, V.results(out))
    end
    local function parameters()
        local function parameter(index)
            if index > #instance.paramPositions then return answer() end
            local position = instance.paramPositions[index]
            -- After the environment, the declared parameters follow in signature order.
            return self:expressionCPS(machine, ctx, args[position], instance.inputTypes[#envArgs + index],
                function(m, expr)
                    operands[#operands + 1] = Ir.ValueArg(expr)
                    return parameter(index + 1)
                end)
        end
        return parameter(1)
    end
    local function environment(index)
        if index > #envArgs then return parameters() end
        local arg = envArgs[index]
        if arg.kind == "place" then
            operands[#operands + 1] = Ir.BorrowArg(arg.place)
            return environment(index + 1)
        end
        if arg.expr then
            operands[#operands + 1] = Ir.ValueArg(arg.expr)
            return environment(index + 1)
        end
        return self:expressionCPS(machine, ctx, arg.value, instance.inputTypes[index], function(m, expr)
            operands[#operands + 1] = Ir.ValueArg(expr)
            return environment(index + 1)
        end)
    end
    return environment(1)
end
-- The shim: `callClosureCPS`, `expressionCPS`, `makeViewCPS` and `evalLambdaCPS` reach the converted
-- form directly; this stays for any caller that has not converted.

-- The instance for one closure plan and argument vector, or the one already built for it.
function Eval:callableInstanceCPS(machine, callable, args, span, k)
    local key = self:callableKey(callable.plan, args)
    local existing = self.instances[key]
    if existing then
        if existing.failure then error(existing.failure, 0) end
        return k(machine, existing)
    end
    if self.instanceCount >= (self.limits.keys or 1024) then
        D.resource("keys", "Residual instance budget exhausted", span)
    end
    return self:buildCallableInstanceCPS(machine, key, callable, args, span, k)
end
-- The same shape as `buildInstance`: the failed attempt is remembered here, so a probe that swallows
-- the diagnostic still leaves the session usable.
-- probe that swallows the diagnostic still leaves the session usable.

-- Building a callable instance. The depth is counted on the machine and the attempt runs under a
-- `Build` descriptor: a failure is remembered on the instance and re-raised, which is exactly what the
-- `pcall` pair did, without a host frame per attempt.
function Eval:buildCallableInstanceCPS(machine, key, callable, args, span, k)
    machine:checkDepth("build", span, key)
    -- Building code is not executing it, even when requested during initialization/interpretation.
    local savedRun, savedDemand = self.run, self.demanding
    self.run, self.demanding = false, false
    machine:push("build", span, key, function(_, diagnostic)
        self.run, self.demanding = savedRun, savedDemand
        local instance = self.instances[key]
        if instance then
            instance.failure = diagnostic
            instance.status = "failed"
        end
        error(diagnostic, 0)
    end)
    return self:constructCallableInstanceCPS(machine, key, callable, args, span, function(m, instance)
        machine:pop()
        self.run, self.demanding = savedRun, savedDemand
        return k(m, instance)
    end)
end
function Eval:constructCallableInstanceCPS(machine, key, callable, args, span, k)
    local plan, def = callable.plan, callable.plan.def
    self.nextFn = self.nextFn + 1
    local instance = { key = key, def = def, plan = plan, target = "wordletfn_" .. self.nextFn,
        status = "building", args = args, paramPositions = {}, inputTypes = {} }
    self:registerInstance(instance)

    local body, setup = {}, {}
    local builder = IR.builder()
    local sc = scope(plan.def.lexical)
    local params, paramTypes, inputs = {}, {}, {}

    -- The captured environment arrives first, one input per runtime capture.
    for index, name in ipairs(plan.runtimeOrder) do
        local value = builder:valueId()
        local ty = plan.runtime[name].ty
        params[#params + 1] = Ir.ValueParam(#inputs, value, ty)
        inputs[#inputs + 1] = S.inValue(ty)
        paramTypes[#paramTypes + 1] = ty
        instance.inputTypes[#instance.inputTypes + 1] = ty
        declare(sc, name, { kind = "value", name = name, value = V.runtime(builder:ref(value, ty), ty) }, span)
    end
    for _, name in ipairs(plan.borrowedOrder) do
        local borrowed = plan.borrowed[name]
        local storage = builder:storageId()
        params[#params + 1] = Ir.PlaceParam(#inputs, storage, borrowed.ty)
        inputs[#inputs + 1] = S.inPlace(borrowed.ty)
        paramTypes[#paramTypes + 1] = borrowed.ty
        instance.inputTypes[#instance.inputTypes + 1] = borrowed.ty
        -- The place parameter belongs to the caller, so the object is an enclosing owner here.
        if borrowed.ty:isArray() then
            declare(sc, name, { kind = "value", name = name,
                value = V.array(borrowed.ty, nil, Ir.Local(storage), true) }, span)
        else
            local object = V.object(borrowed.ty, Ir.Local(storage), borrowed.schema, nil, true)
            if borrowed.kind == "method" then
                declare(sc, name, { kind = "value", name = name,
                    value = V.method(borrowed.method, object) }, span)
            else
                declare(sc, name, { kind = "value", name = name, value = object }, span)
            end
        end
    end
    for name, value in pairs(plan.static) do
        declare(sc, name, { kind = "value", name = name, value = value }, span)
    end

    local function afterParameters(m)
        return self:declaredResultCPS(m, def, sc, span, function(m2, declared)
            instance.results = declared
            local ctx = self:residualFrame(sc, span)
            ctx.builder, ctx.body, ctx.fn, ctx.instance = builder, body, { id = instance.target }, instance
            return self:execBodyResidualCPS(m2, ctx, def.body, span, function(m3)
                if not instance.results then instance.results = ctx.resultTypes end
        if not instance.results then D.reject("recursive-result", "Closure has no returning path", span) end
        self:checkResultContract(instance.results, ctx.resultTypes, "Closure", span)
        for _, ty in ipairs(instance.results) do
            if not S.representable(ty) then
                D.todo("static-callable-result",
                    "A closure result that is pure code with no environment has no runtime representation", span)
            end
        end
        local statements = setup
        for _, stmt in ipairs(body) do statements[#statements + 1] = stmt end
        instance.runtimeResults = self:runtimeResults(instance.results)
        instance.fn = Ir.Fn(instance.target, Ir.Body, 0, S.list(inputs), S.list(instance.runtimeResults),
            S.list(params), S.list(statements))
        instance.status = "done"
        return k(m3, instance)
            end)
        end)
    end
    local function parameterAt(index, m)
        if index > #def.params then return afterParameters(m) end
        local param = def.params[index]
        local function withTy(m2, ty)
            local supplied = args[index]
            if supplied and (V.isInteger(supplied) or V.tag(supplied) == "float") then
                supplied = self:copyArgument(supplied)
            end
            local bound = false
            if ty:isSig() then
                -- A callable parameter: static code is specialised away entirely; otherwise the Owned
                -- type carries the code identity, so the call stays direct and only the environment
                -- travels as a by-value input.
                if supplied ~= nil and (V.tag(supplied) == "closure" or V.tag(supplied) == "word") then
                    if self:callableMatches(supplied, ty) == false then
                        D.reject("callable-shape", "Callable does not match the required signature", param.span)
                    end
                    if V.isStatic(supplied) then
                        declare(sc, param.name.text, { kind = "value", name = param.name.text, value = supplied },
                            param.span)
                        bound = true
                    else
                        -- A closure with a runtime environment travels by value as that environment. A
                        -- closure that borrows storage is non-retaining, so the parameter becomes an
                        -- erased view, which the caller binds through a local adapter that holds the
                        -- borrowed places.
                        ty = self:borrowsStorage(supplied) and S.view(ty) or supplied.ty
                    end
                elseif V.tag(supplied) == "method" then
                    -- A method borrows its receiver, so it is non-retaining for the same reason a
                    -- borrowing closure is: the parameter takes a view.
                    ty = S.view(ty)
                elseif supplied ~= nil and V.tag(supplied) == "runtime" and supplied.ty:isOwned() then
                    ty = supplied.ty
                elseif supplied ~= nil and V.tag(supplied) == "runtime" and supplied.ty:isView() then
                    ty = supplied.ty
                elseif supplied == nil then
                    -- An entry face with no call site: the callable arrives from outside, so it needs
                    -- the invocation-pointer ABI rather than a code identity.
                    ty = S.view(ty)
                else
                    D.todo("opaque-callable",
                        "A callable argument with no known code needs a function-pointer ABI", param.span)
                end
            else
                S.checkRuntime(ty, param.span)
            end
            if not bound and ty == S.unit then
                -- A unit parameter carries no information, so it is not a runtime input at all: the
                -- name is bound to the unit value and neither the ABI nor the call site mentions it.
                declare(sc, param.name.text, { kind = "value", name = param.name.text, value = V.unit() }, param.span)
                bound = true
            end
            if not bound then
                if supplied ~= nil and V.isStatic(supplied) then
                    self:requireType(supplied, ty, param.span)
                    declare(sc, param.name.text, { kind = "value", name = param.name.text, value = supplied }, param.span)
                else
                    local value = builder:valueId()
                    params[#params + 1] = Ir.ValueParam(#inputs, value, ty)
                    inputs[#inputs + 1] = S.inValue(ty)
                    paramTypes[#paramTypes + 1] = ty
                    instance.paramPositions[#instance.paramPositions + 1] = index
                    if ty:isRecord() then
                        declare(sc, param.name.text, { kind = "value", name = param.name.text,
                            value = V.object(ty, nil, { fields = S.fieldsOf(ty),
                                fieldNames = S.fieldNames(ty), statics = {}, readonly = {}, methods = {}, type = ty },
                                nil, false, builder:ref(value, ty), setup) },
                            param.span)
                    else
                        declare(sc, param.name.text, { kind = "value", name = param.name.text,
                            value = V.runtime(builder:ref(value, ty), ty) }, param.span)
                    end
                end
            end
            return parameterAt(index + 1, m2)
        end
        -- A contextually typed lambda carries its resolved parameter types on the plan.
        if plan.paramTypes[index] then return withTy(m, plan.paramTypes[index]) end
        return self:requirementCPS(m, def, index, sc, span, withTy)
    end
    return parameterAt(1, machine)
end

-- Bodies --------------------------------------------------------------------------------------

-- A deferred action hands the rest of the list to a nested block over the same context, so every way
-- out of what follows passes through a `return`, which the action is attached to. A second action
-- nests inside the first, which is what makes several of them run in reverse order. The action itself
-- runs at the return rather than here: a return inside a statement conditional's arm is an exit from
-- this block too, and running the action here would miss that path and could only ever produce one
-- value.

-- A deferred action. Its callee and arguments are evaluated where the `defer` is written, and then
-- the rest of the list runs with the action pending on the frame.
function Eval:execDeferCPS(machine, ctx, statements, index, stmt, k)
    return self:deferredCallCPS(machine, ctx, stmt, function(m, pending)
        local frame = { pending = pending, parent = ctx.deferFrame, span = stmt.span }
        ctx.deferFrame = frame
        return self:execBlockCPS(m, ctx, statements, index + 1, function(m2, terminated)
            ctx.deferFrame = frame.parent
            return k(m2, terminated)
        end)
    end)
end

-- Every deferred action pending at a return, innermost first, which is the reverse of the order the
-- `defer` statements were written. Running them here is what makes a transfer out of the block in
-- the middle of a conditional reach them as well.

-- Every deferred action pending at a return, innermost first, which is the reverse of the order the
-- `defer` statements were written. Each action is a supply step, so walking the frame chain is a
-- continuation rather than a loop.
function Eval:runPendingDefersCPS(machine, ctx, k)
    local frame = ctx.deferFrame
    local function runNext(m)
        if not frame then return k(m) end
        local current = frame
        frame = frame.parent
        -- `supply` is still direct (it converts with the rest of the spine), so its answer is
        -- discarded here; the walk to the next frame is the tail call.
        return self:supplyCPS(m, ctx, current.pending.callee, current.pending.args,
            current.pending.span, function(m2) return runNext(m2) end)
    end
    return runNext(machine)
end

-- The callee and the arguments of a deferred action are evaluated where the `defer` is written, so a
-- read of mutable storage there is a snapshot of what the program had rather than of what the names
-- mean later.

-- The callee and the arguments of a deferred action, both evaluated where the `defer` is written so a
-- read of mutable storage there is a snapshot rather than what the names mean later.
function Eval:deferredCallCPS(machine, ctx, stmt, k)
    return self:evalExprCPS(machine, ctx, stmt.call.callee, function(m, callee)
        return self:evalArgumentsCPS(m, ctx, stmt.call.arguments, callee, function(m2, args)
            return k(m2, { callee = callee, args = args, span = stmt.call.span })
        end)
    end)
end



-- A statement list. The walk is a continuation over the remaining statements, so a block costs one
-- frame however many statements it has, and the answer is whether control left the list (a `return`, or
-- a back edge a returned expression took). `from` lets a `defer` hand the rest of a list to a nested
-- block over the same context.
function Eval:execBlockCPS(machine, ctx, statements, from, k)
    -- A statement list is not a tail position; only a `return` inside it is, and it sets the flag.
    ctx.tail = false
    local function statement(index)
        if index > #statements then return k(machine, false) end
        local stmt = statements[index]
        self:step(stmt.span)
        local kind = stmt.kind
        if kind == "Defer" then
            return self:execDeferCPS(machine, ctx, statements, index, stmt, k)
        end
        if kind == "ValueStmt" then
            return self:evalValueDefCPS(machine, ctx, stmt.def, function(m, bound)
                local values = self:expand(bound)
                for position, binder in ipairs(stmt.def.binders) do
                    declare(ctx.scope, binder.name.text,
                        { kind = "value", name = binder.name.text, value = values[position] or V.unit() },
                        binder.span)
                end
                return statement(index + 1)
            end)
        elseif kind == "WordStmt" then
            local def = self:define(stmt.def, ctx.scope, nil)
            declare(ctx.scope, stmt.def.name.text, { kind = "word", name = stmt.def.name.text, def = def }, stmt.def.name.span)
        elseif kind == "ReturnStmt" then
            -- A signature result annotation types a returned lambda. Only a single returned value
            -- can be a tail self-call: in a result vector the non-final values are adjusted to one
            -- value each and are not tail positions.
            local savedExpected, savedTail, savedTerminated = ctx.expectedResult, ctx.tail, ctx.terminated
            if #stmt.values ~= 1 then ctx.expectedResult = nil end
            ctx.tail, ctx.terminated = #stmt.values == 1, false
            return self:evalListCPS(machine, ctx, stmt.values, function(m, values)
                ctx.expectedResult, ctx.tail = savedExpected, savedTail
                self:checkReturn(values, stmt.span)
                if ctx.terminated then return k(m, true) end
                ctx.terminated = savedTerminated
                if ctx.residual then
                    return self:materializeAllCPS(m, ctx, values,
                        ctx.instance and ctx.instance.results or nil, function(m2, exprs)
                            ctx.resultTypes = {}
                            for position, value in ipairs(values) do
                                ctx.resultTypes[position] = value.ty
                            end
                            -- The action runs after the returned expression has been evaluated and before
                            -- the value leaves. `materializeAll` above is what takes the snapshot the
                            -- returned value names, so a read of storage the action changes still yields
                            -- what it was at the return.
                            return self:runPendingDefersCPS(m2, ctx, function(m3)
                                ctx.builder:emit(ctx.body, Ir.Return(S.list(exprs)))
                                return k(m3, true)
                            end)
                        end)
                end
                -- The interpreter executes the program rather than compiling it, so the actions run as
                -- ordinary calls on the way out of the block.
                return self:runPendingDefersCPS(m, ctx, function(m2)
                    ctx.result = values
                    return k(m2, true)
                end)
            end)
        elseif kind == "IfStmt" then
            return self:execIfStatementCPS(machine, ctx, stmt, function(m, returned)
                if returned then return k(m, true) end
                return statement(index + 1)
            end)
        elseif kind == "CallStmt" then
            -- A statement call is not a position for its value, so it is discarded and the walk goes on.
            return self:evalApplyCPS(machine, ctx, stmt.call, function(m)
                return statement(index + 1)
            end)
        elseif kind == "StoreStmt" then
            return self:execStoreCPS(machine, ctx, stmt, function(m)
                return statement(index + 1)
            end)
        else
            D.todo("statement", "Unsupported statement form: " .. tostring(kind), stmt.span)
        end
        return statement(index + 1)
    end
    return statement(from or 1)
end

-- A value list as an IR expression list. A unit slot is logical but has no runtime representation,
-- exactly as a unit parameter has none, so it is dropped here and the IR result list is the erased one.
-- A value list as an IR expression list. A unit slot is logical but has no runtime representation,
-- exactly as a unit parameter has none, so it is dropped here and the IR result list is the erased one.
function Eval:materializeAllCPS(machine, ctx, values, wants, k)
    local out = {}
    local function item(index)
        if index > #values then return k(machine, out) end
        local value = values[index]
        if value.ty == S.unit then return item(index + 1) end
        return self:expressionCPS(machine, ctx, value, wants and wants[index] or nil, function(m, expr)
            out[#out + 1] = expr
            return item(index + 1)
        end)
    end
    return item(1)
end
-- A unit slot erases from a result vector the way it erases from a parameter list (syntax.md §6).
-- The function's IR results are the non-unit ones; a call site reinserts the unit values so a
-- binding list keeps its positions, while a return simply drops them.
function Eval:runtimeResults(results)
    local out = {}
    for _, ty in ipairs(results or {}) do if ty ~= S.unit then out[#out + 1] = ty end end
    return out
end

function Eval:logicalResults(results, runtime)
    local out, index = {}, 1
    for _, ty in ipairs(results or {}) do
        if ty == S.unit then out[#out + 1] = V.unit()
        else out[#out + 1] = runtime[index]; index = index + 1 end
    end
    return out
end

-- The declared result contract against the result vector a body actually returned. The contract is
-- exact (`syntax.md` §6): a return vector is neither widened to satisfy it nor padded, so a `unit`
-- slot counts as a logical slot even though C erases its payload, and a `u8` where `u32` is declared
-- rejects rather than widening. This runs after the body walk because the declared vector and the
-- actual one are only both known then -- and it must run at all, because without it the mismatch
-- reaches the IR checker, which reports a source mistake as an internal bug.
--
-- A slot the declaration left open (`false`) is filled from the body just before this, so it compares
-- equal and is skipped. A body that never returned has its own diagnostic (`no-return`).
function Eval:checkResultContract(declared, actual, subject, span)
    if not declared or actual == nil then return end
    if #declared ~= #actual then
        D.reject("result-count", subject .. " declares " .. #declared .. " result"
            .. (#declared == 1 and "" or "s") .. " but returns " .. #actual, span)
    end
    for index, want in ipairs(declared) do
        local got = actual[index]
        if want ~= false and got and want ~= got then
            D.reject("type-mismatch", "Result " .. index .. " of " .. subject .. " is declared "
                .. S.display(want) .. " but found " .. S.display(got), span)
        end
    end
end

-- A statement conditional. A known test runs one arm; an opaque one runs both arms into their own
-- statement lists and emits one `If`. The answer is whether both arms returned, which is what lets the
-- block that contains this stop looking for the end of its list.
-- A statement conditional. A known test runs one arm; an opaque one runs both arms into their own
-- statement lists and emits one `If`. The answer is whether both arms returned, which is what lets the
-- block that contains this stop looking for the end of its list.
function Eval:execIfStatementCPS(machine, ctx, stmt, k)
    return self:evalExprCPS(machine, ctx, stmt.test, function(m, test)
        self:requireType(test, S.bool, stmt.test.span)
        if V.tag(test) == "bool" then
            return self:execBlockCPS(m, ctx, test.b and stmt.yes or stmt.no, nil, k)
        end
        return self:expressionCPS(m, ctx, test, nil, function(m2, testExpr)
            local yesList, noList = {}, {}
            return self:execBlockCPS(m2, ctx:arm(yesList), stmt.yes, nil, function(m3, yesReturned)
                return self:execBlockCPS(m3, ctx:arm(noList), stmt.no, nil, function(m4, noReturned)
                    if #yesList > 0 or #noList > 0 then
                        ctx.builder:emit(ctx.body, Ir.If(testExpr, S.list(yesList), S.list(noList)))
                    end
                    return k(m4, yesReturned and noReturned)
                end)
            end)
        end)
    end)
end
-- Value definitions and annotations -----------------------------------------------------------

-- The shim for the callers that reach this by name or through a `pcall` (`demand` does, which a
-- grep for `self:evalValueDef(` misses because it is written `self.evalValueDef`). One boundary.

-- A value definition. The annotations resolve first, because they are what types an unannotated
-- lambda or an empty array literal; then each value is evaluated with its expectation; then each
-- binder is checked. No child here is recursive, so nothing nests and every answer goes straight back
-- through `k`. The caller enters it through the machine's driver.
-- A value definition. The annotations resolve first, because they are what types an unannotated
-- lambda, and then the values are evaluated in written order; the binders are checked once all of them
-- are in. Both walks are local drivers, so neither costs host frames.
function Eval:evalValueDefCPS(machine, ctx, def, k)
    local expectations = {}
    local function annotation(index)
        if index > #def.binders then
            local values = {}
            local function value(position)
                if position > #def.values then
                    local bound = {}
                    local function binderAt(binderIndex)
                        if binderIndex > #def.binders then
                            if #bound == 1 then return k(machine, bound[1]) end
                            return k(machine, V.results(bound))
                        end
                        local binder = def.binders[binderIndex]
                        return self:checkAnnotationCPS(machine, ctx, binder,
                            values[binderIndex] or V.unit(), function(m, checked)
                                bound[binderIndex] = checked
                                return binderAt(binderIndex + 1)
                            end)
                    end
                    return binderAt(1)
                end
                return self:evalExpectedCPS(machine, ctx, def.values[position], expectations[position],
                    function(m, produced)
                        if position < #def.values then
                            values[#values + 1] = self:first(produced)
                        else
                            for _, item in ipairs(self:expand(produced)) do values[#values + 1] = item end
                        end
                        return value(position + 1)
                    end)
            end
            return value(1)
        end
        local binder = def.binders[index]
        if not binder.annotation then return annotation(index + 1) end
        return self:typeOfCPS(machine, binder.annotation, ctx.scope, binder.span, function(m, ty)
            -- A signature annotation types an unannotated lambda; any other annotation is what an
            -- array literal with no elements of its own has to take its type from.
            if ty:isSig() or ty:isArray() then expectations[index] = ty end
            return annotation(index + 1)
        end)
    end
    return annotation(1)
end

-- A binder's annotation, checked against the value bound to it.
function Eval:checkAnnotationCPS(machine, ctx, binder, value, k)
    if not binder.annotation then return k(machine, value) end
    return self:typeOfCPS(machine, binder.annotation, ctx.scope, binder.span, function(m, ty)
        self:requireAgainst(value, ty, binder.span)
        return k(m, value)
    end)
end
-- A type expression is a type value or a schema (which denotes its record type).
function Eval:asType(value, span)
    if V.tag(value) == "type" then return value.value end
    if V.tag(value) == "schema" then return value.def.type end
    return nil
end

-- The type an expression denotes, computed in a static frame so that naming a type is not an
-- evaluation of a value. The name being computed right now is the recursion knot: its cell comes back
-- rather than its layout being demanded.
function Eval:typeOfCPS(machine, expr, sc, span, k)
    if expr.kind == "Reference" then
        local slot = lookup(sc, expr.name.text)
        if slot and slot.open and slot.cell and self:isTypeDefinition(slot) then
            self.types.referenced[slot.cell] = true
            return k(machine, S.named(slot.cell))
        end
    end
    return self:evalExprCPS(machine, self:staticFrame(sc, span), expr, function(m, value)
        local ty = self:asType(value, span)
        if not ty then D.reject("type-required", "Expected a type", expr.span) end
        return k(m, ty)
    end)
end

-- The declared type of one parameter, which is what a call requirement reports.
function Eval:requirementCPS(machine, def, index, sc, span, k)
    local param = def.params[index]
    if not param.annotation then
        D.reject("type-required", "Parameter " .. param.name.text .. " needs a type annotation", param.span)
    end
    return self:typeOfCPS(machine, param.annotation, sc, param.span, k)
end
-- Integer arithmetic -------------------------------------------------------------------------------
-- One implementation of the per-width rules, shared by the interpreter and by the builder when it
-- folds constants. Wrapping is masked at the type's own width, so a narrower integer wraps the way
-- u32 wraps at 32 bits.

local U32Kernel = require("wordletkit.u32")

-- Wrapping is a modulus rather than a bit mask: Lua's bit operations are signed 32-bit, so masking a
-- value at or above 2^31 would turn it negative. A signed width maps the wrapped value back into its
-- own range, which is what makes two's complement wrap around.
function wrap(ty, n)
    local wrapped = n % S.modulusOf(ty)
    if ty:isSigned() and wrapped > S.maxOf(ty) then wrapped = wrapped - S.modulusOf(ty) end
    return wrapped
end

-- A signed divisor is truncated toward zero, and the remainder takes the dividend's sign, so that
-- `/%` on signed values matches C. The one case C leaves undefined is defined here: the most
-- negative value divided by -1 wraps to itself.
function truncDiv(a, b)
    local quotient = a / b
    if quotient < 0 then quotient = math.ceil(quotient) else quotient = math.floor(quotient) end
    return quotient
end

function signedDiv(ty, x, y)
    if y == 0 then return nil end
    if y == -1 then return wrap(ty, -x) end
    return truncDiv(x, y)
end

function signedRem(ty, x, y)
    if y == 0 then return nil end
    if y == -1 then return 0 end
    return x - truncDiv(x, y) * y
end

-- A product exceeds what a Lua number holds exactly at 32 bits, so that width goes through the exact
-- kernel; every narrower width fits exactly either way. A power needs the same exactness and has its
-- own function, because its intermediate squares are products too.
function mulExact(ty, x, y)
    if ty == S.u32 then return U32Kernel.mul(x, y) end
    return wrap(ty, x * y)
end

function pow(ty, base, exponent)
    if ty == S.u32 then return U32Kernel.pow(base, exponent) end
    if ty == S.i32 then
        -- A signed power wraps at 32 bits exactly as an unsigned one does, so the exact kernel does
        -- the arithmetic on the two's complement words and the result is mapped back into range.
        -- Doing it here would multiply values whose product exceeds what a Lua number holds.
        return wrap(ty, U32Kernel.pow(base % 4294967296, exponent))
    end
    local result, b, e = 1, base, exponent
    while e > 0 do
        if e % 2 == 1 then result = wrap(ty, result * b) end
        e = math.floor(e / 2)
        if e > 0 then b = wrap(ty, b * b) end
    end
    return result
end

-- Application ---------------------------------------------------------------------------------

-- Argument expectations come from parameters whose annotation is written as a signature, so an
-- unannotated lambda argument is typed by the requirement it is passed to.

-- The argument vector. Every step here is direct except the final answer, because `evalExpected` is
-- not on the machine yet; the walk over the arguments is iterative, so it costs one frame whatever the
-- arity. A builtin parameter that names a type resolves on the type path and declares into the callee's
-- scope as it goes.
-- The argument vector. Every argument is a step, and a builtin parameter that names a type resolves
-- on the type path and declares into the callee's scope as it goes.
function Eval:evalArgumentsCPS(machine, ctx, exprs, callee, k, prepared)
    local def, offset
    local tag = V.tag(callee)
    local resolved = prepared or (tag == "closure" and callee.plan or nil)
    if prepared then
        def, offset = prepared.def, 0
    elseif tag == "word" then
        def = callee.def
        offset = #callee.args
    elseif tag == "closure" then
        def = callee.plan.def
        offset = #(callee.bound or {})
    elseif tag == "method" then
        def = callee.def
        offset = #(callee.args or {})
    end
    local sc = (def and (offset == 0 or resolved)) and scope(def.lexical) or nil
    local values = {}
    local function argument(index)
        if index > #exprs then return k(machine, values) end
        local expr = exprs[index]
        local param = sc and def.params[index + offset] or nil
        if param and param.isType then
            -- A builtin parameter that names a type is resolved on the type path, which is the path
            -- that hands back the cell an open definition reserved instead of demanding its layout.
            -- That is what lets `array(Node, 2)` inside Node's own definition reach the cycle checker
            -- rather than being refused as an eager initializer.
            return self:typeOfCPS(machine, expr, sc, expr.span, function(m, ty)
                local held = V.type(ty)
                values[#values + 1] = held
                if param.name and param.name.text then
                    declare(sc, param.name.text, { kind = "value", name = param.name.text, value = held },
                        param.span)
                end
                return argument(index + 1)
            end)
        end
        local function withExpected(expected)
            return self:evalExpectedCPS(machine, ctx, expr, expected, function(m, value)
                if index < #exprs then
                    local adjusted = self:first(value)
                    values[#values + 1] = adjusted
                    if param and param.name and param.name.text then
                        declare(sc, param.name.text, { kind = "value", name = param.name.text,
                            value = adjusted }, param.span)
                    end
                else
                    for _, item in ipairs(self:expand(value)) do values[#values + 1] = item end
                end
                return argument(index + 1)
            end)
        end
        -- The requirement decides, not how it was spelled: an alias of a signature is a signature,
        -- so a lambda passed to `f: Endo` gets its parameter type from it just as one passed to a
        -- written `(u32): u32` does. Only a signature is used this way, as that is what types a
        -- lambda.
        if resolved and param then
            local ty = resolved.paramTypes[index + offset]
            return withExpected(ty:isSig() and ty or nil)
        end
        if not (param and param.annotation) then return withExpected(nil) end
        return self:typeOfCPS(machine, param.annotation, sc, param.span, function(m, ty)
            return withExpected(ty:isSig() and ty or nil)
        end)
    end
    return argument(1)
end
-- `u8(x)`, `u16(x)` and `u32(x)` convert between integer widths: widening is free, narrowing traps
-- when the value does not fit, and a known value outside the target is rejected while compiling.
-- An integer becomes the nearest double, rounding once with ties to even. The exact kernel does the
-- rounding, because a Lua division would round twice for a value above 2^53.

-- An integer to f64: known values round here, a runtime one converts in code.
function Eval:roundToFloatCPS(machine, ctx, value, span, k)
    local from = value.ty
    if V.isKnown(value) then
        local high, low = wordsOf(value)
        if from:isWide() and from:isSigned() and U64Kernel.slt(high, low, 0, 0) then
            return k(machine, V.f64(-U64Kernel.tofloat(U64Kernel.neg(high, low))))
        end
        if from:isWide() then return k(machine, V.f64(U64Kernel.tofloat(high, low))) end
        return k(machine, V.f64(value.n))
    end
    return self:expressionCPS(machine, ctx, value, nil, function(m, expr)
        return k(m, V.runtime(ctx.builder:convert(expr, S.f64), S.f64))
    end)
end

-- A float becomes an integer by truncation toward zero. A value the target cannot hold rejects when it
-- is known and stops a run-time one, which is also what keeps a NaN from becoming some integer: a NaN
-- compares false against every bound, so it is trapped on its own.

-- An f64 to an integer: known values are range-checked here, a runtime one in code.
function Eval:truncateToIntCPS(machine, ctx, ty, value, span, k)
    local maxDouble, minDouble = floatBounds(ty)
    if V.isKnown(value) then
        -- Truncation toward zero, which is what a conversion to an integer means; `math.modf` is
        -- that operation, while a modulo would floor toward negative infinity instead.
        local truncated = math.modf(value.n)
        if truncated ~= truncated or truncated < minDouble or truncated >= maxDouble then
            D.reject("numeric-range", "Value " .. string.format("%.17g", value.n)
                .. " does not fit in " .. S.encode(ty), span)
        end
        if ty:isWide() then return k(machine, V.int64(ty, wordsOfDouble(truncated))) end
        return k(machine, V.int(ty, truncated))
    end
    local builder = ctx.builder
    return self:expressionCPS(machine, ctx, value, nil, function(m, expr)
        builder:emit(ctx.body, Ir.Trap(builder:bin("Ne", expr, expr, S.bool), "numeric-range"))
        builder:emit(ctx.body, Ir.Trap(builder:bin("Lt", expr, builder:float(S.f64, minDouble), S.bool),
            "numeric-range"))
        builder:emit(ctx.body, Ir.Trap(builder:bin("Ge", expr, builder:float(S.f64, maxDouble), S.bool),
            "numeric-range"))
        return k(m, V.runtime(builder:convert(expr, ty), ty))
    end)
end

-- `f64(x)` rounds an integer to the nearest double, and `u32(f)` truncates a float toward zero with
-- the target's range checked. Both directions are explicit here even where the value would be exact,
-- because that is what names the rounding at the point it happens.

-- An explicit numeric conversion. A same-width signedness change keeps every bit; a narrowing that
-- reaches the run-time case is checked where it happens, not at the assignment.
function Eval:applyConversionCPS(machine, ctx, ty, args, span, k)
    if #args ~= 1 then D.reject("arity", "A conversion takes one value", span) end
    local value = args[1]
    if ty:isF64() then
        if value.ty:isF64() then return k(machine, value) end
        if not value.ty:isInteger() then
            D.reject("type-mismatch", "f64 needs a number, found " .. S.encode(value.ty or S.unit), span)
        end
        return self:roundToFloatCPS(machine, ctx, value, span, k)
    end
    if ty:isInteger() and value.ty:isF64() then
        return self:truncateToIntCPS(machine, ctx, ty, value, span, k)
    end
    if not value.ty:isInteger() then
        D.reject("type-mismatch", S.encode(ty) .. " needs an integer, found "
            .. S.encode(value.ty or S.unit), span)
    end
    local reinterprets = S.widthOf(value.ty) == S.widthOf(ty)
        and value.ty:isSigned() ~= ty:isSigned()
    if reinterprets then
        -- The same width read the other way keeps every bit, so nothing is checked.
        if V.isKnown(value) then return k(machine, become(value, ty, wordsOf(value))) end
        return self:expressionCPS(machine, ctx, value, nil, function(m, expr)
            return k(m, V.runtime(ctx.builder:convert(expr, ty), ty))
        end)
    end
    -- A known value has already returned above, so a narrowing that reaches here is a run-time one:
    -- it is refused when it is converted, not at the assignment. A bound only needs a check when the
    -- source can go beyond it, which is a strict comparison.
    local converted = self:convert(value, ty, span)
    if converted then return k(machine, converted) end
    local sourceMinHigh, sourceMinLow = S.minWordsOf(value.ty)
    local sourceMaxHigh, sourceMaxLow = S.maxWordsOf(value.ty)
    local minHigh, minLow = S.minWordsOf(ty)
    local maxHigh, maxLow = S.maxWordsOf(ty)
    local compare = (value.ty:isSigned() or ty:isSigned()) and U64Kernel.slt or U64Kernel.lt
    return self:expressionCPS(machine, ctx, value, nil, function(m, expr)
        if compare(sourceMinHigh, sourceMinLow, minHigh, minLow) then
            ctx.builder:emit(ctx.body, Ir.Trap(ctx.builder:bin("Lt", expr,
                self:constInt(ctx, value.ty, minHigh, minLow), S.bool), "numeric-range"))
        end
        if compare(maxHigh, maxLow, sourceMaxHigh, sourceMaxLow) then
            ctx.builder:emit(ctx.body, Ir.Trap(ctx.builder:bin("Gt", expr,
                self:constInt(ctx, value.ty, maxHigh, maxLow), S.bool), "numeric-range"))
        end
        return k(m, V.runtime(ctx.builder:convert(expr, ty), ty))
    end)
end
-- An integer constant of a type, which a 64-bit one holds as its two words.
function Eval:constInt(ctx, ty, high, low)
    if ty:isWide() then return ctx.builder:int64(ty, high, low) end
    return ctx.builder:int(ty, low)
end


-- An application. The callee is one step, and the three builtin spellings (`slice`, `ptr`, `ref`) tail
-- into their own converted methods so a `slice(x)` costs no frame of its own. The invocation is in tail
-- position when the call is the returned expression; callee and arguments never are.
-- An application. The callee is one step, and the three builtin spellings (`slice`, `ptr`, `ref`) tail
-- into their own converted methods so a `slice(x)` costs no frame of its own. The invocation is in tail
-- position when the call is the returned expression; callee and arguments never are.
function Eval:evalApplyCPS(machine, ctx, expr, k)
    local tail = ctx.tail
    ctx.tail = false
    if not ctx.residual and expr.callee.kind == "Lambda" then
        self:step(expr.callee.span)
        return self:prepareLambdaCPS(machine, ctx, expr.callee, nil, function(m, plan)
            local function arguments(m2, callee)
                return self:evalArgumentsCPS(m2, ctx, expr.arguments, callee, function(m3, args)
                    ctx.tail = tail
                    if callee then return self:supplyCPS(m3, ctx, callee, args, expr.span, k) end
                    return self:invokePreparedLambdaCPS(m3, ctx, plan, args, expr.span, k)
                end, plan)
            end
            if #plan.borrowedOrder > 0 or #plan.runtimeOrder > 0 then
                return self:completeLambdaCPS(m, plan, expr.callee.span, arguments)
            end
            return arguments(m)
        end)
    end
    return self:evalExprCPS(machine, ctx, expr.callee, function(m, callee)
        if V.tag(callee) == "word" and callee.def.sliceOf and #callee.args == 0 and #expr.arguments == 1 then
            return self:evalSliceCPS(m, ctx, expr.arguments[1], k)
        end
        if V.tag(callee) == "word" and callee.def.ptrOf and #callee.args == 0 and #expr.arguments == 1 then
            return self:evalPtrCPS(m, ctx, expr.arguments[1], k)
        end
        if V.tag(callee) == "word" and callee.def.refOf and #callee.args == 0 and #expr.arguments == 1 then
            return self:evalRefCPS(m, ctx, expr.arguments[1], k)
        end
        return self:evalArgumentsCPS(m, ctx, expr.arguments, callee, function(m2, args)
            ctx.tail = tail
            local tag = V.tag(callee)
            if tag == "type" then
                -- `unit()` is the unit value (syntax.md §1). An integer or float type converts; any other
                -- type is not a call.
                if callee.value == S.unit then
                    if #args ~= 0 then D.reject("arity", "unit() takes no value", expr.span) end
                    return k(m2, V.unit())
                end
                if callee.value:isInteger() or callee.value:isF64() then
                    return self:applyConversionCPS(m2, ctx, callee.value, args, expr.span, k)
                end
                D.reject("callable-required", S.encode(callee.value) .. " is a type, not a callable",
                    expr.callee.span)
            end
            if tag == "ctor" then
                -- An alternative whose payload is not a record takes one positional argument; a unit
                -- alternative takes none.
                if callee.caseType == S.unit then
                    if #args ~= 0 then D.reject("arity", "A unit alternative takes no value", expr.span) end
                    return self:makeVariantCPS(m2, ctx, callee, nil, expr.span, k)
                end
                if #args ~= 1 then D.reject("arity", "A variant constructor takes one value", expr.span) end
                self:requireAgainst(args[1], callee.caseType, expr.span)
                return self:makeVariantCPS(m2, ctx, callee, args[1], expr.span, k)
            end
            return self:supplyCPS(m2, ctx, callee, args, expr.span, k)
        end)
    end)
end
-- A foreign declaration is a word with no body: its requirements and its result are written down, and
-- the host symbol it calls is the name it spells. Because there is nothing to infer from, a result that
-- the annotation leaves open is refused rather than guessed.
function Eval:foreignDef(def, lexical)
    self.nextDef = self.nextDef + 1
    return {
        id = self.nextDef, name = def.name.text, span = def.name.span,
        params = def.params, result = def.result, lexical = lexical,
        foreign = true, symbol = def.name.text,
    }
end

-- The call shape of a foreign word: every requirement is an input and the result is the declared one.
-- It is built once per definition, because a foreign call has no specialization to key.

-- The instance that describes one foreign declaration, built once per declaration.
function Eval:foreignInstanceCPS(machine, def, span, k)
    local existing = self.foreigns.instances[def]
    if existing then return k(machine, existing) end
    local sc = scope(def.lexical)
    local plan, types, inputs = {}, {}, {}
    local function parameter(index)
        if index > #def.params then
            return self:declaredResultCPS(machine, def, sc, span, function(m, declared, requirements)
                if not declared or next(requirements or {}) ~= nil then
                    D.reject("result-required", "Foreign word " .. def.name
                        .. " needs a concrete result, as in `: u32`", span)
                end
                for _, ty in ipairs(declared) do
                    if ty == false then
                        D.reject("result-required", "Foreign word " .. def.name
                            .. " needs a concrete result", span)
                    end
                    S.checkRuntime(ty, span)
                end
                -- A single `unit` result is erased, exactly as a Wordlet result contract's unit is:
                -- there is no value to carry, and emitting one would declare a `void` variable.
                if #declared == 1 and declared[1] == S.unit then declared = {} end
                local instance = { target = def.symbol, def = def, foreign = true, inputPlan = plan,
                    inputTypes = types, inputs = inputs, results = declared }
                self.foreigns.instances[def] = instance
                self.foreigns.order[#self.foreigns.order + 1] = instance
                return k(m, instance)
            end)
        end
        return self:requirementCPS(machine, def, index, sc, span, function(m, ty)
            S.checkRuntime(ty, span)
            types[#types + 1] = ty
            inputs[#inputs + 1] = S.inValue(ty)
            plan[#plan + 1] = { kind = "value", position = index }
            return parameter(index + 1)
        end)
    end
    return parameter(1)
end
-- A foreign call is an effect the compiler cannot see into, so it exists only where there is code to
-- emit: it is never folded, and the reference interpreter has no binding to call.

-- A foreign call exists only in compiled code.
function Eval:invokeForeignCPS(machine, ctx, def, values, span, k)
    if not ctx.residual then
        D.reject("foreign-effect", "A foreign call exists only in compiled code: " .. def.name
            .. "; a constant argument does not make the host call foldable", span)
    end
    return self:foreignInstanceCPS(machine, def, span, function(m, instance)
        -- A foreign word has no body, so nothing else ever compares the supplied arguments with the
        -- declared requirements. Both the contract and the values are known here, which is why the
        -- check lives here: without it a mistyped argument reaches the IR checker and is reported as
        -- an internal bug instead of a source error.
        for index, value in ipairs(values) do
            local want = instance.inputTypes[index]
            if want then self:requireAgainst(value, want, span) end
        end
        return self:emitCallCPS(m, ctx, instance, values, span, nil, k)
    end)
end

-- The one law (syntax.md §3): evaluate the callee, evaluate the arguments left to right, append
-- them to the callee's bound arguments, and test saturation. Every call in the language comes through
-- here, so a partial application is decided once and each kind of saturated call has exactly one
-- owner. `args` are evaluated values: `evalArguments` typed them against the requirements already.

-- The shim: the direct callers that are left (the residual match and the runtime dispatch) still take
-- a value from this.

-- The one place a callee of any tag becomes an invocation. A partial application answers with the
-- bound word or method rather than calling anything, and every real call is a tail call into the
-- family that handles it, so one supplied call costs one step and no frames of its own.
function Eval:supplyCPS(machine, ctx, callee, args, span, k)
    local tag = V.tag(callee)
    if tag == "word" then
        local def = callee.def
        local bound = appendArguments(callee.args, args)
        if #bound > #def.params then D.reject("arity", "Overapplication is not supported", span) end
        if #bound < #def.params then
            -- A keyed word is never supplied positionally; its requirements are supplied by name,
            -- as in `word { key = value }`.
            if def.builtin then
                requireStatic(bound, span)
            else
                if def.keyed then
                    D.reject("keyed-required",
                        "A keyed word is supplied by name, as in word { key = value }", span)
                end
                requireStatic(bound, span, def)
            end
            return k(machine, V.word(def, bound, span))
        end
        if def.builtin then return self:invokeBuiltinCPS(machine, ctx, def, bound, span, k) end
        if def.foreign then return self:invokeForeignCPS(machine, ctx, def, bound, span, k) end
        return self:invokeSourceCPS(machine, ctx, def, bound, span, k)
    end
    if tag == "method" then
        local def, receiver = callee.def, callee.receiver
        local bound = appendArguments(callee.args, args)
        if #bound > #def.params then D.reject("arity", "Overapplication is not supported", span) end
        if #bound < #def.params then
            requireStatic(bound, span, def)
            return k(machine, setmetatable({ tag = "method", def = def, receiver = receiver,
                args = bound }, V.mt))
        end
        if not receiver then
            D.reject("missing-receiver", "Bind the receiver before calling " .. def.name, span)
        end
        return self:invokeMethodCPS(machine, ctx, def, bound, receiver, span, k)
    end
    if tag == "closure" then
        return self:invokeClosureCPS(machine, ctx, callee.plan, nil, args, span, callee.bound, k)
    end
return self:invokeRuntimeCPS(machine, ctx, callee, args, span, k)
end


-- A builtin runs its terminal directly: it has no body to fold and never builds an instance.

-- A builtin is one Lua function over its arguments, so its answer is direct.
function Eval:invokeBuiltinCPS(machine, ctx, def, values, span, k)
    return k(machine, def.builtin(self, ctx, values, span))
end

-- A named word with a source body, which is the only word that can become an instance.

-- A named word: fold it now or compile an instance.
function Eval:invokeSourceCPS(machine, ctx, def, values, span, k)
    return self:foldOrBuildCPS(machine, ctx, def, values, span, nil,
        "This call needs runtime storage or values", k)
end

-- A method on a receiver: the receiver is an argument of a different shape, and only a concrete
-- record can have its fields read for a static fold.

-- A method call: the receiver's fields are the fold's input, so it folds only over a concrete record.
function Eval:invokeMethodCPS(machine, ctx, def, values, receiver, span, k)
    return self:foldOrBuildCPS(machine, ctx, def, values, span, receiver,
        "This method call needs runtime storage", k)
end

-- The fold-or-build decision every saturated word and method call shares: a call whose arguments
-- are all known, and either all static or in normalize code, is folded; anything else is built.

-- Fold the call now, or compile an instance for it. This is where the `pcall` used to be, and it is
-- the reason the machine has handlers: folding is an optimization in residual code, so a diagnostic
-- that says the body needs runtime storage is the signal to compile instead, while any other
-- diagnostic is a real one. The handler below is that decision; the machine routes a raised diagnostic
-- to it instead of unwinding a host stack, so the fold attempt costs one descriptor and no frames.
function Eval:foldOrBuildCPS(machine, ctx, def, values, span, receiver, subject, k)
    local allKnown, allStatic = true, true
    for _, value in ipairs(values) do
        if not V.isKnown(value) then allKnown = false end
        if not V.isStatic(value) then allStatic = false end
    end
    local foldable = allKnown and (not ctx.residual or allStatic)
    if foldable and receiver ~= nil then foldable = V.tag(receiver) == "record" end
    if foldable then
        -- Checked before the descriptor is pushed, so a refusal leaves the session as it found it, and
        -- raised to the *enclosing* handler: a nested fold that runs out of room in residual code
        -- compiles instead.
        machine:checkDepth("static", span, def.name)
        machine:push("static", span, def.name, function(m, diagnostic)
            if not ctx.residual then error(diagnostic, 0) end
            if not (D.is(diagnostic) and (diagnostic.code == "runtime-in-normalization"
                or diagnostic.code == "static-depth" or diagnostic.code == "foreign-effect")) then
                error(diagnostic, 0)
            end
            return self:callInstanceCPS(m, ctx, def, values, span, receiver, k)
        end)
        return self:evaluateStaticallyCPS(machine, def, values, span, receiver, function(m, folded)
            machine:pop()
            return k(m, folded)
        end)
    end
    if not ctx.residual then
        D.reject("runtime-in-normalization", subject, span)
    end
    return self:callInstanceCPS(machine, ctx, def, values, span, receiver, k)
end

-- `Word { key = value }`: supply a word's keyed requirements. Values are evaluated in written
-- order; a name that is not a requirement, or one supplied twice, rejects. A keyed requirement is
-- always annotated, and an annotation written as a signature types the value supplied for it exactly
-- as a positional requirement does, which is what lets `f { g = |x| -> x }` leave `x` unannotated.

-- A keyed invocation `f { x = 1 }`. Its requirements have no order, so the walk over the written
-- fields is a local driver; a fully supplied word becomes a positional call through `supply`, and a
-- partial one becomes a specialised word whose remaining requirements are positional.
-- A keyed invocation `f { x = 1 }`. Its requirements have no order, so the walk over the written
-- fields is a local driver; a fully supplied word becomes a positional call through `supply`, and a
-- partial one becomes a specialised word whose remaining requirements are positional.
function Eval:applyKeyedCPS(machine, ctx, word, fields, span, tail, k)
    local def = word.def
    local params = def.params
    local byName = {}
    for _, param in ipairs(params) do byName[param.name.text] = param end
    local bound = {}
    for name, value in pairs(def.statics or {}) do bound[name] = value end
    -- A keyed requirement has no order, so an annotation may not depend on another key: the word's
    -- own lexical scope is the right place to resolve one.
    local lexical = scope(def.lexical)
    local function afterFields()
        local remaining = {}
        for _, param in ipairs(params) do
            if bound[param.name.text] == nil then remaining[#remaining + 1] = param end
        end
        if #remaining == 0 then
            local values = {}
            for index, param in ipairs(params) do values[index] = bound[param.name.text] end
            ctx.tail = tail
            return self:supplyCPS(machine, ctx, V.word(def, values, span), {}, span, k)
        end
        for _, value in pairs(bound) do
            if not V.isStatic(value) then
                D.reject("static-required", "Partial keyed supply needs a static value", span)
            end
        end
        self.nextDef = self.nextDef + 1
        local specialized = {
            id = self.nextDef, name = def.name, node = def.node, span = def.span,
            params = remaining, keyed = remaining, statics = bound,
            result = def.result, body = def.body, lexical = def.lexical, fields = def.fields,
            tailSelf = def.tailSelf,
        }
        ctx.tail = false
        return k(machine, V.word(specialized, {}, span))
    end
    local function field(index)
        if index > #fields then return afterFields() end
        local entry = fields[index]
        local name = entry.name.text
        local param = byName[name]
        if not param then
            D.reject("unknown-member", "Word " .. def.name .. " has no keyed requirement " .. name,
                entry.name.span)
        end
        if bound[name] ~= nil then
            D.reject("duplicate", "Keyed requirement " .. name .. " is supplied twice", entry.name.span)
        end
        local function withExpected(expected)
            return self:evalExpectedCPS(machine, ctx, entry.value, expected, function(m, value)
                bound[name] = value
                return field(index + 1)
            end)
        end
        if not param.annotation then return withExpected(nil) end
        return self:typeOfCPS(machine, param.annotation, lexical, param.span, function(m, ty)
            return withExpected(ty:isSig() and ty or nil)
        end)
    end
    return field(1)
end
-- Shared scope construction: parameters, and receiver fields for methods.

-- The scope a word's body sees: the receiver's fields, the statics a partial supply bound, and then
-- the parameters one at a time, because a later annotation may depend on an earlier parameter.
function Eval:parameterScopeCPS(machine, def, values, receiver, k)
    local sc = scope(def.lexical)
    if receiver then
        local rdef = receiver.schema or receiver.def
        for _, name in ipairs(rdef.fieldNames) do
            if V.tag(receiver) == "record" then
                declare(sc, name, { kind = "concrete-field", name = name, record = receiver,
                    ty = rdef.fields[name], readonly = rdef.readonly[name] and true or false }, def.span)
            else
                declare(sc, name, self:fieldSlot(rdef, receiver, name), def.span)
            end
        end
    end
    -- A keyed word partially supplied earlier carries those values as statics, so the body sees
    -- them exactly as if they had been supplied now.
    for name, value in pairs(def.statics or {}) do
        declare(sc, name, { kind = "value", name = name, value = value }, def.span)
    end
    local function parameter(index)
        if index > #def.params then return k(machine, sc) end
        local param = def.params[index]
        -- Check each requirement against the supplied value before binding the next parameter,
        -- since a later annotation may depend on an earlier parameter.
        return self:requirementCPS(machine, def, index, sc, def.span, function(m, ty)
            local value = self:copyArgument(values[index])
            if value then self:requireAgainst(value, ty, param.span) end
            declare(sc, param.name.text, { kind = "value", name = param.name.text, value = value },
                param.span)
            return parameter(index + 1)
        end)
    end
    return parameter(1)
end
-- Ordinary parameter binding copies record data; a local alias keeps its instance, an argument
-- does not. Field values are immutable, so a shallow copy of the field table is a value copy.
function Eval:copyArgument(value)
    if V.tag(value) == "int" or V.tag(value) == "float" then
        -- Coercion retags numeric wrappers in place. The parameter owns its wrapper, not the
        -- caller's binding or a captured snapshot that happens to refer to that same atom.
        local copy = {}
        for name, field in pairs(value) do copy[name] = field end
        return setmetatable(copy, V.mt)
    end
    if V.tag(value) == "array" then
        local items = {}
        for index, item in ipairs(value.items or {}) do items[index] = item end
        return V.array(value.ty, items, value.place)
    end
    if V.tag(value) ~= "record" then return value end
    local fields = {}
    for name, field in pairs(value.fields) do fields[name] = field end
    return V.record(value.ty, fields, value.schema)
end


-- Compile-time execution of a word over concrete values. The frame is a static one, which is what makes
-- module storage readable and writable here, and the block walk carries the depth.
-- Compile-time execution of a word over concrete values. The frame is a static one, which is what makes
-- module storage readable and writable here, and the block walk carries the depth.
function Eval:evaluateStaticallyCPS(machine, def, values, span, receiver, k)
    return self:parameterScopeCPS(machine, def, values, receiver, function(m, sc)
        return self:declaredResultCPS(m, def, sc, span, function(m2, declared, requirements)
            local ctx = self:staticFrame(sc, span)
            ctx.expectedResult = self:resultExpectation(requirements)
            return self:execBodyCPS(m2, ctx, def.body, span, function(m3, result)
                if declared then
                    if #declared ~= #result then
                        D.reject("branch-result", "Word " .. def.name .. " returned " .. #result
                            .. " values but declares " .. #declared, span)
                    end
                    for index, ty in ipairs(declared) do
                        if ty ~= false then self:requireAgainst(result[index], ty, span) end
                    end
                end
                if requirements then
                    for index, requirement in pairs(requirements) do
                        self:requireResultSignature(result[index], requirement, span)
                    end
                end
                if #result == 0 then return k(m3, V.unit()) end
                if #result == 1 then return k(m3, result[1]) end
                return k(m3, V.results(result))
            end)
        end)
    end)
end
-- The saturated call that cannot fold: emit a call to the instance, or, when the call is a tail call
-- to the instance currently being built, a back edge to its loop header.

-- A call to a compiled instance, or a back edge when the tail call is to the instance being built. A
-- block with a pending deferred action does not become a loop: the action runs after the call returns
-- and before the value leaves, which is not the order a back edge would give.
function Eval:callInstanceCPS(machine, ctx, def, values, span, receiver, k)
    return self:instanceForCPS(machine, def, span, values, receiver, function(m, instance)
        if instance.status == "building" and not instance.results then
            D.reject("recursive-result", "Recursive " .. (receiver and "method " or "word ") .. def.name
                .. " needs an explicit result annotation", span)
        end
        if ctx.tail and not ctx.deferFrame and ctx.instance == instance and instance.loopTargets then
            return self:loopBackCPS(m, ctx, instance, values, span, k)
        end
        return self:emitCallCPS(m, ctx, instance, values, span, receiver, k)
    end)
end

-- Evaluate every next argument before assigning any parameter, then transfer to the loop head.

-- A tail call to the instance being built is a back edge: the loop targets are written from the
-- arguments and the block ends with `Next` rather than calling itself.
-- A tail call to the instance being built is a back edge: the loop targets are written from the
-- arguments and the block ends with `Next` rather than calling itself.
function Eval:loopBackCPS(machine, ctx, instance, values, span, k)
    local builder = ctx.builder
    local temporaries = {}
    local function targetAt(index)
        if index > #instance.loopTargets then
            for position, target in ipairs(instance.loopTargets) do
                -- A slot the tail call forwards unchanged already holds its value: storing it back
                -- would be a self-copy. Only slots the call actually rebinds get a back-edge store.
                if temporaries[position] then
                    builder:store(ctx.body, Ir.Local(target.storage), temporaries[position])
                end
            end
            builder:emit(ctx.body, Ir.Next)
            instance.loopBack = true
            ctx.terminated = true
            return k(machine)
        end
        local target = instance.loopTargets[index]
        local value = values[target.position]
        self:requireType(value, target.ty, span)
        -- The argument is exactly the binding this slot already carries, and the parameter is
        -- immutable, so nothing between the header and here could have changed it. No temp, no
        -- store; the loop edge leaves the slot alone.
        if value == target.binding then return targetAt(index + 1) end
        local id = builder:valueId()
        return self:expressionCPS(machine, ctx, value, nil, function(m, expr)
            builder:emit(ctx.body, Ir.Let(id, target.ty, expr))
            temporaries[index] = builder:ref(id, target.ty)
            return targetAt(index + 1)
        end)
    end
    return targetAt(1)
end
-- Builds the argument list from the instance's input plan.

-- The call itself: a borrowed receiver becomes a place argument, every other input is materialised,
-- and the results come back as runtime values with the unit slots reinserted.
function Eval:emitCallCPS(machine, ctx, instance, values, span, receiver, k)
    local builder = ctx.builder
    local args = {}
    local function input(index)
        if index > #instance.inputPlan then
            local runtime = instance.runtimeResults or self:runtimeResults(instance.results)
            local results = {}
            for _ = 1, #runtime do results[#results + 1] = builder:valueId() end
            builder:emit(ctx.body, Ir.Call(S.list(results), instance.target, S.list(args)))
            local ir = {}
            for position, ty in ipairs(runtime) do
                ir[position] = V.runtime(builder:ref(results[position], ty), ty)
            end
            local out = self:logicalResults(instance.results, ir)
            if #out == 0 then return k(machine, V.unit()) end
            if #out == 1 then return k(machine, out[1]) end
            return k(machine, V.results(out))
        end
        local plan = instance.inputPlan[index]
        if plan.kind == "place" then
            -- A borrowed receiver must be a place; a record still carrying its construction
            -- expression materialises once here.
            return self:recordPlaceCPS(machine, ctx, receiver, span, function(m, place)
                args[#args + 1] = Ir.BorrowArg(place)
                return input(index + 1)
            end)
        end
        return self:expressionCPS(machine, ctx, values[plan.position], instance.inputTypes[index],
            function(m, expr)
                args[#args + 1] = Ir.ValueArg(expr)
                return input(index + 1)
            end)
    end
    return input(1)
end
-- Instance construction ------------------------------------------------------------------------

function Eval:instanceKey(def, values, receiver)
    local parts = { tostring(def.id) }
    if receiver then
        local rdef = receiver.schema
        local names = {}
        for name in pairs(rdef.statics) do names[#names + 1] = name end
        table.sort(names)
        parts[#parts + 1] = "recv"
        for _, name in ipairs(names) do
            local encoded = V.encode(rdef.statics[name])
            if not encoded then D.bug("instance-key", "A static receiver field has no encoding") end
            parts[#parts + 1] = name .. "=" .. encoded
        end
    end
    -- Every parameter position contributes to the key, including unsupplied ones. An export face
    -- passes no values, but it must still name the same instance as an ordinary call to it.
    for index = 1, #def.params do
        local value = values[index]
        if value ~= nil and V.isStatic(value) then
            local encoded = V.encode(value)
            if not encoded then D.bug("instance-key", "A static argument has no encoding") end
            parts[#parts + 1] = S.encode(value.ty) .. "=" .. encoded
        else
            -- A runtime callable carries its code identity in its type, so two different closures
            -- must not share an instance. Other runtime arguments are fixed by the requirement.
            local ty = value and value.ty
            parts[#parts + 1] = (ty and ty:isOwned()) and ("!" .. ty.entry) or "*"
        end
    end
    return table.concat(parts, "/")
end

-- The shim: the word path reaches the converted form directly; this stays for any caller that has not
-- converted.

-- The instance for one definition and argument vector. A build that failed is remembered, so a later
-- call with the same key reports the same diagnostic rather than finding an instance never finished.
function Eval:instanceForCPS(machine, def, span, values, receiver, k)
    values = values or {}
    local key = self:instanceKey(def, values, receiver)
    local existing = self.instances[key]
    if existing then
        if existing.failure then error(existing.failure, 0) end
        return k(machine, existing)
    end
    if self.instanceCount >= (self.limits.keys or 1024) then
        D.resource("keys", "Residual instance budget exhausted", span)
    end
    return self:buildInstanceCPS(machine, key, def, values, span, receiver, k)
end
function Eval:loopTarget(instance, position, storage, ty, binding)
    instance.loopTargets = instance.loopTargets or {}
    -- `binding` is the frontend value the parameter name denotes this iteration. Identity with a
    -- forwarded argument is what lets the back edge skip a slot that already holds it.
    instance.loopTargets[#instance.loopTargets + 1] =
        { position = position, storage = storage, ty = ty, binding = binding }
end

-- A failed build leaves the half-made instance remembered as failed, so a later attempt re-raises
-- that diagnostic instead of building again. The nesting budget itself belongs to the session.

-- Building a word or method instance, one `Build` descriptor per attempt.
function Eval:buildInstanceCPS(machine, key, def, values, span, receiver, k)
    machine:checkDepth("build", span, key)
    local savedRun, savedDemand = self.run, self.demanding
    self.run, self.demanding = false, false
    machine:push("build", span, key, function(_, diagnostic)
        self.run, self.demanding = savedRun, savedDemand
        local instance = self.instances[key]
        if instance then
            instance.failure = diagnostic
            instance.status = "failed"
        end
        error(diagnostic, 0)
    end)
    return self:constructInstanceCPS(machine, key, def, values, span, receiver, function(m, instance)
        machine:pop()
        self.run, self.demanding = savedRun, savedDemand
        return k(m, instance)
    end)
end
function Eval:constructInstanceCPS(machine, key, def, values, span, receiver, k)
    self.nextFn = self.nextFn + 1
    local instance = { key = key, def = def, target = "wordletfn_" .. self.nextFn,
        status = "building", args = values, inputPlan = {}, inputTypes = {} }
    self:registerInstance(instance)

    local body, setup = {}, {}
    local builder = IR.builder()
    local sc = scope(def.lexical)
    local params, paramTypes, inputs = {}, {}, {}

    -- A method's receiver is borrowed storage, so it is input zero and a place parameter.
    if receiver then
        local rdef = receiver.schema
        local storage = builder:storageId()
        inputs[#inputs + 1] = S.inPlace(rdef.type)
        instance.inputTypes[#instance.inputTypes + 1] = rdef.type
        params[#params + 1] = Ir.PlaceParam(#inputs - 1, storage, rdef.type)
        instance.inputPlan[#instance.inputPlan + 1] = { kind = "place" }
        for _, name in ipairs(rdef.fieldNames) do
            if rdef.statics[name] then
                declare(sc, name, { kind = "value", name = name, value = rdef.statics[name] }, def.span)
            else
                -- A receiver belongs to the caller, so storing a borrow in it would outlive the
                -- activation that produced the borrow.
                declare(sc, name, { kind = "field", name = name, ty = rdef.fields[name],
                    place = Ir.Project(Ir.Local(storage), Ir.Field(name)), retaining = true }, def.span)
            end
        end
    end
    -- Keyed values supplied earlier travel on the definition, so the body sees them as bindings.
    for name, value in pairs(def.statics or {}) do
        declare(sc, name, { kind = "value", name = name, value = value }, span)
    end

    local function afterParameters(m)
        return self:declaredResultCPS(m, def, sc, span, function(m, declared, requirements)
    instance.results, instance.resultRequirements = declared, requirements
    local ctx = self:residualFrame(sc, span)
    ctx.builder, ctx.body, ctx.fn, ctx.instance = builder, body, { id = instance.target }, instance
    ctx.expectedResult = self:resultExpectation(requirements)
    return self:execBodyResidualCPS(m, ctx, def.body, span, function(m2)
    if instance.results then
        for index, ty in ipairs(instance.results) do
            if ty == false then instance.results[index] = ctx.resultTypes and ctx.resultTypes[index] end
        end
    else
        instance.results = ctx.resultTypes
    end
    if not instance.results then
        D.reject("recursive-result", "Word " .. def.name .. " has no returning path", span)
    end
    self:checkResultContract(instance.results, ctx.resultTypes, "Word " .. def.name, span)
    if requirements then
        for index, requirement in pairs(requirements) do
            local actual = instance.results[index]
            self:requireResultSignature(actual and { ty = actual } or nil, requirement, span)
        end
    end
    for _, ty in ipairs(instance.results) do
        if not S.representable(ty) then
            D.todo("static-callable-result",
                "A result that is pure code with no environment has no runtime representation", span)
        end
    end
    instance.runtimeResults = self:runtimeResults(instance.results)
    -- Loop-carried parameter storage lives outside the loop so it survives each iteration.
    local statements = setup
    local header = instance.loopHeader or {}
    if instance.loopBack then
        -- The header reads run once per iteration; the back edge stores the next values.
        local iterations = {}
        for _, stmt in ipairs(header) do iterations[#iterations + 1] = stmt end
        for _, stmt in ipairs(body) do iterations[#iterations + 1] = stmt end
        statements[#statements + 1] = Ir.Loop(S.list(iterations))
    else
        for _, stmt in ipairs(header) do statements[#statements + 1] = stmt end
        for _, stmt in ipairs(body) do statements[#statements + 1] = stmt end
    end
    instance.fn = Ir.Fn(instance.target, Ir.Body, receiver and 1 or 0, S.list(inputs),
        S.list(instance.runtimeResults), S.list(params), S.list(statements))
    instance.paramTypes = paramTypes
    instance.status = "done"
    return k(m2, instance)
    end)
    end)
    end
    local function parameterAt(index, m)
        if index > #def.params then return afterParameters(m) end
        local param = def.params[index]
        return self:requirementCPS(m, def, index, sc, span, function(m2, ty)
            if ty:isSig() then
                -- A callable parameter: static code is specialised away entirely; otherwise the Owned
                -- type carries the code identity, so the call stays direct and only the environment
                -- travels as a by-value input.
                local supplied = values[index]
                if supplied ~= nil and (V.tag(supplied) == "closure" or V.tag(supplied) == "word") then
                    if self:callableMatches(supplied, ty) == false then
                        D.reject("callable-shape", "Callable does not match the required signature", param.span)
                    end
                    if V.isStatic(supplied) then
                        declare(sc, param.name.text, { kind = "value", name = param.name.text, value = supplied },
                            param.span)
                        goto continue
                    else
                        -- A closure with a runtime environment travels by value as that environment. A
                        -- closure that borrows storage is non-retaining, so the parameter becomes an
                        -- erased view, which the caller binds through a local adapter that holds the
                        -- borrowed places.
                        ty = self:borrowsStorage(supplied) and S.view(ty) or supplied.ty
                    end
                elseif V.tag(supplied) == "method" then
                    -- A method borrows its receiver, so it is non-retaining for the same reason a
                    -- borrowing closure is: the parameter takes a view.
                    ty = S.view(ty)
                elseif supplied ~= nil and V.tag(supplied) == "runtime" and supplied.ty:isOwned() then
                    ty = supplied.ty
                elseif supplied ~= nil and V.tag(supplied) == "runtime" and supplied.ty:isView() then
                    ty = supplied.ty
                elseif supplied == nil then
                    -- An entry face with no call site: the callable arrives from outside, so it needs
                    -- the invocation-pointer ABI rather than a code identity.
                    ty = S.view(ty)
                else
                    D.todo("opaque-callable",
                        "A callable argument with no known code needs a function-pointer ABI", param.span)
                end
            else
                -- `type` and the other compile-time descriptors have no runtime representation, so a
                -- parameter of one has to be supplied statically; the static branch below binds it.
                if not S.runtime(ty) then
                    if values[index] == nil or not V.isStatic(values[index]) then
                        D.reject("static-required", "Parameter " .. param.name.text
                            .. " needs a static argument of type " .. S.display(ty), param.span)
                    end
                else
                    S.checkRuntime(ty, param.span)
                end
            end
            if ty == S.unit then
                -- Erased exactly like a unit result: no input, no ABI slot, name bound directly.
                declare(sc, param.name.text, { kind = "value", name = param.name.text, value = V.unit() }, param.span)
                goto continue
            end
            do
            local supplied = values[index]
            if supplied and (V.isInteger(supplied) or V.tag(supplied) == "float") then
                supplied = self:copyArgument(supplied)
            end
            -- A supplied argument is checked against the requirement whichever branch binds it. The
            -- static branch below checks the type as well; without this line a run-time argument would
            -- reach the IR checker unchecked, where a wrong type is a compiler bug instead of a source
            -- error.
            if supplied ~= nil then self:requireAgainst(supplied, ty, param.span) end
            if supplied ~= nil and V.isStatic(supplied) then
                self:requireType(supplied, ty, param.span)
                declare(sc, param.name.text, { kind = "value", name = param.name.text, value = supplied }, param.span)
            else
                local value = builder:valueId()
                params[#params + 1] = Ir.ValueParam(#inputs, value, ty)
                inputs[#inputs + 1] = S.inValue(ty)
                paramTypes[#paramTypes + 1] = ty
                instance.inputPlan[#instance.inputPlan + 1] = { kind = "value", position = index }
                -- The call site needs each input's type to materialise its argument, so the two lists
                -- are maintained together.
                instance.inputTypes[#instance.inputTypes + 1] = ty
                if ty:isArray() then
                    -- A by-value array parameter owns fresh storage only when an element is addressed;
                    -- a whole-value use reads the input directly.
                    declare(sc, param.name.text, { kind = "value", name = param.name.text,
                        value = V.array(ty, nil, nil, false, builder:ref(value, ty), setup) }, param.span)
                elseif ty:isRecord() then
                    -- A by-value record parameter owns fresh storage only when a write or an address
                    -- demands one, so a read-only parameter reads the input directly. A loop-carried
                    -- parameter needs its storage up front because the back edge names it.
                    local fields = { fields = S.fieldsOf(ty),
                        fieldNames = S.fieldNames(ty), statics = {}, readonly = {}, methods = {}, type = ty }
                    if def.tailSelf then
                        local storage = builder:storageId()
                        setup[#setup + 1] = Ir.Var(storage, ty, builder:ref(value, ty))
                        local binding = V.object(ty, Ir.Local(storage), fields)
                        self:loopTarget(instance, index, storage, ty, binding)
                        declare(sc, param.name.text, { kind = "value", name = param.name.text,
                            value = binding }, param.span)
                    else
                        declare(sc, param.name.text, { kind = "value", name = param.name.text,
                            value = V.object(ty, nil, fields, nil, false, builder:ref(value, ty), setup) },
                            param.span)
                    end
                elseif def.tailSelf then
                    -- Loop-carried parameters need mutable storage so a back edge can rebind them.
                    local storage = builder:storageId()
                    setup[#setup + 1] = Ir.Var(storage, ty, builder:ref(value, ty))
                    -- A value parameter is immutable, so one read per iteration is equivalent to reading at
                    -- every mention. Sharing the read is what lets expressions built from the parameter be
                    -- shared too, because reads are never interned.
                    local read = builder:valueId()
                    instance.loopHeader = instance.loopHeader or {}
                    instance.loopHeader[#instance.loopHeader + 1] = Ir.Read(read, ty, Ir.Local(storage))
                    local binding = V.runtime(builder:ref(read, ty), ty)
                    self:loopTarget(instance, index, storage, ty, binding)
                    declare(sc, param.name.text, { kind = "value", name = param.name.text,
                        value = binding }, param.span)
                else
                    declare(sc, param.name.text, { kind = "value", name = param.name.text,
                        value = V.runtime(builder:ref(value, ty), ty) }, param.span)
                end
            end
            end
            ::continue::
            return parameterAt(index + 1, m2)
        end)
    end
    return parameterAt(1, machine)
end

-- A result annotation that is a signature states what the returned callable must look like, not a
-- concrete type: the body fixes the code identity, so that slot stays open until the body returns.

-- A word's declared result list: a signature result is a requirement rather than a type, because only
-- a shape can be checked against it.
function Eval:declaredResultCPS(machine, def, sc, span, k)
    local result = def.result
    if not result then return k(machine, nil, nil) end
    sc = sc or def.lexical
    local expressions = {}
    if result.kind == "Single" then
        expressions[1] = result.type
    else
        for index, item in ipairs(result.types) do expressions[index] = item end
    end
    local types, requirements = {}, {}
    local function declared(index)
        if index > #expressions then
            if next(requirements) == nil then return k(machine, types, nil) end
            return k(machine, types, requirements)
        end
        return self:typeOfCPS(machine, expressions[index], sc, span, function(m, ty)
            if ty:isSig() then
                types[index], requirements[index] = false, ty
            else
                S.checkRuntime(ty, span)
                types[index] = ty
            end
            return declared(index + 1)
        end)
    end
    return declared(1)
end
-- One open result slot, or none, is what a signature result annotation can fix.
function Eval:resultExpectation(requirements)
    if not requirements then return nil end
    local only
    for _, requirement in pairs(requirements) do
        if only then return nil end
        only = requirement
    end
    return only
end

-- Body execution ------------------------------------------------------------------------------

-- The shim: `evaluateStatically`, `evaluateClosureStatically` and the construction path still reach
-- this by name.

-- A function body: an expression body is one evaluated expression, a block body is the statement walk
-- plus the check that some path returned. The answer is the returned value list.
function Eval:execBodyCPS(machine, ctx, body, span, k)
    if body.kind == "Expression" then
        return self:evalExpectedCPS(machine, ctx, body.value, ctx.expectedResult, function(m, value)
            local values = self:expand(value)
            self:checkReturn(values, span)
            return k(m, values)
        end)
    end
    ctx.result = nil
    return self:execBlockCPS(machine, ctx, body.statements, nil, function(m, returned)
        if not returned then D.reject("no-return", "Every reachable path must return a value", span) end
        return k(m, ctx.result)
    end)
end

-- A function body compiled into an instance: the returned values are materialised into an `Ir.Return`
-- rather than handed back as frontend values.
function Eval:execBodyResidualCPS(machine, ctx, body, span, k)
    if body.kind == "Expression" then
        ctx.tail, ctx.terminated = true, false
        return self:evalExpectedCPS(machine, ctx, body.value, ctx.expectedResult, function(m, value)
            if ctx.terminated then return k(m) end
            ctx.tail = false
            local values = self:expand(value)
            self:checkReturn(values, span)
            return self:materializeAllCPS(m, ctx, values,
                ctx.instance and ctx.instance.results or nil, function(m2, exprs)
                    ctx.builder:return_(ctx.body, exprs)
                    ctx.resultTypes = {}
                    for position, item in ipairs(values) do ctx.resultTypes[position] = item.ty end
                    return k(m2)
                end)
        end)
    end
    return self:execBlockCPS(machine, ctx, body.statements, nil, function(m, returned)
        if not returned then D.reject("no-return", "Every reachable path must return a value", span) end
        return k(m)
    end)
end

return Eval
