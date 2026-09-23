-- The evaluator: one walker for concrete, normalization and residual execution.
--
-- Modes: "normalize" has no builder at all, so a static attempt cannot leave partial IR behind;
-- "residual" emits statements into the current Ir.Fn. Both share every expression rule.
local D = require("wordlet.diag")
local S = require("wordlet.schema")
local IR = require("wordlet.ir")
local V = require("wordlet.value")
local Resolve = require("wordlet.resolve")

local M = {}
local Eval = {}
Eval.__index = Eval

local Ir = S.Ir
local U64Kernel = require("wordletkit.u64")

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
    local compare = S.isSigned(ty) and U64Kernel.sle or U64Kernel.le
    return compare(minHigh, minLow, high, low) and compare(high, low, maxHigh, maxLow)
end

-- Retags a value with a new type and representation. A runtime value keeps its expression, which is
-- where its value lives; a type that fits a Lua number also keeps a number.
function become(value, ty, high, low)
    if V.tag(value) == "ir" then
        value.ty = ty
        return value
    end
    if S.isWide(ty) then
        value.ty, value.n, value.high, value.low = ty, nil, high, low
    elseif S.isSigned(ty) and low >= 2147483648 then
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
    local compare = (S.isSigned(from) or S.isSigned(to)) and U64Kernel.sle or U64Kernel.le
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
    if S.isWide(ty) then
        if S.isSigned(ty) then return 9223372036854775808.0, -9223372036854775808.0 end
        return 18446744073709551616.0, 0.0
    end
    return S.maxOf(ty) + 1, S.minOf(ty)
end

-- A readable form of an integer value's words, for a diagnostic.
function describeWords(ty, high, low)
    if S.isWide(ty) then return U64Kernel.tostring(high, low, S.isSigned(ty)) end
    return tostring(high * 4294967296 + low)
end

-- Module-level mutable storage is emitted as a file-scope object, so its ids must not look like
-- the function-local storage the builder allocates for each body.
local MODULE_STORAGE_BASE = 1048576

local ARITH = {
    ["+"] = "Add", ["-"] = "Sub", ["*"] = "Mul", ["/"] = "Div", ["%"] = "Rem", ["^"] = "Pow",
    ["<<"] = "Shl", [">>"] = "Shr", ["&"] = "BitAnd", ["|"] = "BitOr", ["~"] = "BitXor",
}
-- F64 has no remainder, power, shift or bitwise operator: those are integer operations, and IEEE
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

local Ctx = {}
Ctx.__index = Ctx
function Ctx:arm(list)
    return setmetatable({ session = self.session, mode = self.mode, scope = self.scope,
        span = self.span, builder = self.builder, body = list,
        instance = self.instance, tail = self.tail, expectedResult = self.expectedResult,
        -- An arm is part of the enclosing block, so a deferred action pending there is still pending
        -- inside the arm: a `return` in an arm must run it too.
        deferFrame = self.deferFrame }, Ctx)
end

function M.session(options)
    options = options or {}
    local limits = options.limits or {}
    return setmetatable({
        options = options, limits = limits,
        definitions = {}, instances = {}, order = {}, moduleStorages = {},
        -- Foreign declarations in first-use order, so the prototypes they need are deterministic.
        foreignInstances = {}, foreignOrder = {},
        -- Tagged-callable arms, keyed by the code identity that names them in a type.
        arms = {},
        -- Sealed definitions of named cells, keyed by the identity a recursive definition reserved.
        typeCells = {},
        nextTypeCell = 0,
        nextDef = 0, nextFn = 0, steps = 0,
        maxSteps = limits.steps or 1000000,
        -- Three separate budgets, because they bound three different recursions. Specialization
        -- nesting is the depth of nested instance building; static depth is nested compile-time
        -- folding, which is an optimization in residual code and can fall back to compiling; and
        -- the interpreter, which has no fallback, gets the largest bound it can have without
        -- reaching the host's own stack limit (measured at roughly 2500 on this host, so this
        -- deliberately stays well below it).
        buildDepth = 0, maxBuildDepth = limits.depth or 256,
        staticDepth = 0, maxStaticDepth = limits.staticDepth or 64,
        maxInterpretDepth = limits.interpretDepth or 1024,
    }, Eval)
end

function Eval:step(span)
    self.steps = self.steps + 1
    if self.steps > self.maxSteps then D.resource("steps", "Static evaluation budget exhausted", span) end
end

-- Specialization nests: building one instance evaluates its body, and a body that specializes again
-- nests another build. The host's Lua stack gives out long before a thousand nested builds would reach
-- the key budget, so the nesting is bounded here and its exhaustion names a resource instead of
-- surfacing as an unlabelled stack overflow.
function Eval:enterBuild(span)
    self.buildDepth = self.buildDepth + 1
    if self.buildDepth > self.maxBuildDepth then
        D.resource("depth", "Specialization nests more than " .. self.maxBuildDepth
            .. " deep; a recursive word whose static arguments change specializes once per value, so"
            .. " bind the changing value at run time", span)
    end
end

function Eval:leaveBuild() self.buildDepth = self.buildDepth - 1 end

-- Folding a known call is optional in residual code, so its depth is a budget rather than a wall: a
-- fold that runs out of depth is compiled instead. The reference interpreter has no such fallback, so
-- it is given the largest bound it can have without reaching the host stack limit.
function Eval:enterStatic(def, span)
    self.staticDepth = self.staticDepth + 1
    local allowed = self.run and self.maxInterpretDepth or self.maxStaticDepth
    if self.staticDepth > allowed then
        D.resource("static-depth", "Static evaluation nests more than " .. allowed .. " deep in "
            .. def.name .. "; a recursive word with a run-time argument is compiled instead, and"
            .. " the reference interpreter is bounded", span)
    end
end

function Eval:leaveStatic() self.staticDepth = self.staticDepth - 1 end

function Eval:context(mode, sc, span)
    return setmetatable({ session = self, mode = mode, scope = sc, span = span }, Ctx)
end

-- Top level -----------------------------------------------------------------------------------

function Eval:load(program)
    local top = scope(nil)
    self.top = top
    for _, decl in ipairs(program.declarations) do
        if decl.kind == "ForeignDecl" then
            local slot = declare(top, decl.def.name.text,
                { kind = "word", name = decl.def.name.text }, decl.span)
            slot.def = self:foreignDef(decl.def, top)
        elseif decl.kind == "WordDecl" then
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
    for _, name in ipairs({ "U32", "U8", "U16", "I32", "U64", "I64", "F64", "Bool", "Unit", "Type" }) do
        declare(top, name, { kind = "value", name = name, value = V.type(S[name]) })
    end
    -- `Ref(T)` is a type and `Ref(place)` is a reference to that place. Both are the same ordinary
    -- word, dispatched on whether the argument is a type value or a place, so no new syntax is
    -- needed and the builtin is applied, supplied and checked like any other word.
    local refBuiltin = self:builtin("Ref", { { name = "target" } }, function(engine, ctx, values, span)
        local target = values[1]
        local ty = engine:asType(target, span)
        if ty then return V.type(S.ref(engine:canonicalize(ty))) end
        return engine:makeReference(ctx, target, span)
    end)
    -- A reference must name a place, and only the argument expression says whether that place has
    -- an identity that outlives the reference, so `Ref` needs the expression as well as the value.
    refBuiltin.refOf = true
    -- `Ptr(T)` is a type and `Ptr(place)` is an unchecked address to that place: one word, like `Ref`,
    -- dispatched the same way. It is the only place a lifetime is deliberately written off.
    local ptrBuiltin = self:builtin("Ptr", { { name = "target" } }, function(engine, ctx, values, span)
        local ty = engine:asType(values[1], span)
        if not ty then D.reject("type-required", "Ptr needs an element type or a place", span) end
        S.checkRuntime(ty, span)
        return V.type(S.ptr(engine:canonicalize(ty)))
    end)
    ptrBuiltin.ptrOf = true
    declare(top, "Ptr", { kind = "word", name = "Ptr", def = ptrBuiltin })
    -- `Null(T)` is the null `Ptr(T)`. There is no null reference, so a pointer is the only thing it
    -- can make, and it needs runtime code because an address has no compile-time value.
    declare(top, "Null", { kind = "word", name = "Null",
        def = self:builtin("Null", { { name = "type" } }, function(engine, ctx, values, span)
            local ty = engine:asType(values[1], span)
            if not ty then D.reject("type-required", "Null needs an element type, as in Null(U8)", span) end
            local target = engine:canonicalize(ty)
            -- `Ptr(T)` is the runtime value, so the pointer is what must be representable, not `T`:
            -- a named record is a fine target even though it is not itself a runtime value.
            local pointer = S.ptr(target)
            S.checkRuntime(pointer, span)
            if ctx.mode ~= "residual" then
                D.reject("runtime-in-normalization",
                    "A null pointer exists only in compiled code", span)
            end
            return V.ir(ctx.builder:nullPtr(pointer), pointer)
        end) })
    declare(top, "Ref", { kind = "word", name = "Ref", def = refBuiltin })
    -- `OneOf(cases)` builds a sum type; the cases are a keyed schema whose fields are the
    -- alternatives. Nothing new is needed in the grammar: member selection names a constructor and
    -- keyed application matches on the tag.
    -- `Array(T, N)` is a type: N elements of T, with the length part of the type so a static index is
    -- checked while compiling and only a run-time index needs a bounds guard.
    declare(top, "Array", { kind = "word", name = "Array",
        -- The element is a type, so it is resolved on the type path: that is what lets a definition
        -- mention itself through an array and be told it is a type cycle rather than an eager demand.
        def = self:builtin("Array", { { name = "element", isType = true }, { name = "length" } },
            function(engine, ctx, values, span)
                local element = engine:asType(values[1], span)
                if not element then
                    D.reject("type-required", "Array needs an element type", span)
                end
                -- A named cell is what an open definition hands back while its own layout is being
                -- computed. It is a placeholder rather than a value, so it is allowed through here and
                -- judged by the cycle checker when the definition is sealed; anything else must be a
                -- type a value can actually have.
                if not S.hasNamed(element) then S.checkRuntime(element, span) end
                local length = values[2]
                if not V.isInteger(length) or length.ty ~= S.U32 then
                    D.reject("type-required", "Array needs a length as a literal U32", span)
                end
                if length.n < 1 then
                    D.reject("array-length", "An array holds at least one element", span)
                end
                return V.type(S.array(element, length.n))
            end) })
    -- `String` is the byte slice: text is an array of bytes with a runtime length, not a separate
    -- kind of value, so it needs no rule of its own.
    declare(top, "String", { kind = "value", name = "String", value = V.type(S.String) })
    -- `Slice(T)` is a type and `Slice(array)` is a view of that array. One word, dispatched on
    -- whether its argument is a type value or a storage array, exactly as `Ref` is.
    local sliceBuiltin = self:builtin("Slice", { { name = "source" } }, function(engine, ctx, values, span)
        local element = engine:asType(values[1], span)
        if not element then
            D.reject("type-required", "Slice needs an element type or an array", span)
        end
        S.checkRuntime(element, span)
        return V.type(S.slice(element))
    end)
    -- Only the argument expression says whether the view's storage outlives it, so `Slice` needs
    -- the expression as well as the value, exactly as `Ref` does.
    sliceBuiltin.sliceOf = true
    declare(top, "Slice", { kind = "word", name = "Slice", def = sliceBuiltin })
    declare(top, "OneOf", { kind = "word", name = "OneOf",
        def = self:builtin("OneOf", { { name = "cases" } }, function(engine, ctx, values, span)
            local cases = values[1]
            if V.tag(cases) ~= "schema" then
                D.reject("type-required", "OneOf needs a keyed schema of alternatives", span)
            end
            local def = cases.def
            local alternatives = {}
            for _, name in ipairs(def.fieldOrder) do alternatives[name] = def.fields[name] end
            if next(alternatives) == nil then
                D.reject("type-required", "OneOf needs at least one alternative", span)
            end
            return V.type(S.sum(alternatives))
        end) })
    return top
end

-- Compiles one module. A `use`d module is loaded first by the caller, which passes its own top so
-- this module's names resolve there.
function Eval:compile(program, loadedTop)
    local top = loadedTop or self:load(program)
    self.top = top
    -- Initialization is explicit and ordered, not an accident of which binding residual code reads first.
    self:initializeModule(program, top)
    local exports = { functions = {}, types = {} }
    local resolve = function(item) return self:resolveExportItem(item, top) end

    for _, item in ipairs(program.export.functions) do
        local value = resolve(item)
        if V.tag(value) ~= "word" then
            D.reject("function-required", "Exported function " .. item.name.text .. " is not a word", item.name.span)
        end
        exports.functions[#exports.functions + 1] = { name = item.name.text, word = value, span = item.name.span }
    end
    for _, item in ipairs(program.export.types) do
        local value = resolve(item)
        local ty = self:asType(value, item.name.span)
        -- Records and sums are both named structures with a C layout a host may need to build.
        if not ty or not (S.isRecord(ty) or S.isSum(ty)) then
            D.reject("type-required", "Exported type " .. item.name.text
                .. " is not a record or a sum type", item.name.span)
        end
        exports.types[#exports.types + 1] = { name = item.name.text, type = ty, span = item.span }
    end

    local compilation = { session = self, exports = exports, functions = {}, types = exports.types,
        foreigns = self.foreignOrder,
        modules = self.moduleStorages }
    for _, export in ipairs(exports.functions) do
        local instance = self:instanceFor(export.word.def, export.span, export.word.args)
        compilation.functions[#compilation.functions + 1] = { name = export.name, instance = instance, span = export.span }
    end
    if compilation.modules and #compilation.modules > 0 then
        compilation.modules.initialiser = self:moduleInitialiser(compilation.modules, program.span)
        compilation.functions[#compilation.functions + 1] = {
            name = "init", instance = compilation.modules.initialiser, span = program.span,
            initialiser = true,
        }
    end
    return compilation
end

-- One entry point that assigns every module-level object its starting value. The host calls it
-- before any exported function; it is never called implicitly.
function Eval:moduleInitialiser(modules, span)
    self.nextFn = self.nextFn + 1
    local target = "wordletinit"
    local builder = IR.builder({ id = target })
    local body = {}
    local fn = { id = target, role = Ir.Body, hidden = 0, inputs = {}, params = {}, results = {},
        body = body }
    local ctx = setmetatable({ session = self, mode = "residual", scope = self.top, span = span,
        builder = builder, body = body, fn = fn }, Ctx)
    for _, module in ipairs(modules) do
        local fields = {}
        if S.isArray(module.type) then
            for index, item in ipairs(module.initial.items or {}) do
                fields[index] = self:expression(ctx, item, module.type.element)
            end
        else
            for index, field in ipairs(module.type.fields) do
                fields[index] = self:expression(ctx, module.initial.fields[field.name], field.type)
            end
        end
        builder:store(body, Ir.Local(module.storage), builder:make(module.type, fields))
    end
    builder:emit(body, Ir.Return(S.list({})))
    local instance = { key = "module-init", def = nil, target = target, status = "done",
        results = {}, inputTypes = {}, inputPlan = {}, fn = fn, initialiser = true }
    self.instances[instance.key] = instance
    self.order[#self.order + 1] = instance
    return instance
end

function Eval:resolveExportItem(item, top)
    if item.kind == "ExportAlias" then
        return self:evalExpr(self:context("normalize", top, item.span), item.value)
    end
    local name = item.name.text
    local slot = lookup(top, name)
    if not slot then D.reject("unknown-name", "Unknown exported name: " .. name, item.name.span) end
    if slot.kind == "word" then return V.word(slot.def, {}, item.span) end
    return self:demand(slot, item.span).value
end

-- A module-level mutable record that runtime code refers to gets a named storage of its own. The
-- generated artifact declares one file-scope object per such binding and initialises them from
-- `wordlet_init`, which the host calls before using the exported functions.
function Eval:moduleObject(slot, span)
    if slot.module then return slot.module.object end
    local value = slot.value
    -- Module storage ids live in a disjoint range so they can never collide with the
    -- function-local storage ids the builder hands out.
    self.nextModule = (self.nextModule or 0) + 1
    local storage = Ir.Storage(MODULE_STORAGE_BASE + self.nextModule)
    if S.isArray(value.ty) then
        local array = V.array(value.ty, nil, Ir.Local(storage))
        array.module = true
        array.backing = value
        self.moduleStorages[#self.moduleStorages + 1] = {
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
    self.moduleStorages[#self.moduleStorages + 1] = {
        storage = storage, type = value.ty, initial = value, name = slot.name,
    }
    slot.module = { object = object }
    return object
end

-- Declares a `use`d module's namespace in the importing module's top scope.
function Eval:declareNamespace(top, name, value, span)
    return declare(top, name, { kind = "value", name = name, value = value }, span)
end

function Eval:exportedValue(program, name, top)
    for _, item in ipairs(program.export.functions) do
        if item.name.text == name then return self:resolveExportItem(item, top) end
    end
    D.reject("unknown-name", "Unknown exported function: " .. tostring(name))
end

function Eval:exportedWord(slot, span, name)
    if slot.kind == "word" then return V.word(slot.def, {}, span) end
    local demanded = self:demand(slot, span)
    local value = demanded.value
    if V.tag(value) ~= "word" then
        D.reject("function-required", "Exported function " .. tostring(name) .. " is not a word", span)
    end
    return value
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

function Eval:demand(slot, span)
    if slot.kind ~= "value" or slot.value ~= nil then return slot end
    local siblings = slot.binders or { slot }
    if slot.demanding then D.reject("initializer-cycle", "Eager value cycle through " .. slot.name, span) end
    for _, sibling in ipairs(siblings) do
        sibling.demanding = true
        -- A binding that its own type computation demands reserves a cell, so the definition can refer
        -- to itself through an indirection instead of forcing its layout.
        if sibling.cell == nil then
            self.nextTypeCell = self.nextTypeCell + 1
            sibling.cell = sibling.name .. "#" .. tostring(self.nextTypeCell)
        end
        sibling.open = true
    end
    local ctx = self:context("normalize", slot.scope, slot.decl.span)
    -- A top-level initializer is compile-time execution over concrete values, so module storage is
    -- readable and writable here even though residual specialization must not touch it. Nested
    -- demands keep the flag set and the outermost demand restores it.
    local savedDemand = self.moduleDemand
    self.moduleDemand = true
    local ok, result = pcall(self.evalValueDef, self, ctx, slot.decl.def)
    self.moduleDemand = savedDemand
    for _, sibling in ipairs(siblings) do
        sibling.demanding = nil
        sibling.open = false
    end
    if not ok then error(result, 0) end
    -- Several binders produce a result vector; distribute it as a local result-list binding does,
    -- filling a missing value with Unit.
    local values = self:expand(result)
    for index, sibling in ipairs(siblings) do
        sibling.value = values[index] or V.unit()
    end
    for _, sibling in ipairs(siblings) do self:sealCell(sibling, span) end
    return slot
end

-- Top-level initialization runs once, eagerly, in declaration order. The reference interpreter and
-- the compiler both call this, so they observe the same sequence of reads and mutations, and a
-- mutating initializer cannot depend on which binding happened to be referenced first.
function Eval:initializeModule(program, top)
    for _, decl in ipairs(program.declarations) do
        if decl.kind == "ValueDecl" then
            local binder = decl.def.binders[1]
            local slot = binder and lookup(top, binder.name.text)
            if slot and slot.atTop then self:demand(slot, decl.span) end
        end
    end
end

-- Seals a reserved cell with the type the binding computed. A cell that nothing referred to needs no
-- definition, and a definition that mentions its own cell by value rather than through a reference
-- has no finite layout.
function Eval:sealCell(slot, span)
    span = span or (slot.decl and slot.decl.span)
    local ty = self:asType(slot.value, span)
    if self.referencedCells == nil then self.referencedCells = {} end
    if ty then
        self.typeCells[slot.cell] = ty
        self.namedByMeaning = self.namedByMeaning or {}
        self.namedByMeaning[S.encode(ty)] = S.named(slot.cell)
    end
    if ty and self.referencedCells[slot.cell] then
        self:checkNoValueCycle(ty, slot, span)
    end
    return ty
end

-- A cell may only appear behind a reference. Every other occurrence would embed the definition in
-- itself, which no finite layout can represent.
function Eval:checkNoValueCycle(ty, slot, span, seen)
    seen = seen or {}
    if S.isNamed(ty) then
        D.reject("type-cycle", "Type " .. slot.name .. " contains itself by value; a recursive type "
            .. "needs an indirection boundary, as in Ref(" .. slot.name .. ") or Ptr(" .. slot.name
            .. ")", span)
    end
    -- A reference, a raw pointer and a slice are all indirection boundaries: the first two are an
    -- address and a slice is an address with a length, so none of them depends on the size of what it
    -- names. A signature and a view hold no storage of their own. Everything else would embed the
    -- definition in itself.
    if S.isRef(ty) or S.isPtr(ty) or S.isSlice(ty) or S.isSig(ty) or S.isView(ty) then return end
    if seen[ty] then return end
    seen[ty] = true
    if S.isRecord(ty) then
        for _, field in ipairs(ty.fields) do self:checkNoValueCycle(field.type, slot, span, seen) end
    elseif S.isTuple(ty) then
        for _, item in ipairs(ty.fields) do self:checkNoValueCycle(item, slot, span, seen) end
    elseif S.isArray(ty) then
        -- An element is embedded by value, so a cycle that crosses an array crosses no boundary at all.
        self:checkNoValueCycle(ty.element, slot, span, seen)
    elseif S.isTaggedType(ty) then
        for _, field in ipairs(S.alternatives(ty)) do self:checkNoValueCycle(field.type, slot, span, seen) end
    elseif S.isOwned(ty) then
        self:checkNoValueCycle(S.environmentOf(ty), slot, span, seen)
    end
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
function Eval:evalList(ctx, exprs)
    local values = {}
    for index, expr in ipairs(exprs) do
        local value = self:evalExpected(ctx, expr, ctx.expectedResult)
        if index < #exprs then
            values[#values + 1] = self:first(value)
        else
            for _, item in ipairs(self:expand(value)) do values[#values + 1] = item end
        end
    end
    return values
end

-- Materialisation -------------------------------------------------------------------------------

-- A record value or object becomes an immutable Make of its fields.
function Eval:recordExpr(ctx, value)
    -- A record that has not demanded a place is already its construction expression, so crossing a
    -- boundary copies that immutable Make instead of reading each field back and rebuilding it.
    if value.expr then return value.expr end
    local ty = value.ty
    local fields = {}
    for index, field in ipairs(ty.fields) do
        fields[index] = self:fieldExpr(ctx, value, field.name)
    end
    return ctx.builder:make(ty, fields)
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

function Eval:fieldExpr(ctx, value, name)
    if V.tag(value) == "record" then return self:expression(ctx, value.fields[name]) end
    local ty = S.field(value.ty, name)
    -- A field of an unmaterialised record is a pure projection of its construction expression; once a
    -- demand clears that expression, and for a spilled SSA value, storage is read instead.
    if value.expr then return V.ir(ctx.builder:get(value.expr, name, ty), ty) end
    local place = Ir.Project(value.place, Ir.Field(name))
    local read = ctx.builder:read(ctx.body, ty, place)
    return ctx.builder:ref(read, ty)
end

-- Wraps a payload in its alternative. Under the interpreter the payload is a value; in residual
-- code it becomes ConstructVariant, which the backend lowers to a tag plus a union member.
function Eval:makeVariant(ctx, ctor, payload, span)
    -- A Unit alternative carries no payload, but the frontend value still holds the Unit value so
    -- that knownness and matching treat it like any other alternative.
    local unit = ctor.caseType == S.Unit and payload == nil
    local value = payload or V.unit()
    if ctx.mode ~= "residual" then
        return V.variant(ctor.sum, ctor.case, value)
    end
    local id = ctx.builder:valueId()
    local payloadExpr
    if not unit then payloadExpr = self:expression(ctx, payload, ctor.caseType) end
    ctx.builder:emit(ctx.body, Ir.ConstructVariant(id, ctor.sum, ctor.case, payloadExpr))
    return V.variant(ctor.sum, ctor.case, value, ctx.builder:ref(id, ctor.sum))
end

-- `value { case = handler, ... }`: every alternative must be covered. A value whose tag is known
-- selects one handler; an opaque variant tests the tag and joins the arms.
function Eval:evalMatch(ctx, base, expr, span)
    span = span or expr.span
    local handlers, order = {}, {}
    for _, field in ipairs(expr.fields) do
        local name = field.name.text
        if not S.caseOf(base.ty, name) then
            D.reject("unknown-member", "Sum type has no alternative " .. name, field.name.span)
        end
        if handlers[name] ~= nil then
            D.reject("duplicate", "Alternative " .. name .. " is handled twice", field.name.span)
        end
        handlers[name] = self:evalExpr(ctx, field.value)
        order[#order + 1] = name
    end
    for _, name in ipairs(S.casesOf(base.ty)) do
        if handlers[name] == nil then
            D.reject("variant-match", "Matching must handle every alternative, including " .. name,
                expr.span)
        end
    end
    for _, name in ipairs(order) do
        if not (V.tag(handlers[name]) == "word" or V.tag(handlers[name]) == "closure"
            or V.tag(handlers[name]) == "method") then
            D.reject("callable-required", "A match handler must be callable", expr.span)
        end
    end

    if V.tag(base) == "variant" then
        -- The tag is known here, so the other alternatives are not evaluated at all.
        local payload = base.payload
        if payload == nil then payload = V.unit() end
        return self:applyAny(ctx, handlers[base.case], { payload }, span)
    end

    if ctx.mode ~= "residual" then
        D.reject("runtime-in-normalization", "Matching an opaque variant needs runtime code", span)
    end
    return self:matchResidual(ctx, base, handlers, span)
end

function Eval:applyAny(ctx, callee, args, span)
    local tag = V.tag(callee)
    if tag == "word" then return self:apply(ctx, callee, args, span) end
    if tag == "closure" then return self:applyClosure(ctx, callee.plan, nil, args, span, callee.bound) end
    if tag == "method" then return self:applyMethod(ctx, callee, args, span) end
    if tag == "variant" and callee.ty and S.isTagged(callee.ty) then
        return self:applyTagged(ctx, callee, args, span)
    end
    if tag == "ir" and S.isTagged(callee.ty) then
        return self:applyTagged(ctx, callee, args, span)
    end
    D.reject("callable-required", "Only words, methods and closures can be applied", span)
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
    if tag == "float" then return a.n == b.n end
    if tag == "unit" then return true end
    if tag == "string" then return a.bytes == b.bytes end
    return false
end

function Eval:matchResidual(ctx, base, handlers, span)
    local builder = ctx.builder
    local variant = sumValueId(base)
    local names = S.casesOf(base.ty)
    local pieces, resultTypes = {}, nil
    for _, name in ipairs(names) do
        local arm = {}
        local armCtx = ctx:arm(arm)
        local caseType = S.caseOf(base.ty, name)
        local args
        if caseType == S.Unit then
            -- The handler still takes one (erased) Unit parameter, so the arity matches; the value
            -- itself is never materialised.
            args = { V.unit() }
        else
            local id = builder:valueId()
            builder:emit(arm, Ir.VariantPayload(id, variant, base.ty, name))
            args = { V.ir(builder:ref(id, caseType), caseType) }
        end
        -- A handler is a callable, so it may return a result vector; the match forwards it.
        local values = self:expand(self:applyAny(armCtx, handlers[name], args, span))
        if resultTypes == nil then
            resultTypes = {}
            for index, value in ipairs(values) do resultTypes[index] = value.ty end
        elseif #values ~= #resultTypes then
            D.reject("branch-result", "Every arm of a match must produce the same number of results: "
                .. #resultTypes .. " and " .. #values, span)
        else
            for index, value in ipairs(values) do
                if value.ty ~= resultTypes[index] then
                    D.reject("branch-result", "Every arm of a match must produce the same type: "
                        .. S.encode(resultTypes[index]) .. " and " .. S.encode(value.ty), span)
                end
            end
        end
        pieces[#pieces + 1] = { name = name, list = arm, ctx = armCtx, values = values,
            terminated = armCtx.terminated }
    end
    -- One slot per result, so a match may yield a result vector rather than only one value.
    local places = {}
    for index, ty in ipairs(resultTypes) do
        places[index] = Ir.Local(builder:var(ctx.body, ty, nil))
    end
    for _, piece in ipairs(pieces) do
        if not piece.terminated then
            for index, value in ipairs(piece.values) do
                builder:store(piece.list, places[index],
                    self:expression(piece.ctx, value, resultTypes[index]))
            end
        end
    end
    -- One switch on the tag. The last alternative carries the fallback flag and is emitted as C's
    -- `default`, so the branch is total and a dense alternative set lowers to a jump table rather
    -- than a chain of compares.
    local cases = {}
    for index, piece in ipairs(pieces) do
        cases[index] = Ir.Case(piece.name, index == #pieces, S.list(piece.list))
    end
    builder:emit(ctx.body, Ir.Switch(variant, base.ty, S.list(cases)))
    local out = {}
    for index, ty in ipairs(resultTypes) do
        out[index] = V.ir(builder:ref(builder:read(ctx.body, ty, places[index]), ty), ty)
    end
    if #out == 1 then return out[1] end
    return V.results(out)
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

function Eval:placeRoot(place)
    while place and place.kind == "Project" do place = place.base end
    return place
end

-- A named cell resolves to the definition it reserved. Every other type is already its own meaning,
-- so this is the one place recursion has to be unwound for inspection.
function Eval:resolveType(ty, span)
    if S.isNamed(ty) then
        local cell = self.typeCells[ty.cell]
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
    local named = self.namedByMeaning and self.namedByMeaning[S.encode(ty)]
    if named then return named end
    if S.isPtr(ty) then
        local target = self:canonicalize(ty.target)
        if target ~= ty.target then return S.ptr(target) end
        return ty
    end
    if S.isRef(ty) then
        local target = self:canonicalize(ty.target)
        if target ~= ty.target then return S.ref(target) end
    end
    return ty
end

-- The record type a reference points at, unwinding the cell a recursive definition reserved.
-- The type an address points at, unwinding the cell a recursive definition reserved. A reference and a
-- raw pointer name their target the same way, so one unwinding serves both.
function Eval:pointeeType(ty)
    local target = S.environmentOf(ty.target)
    if S.isNamed(target) then target = self:resolveType(target) end
    return target
end

Eval.refTargetType = Eval.pointeeType

function Eval:refTargetType(ty)
    local target = S.environmentOf(ty.target)
    if S.isNamed(target) then target = self:resolveType(target) end
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
    -- Module storage is a named file-scope object, so it outlives every activation.
    if value.module or (value.schema and value.schema.module) then return "module" end
    local root = self:placeRoot(value.place)
    if value.enclosing or (root and root.kind == "Captured") then return "enclosing" end
    return nil
end

-- A reference names a place, so selecting or storing through it selects that place. A frontend
-- reference therefore behaves exactly like the instance it names.
function Eval:placeObject(value)
    if V.tag(value) ~= "ref" then return nil end
    local target = S.environmentOf(self:resolveType(value.ty.target))
    local schema = value.schema
    if not schema and S.isRecord(target) then
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
function Eval:derefPlace(ctx, value, span)
    -- An address is a pointer; `value.place` is where that pointer lives, so the target is
    -- one dereference further on. The pointee type travels with the place, like every other typed
    -- IR node, so the verifier needs no type-cell table to check it.
    local pointee = S.environmentOf(self:refTargetType(value.ty))
    if value.place then return Ir.Deref(value.place, pointee) end
    if ctx.mode ~= "residual" then
        D.reject("runtime-in-normalization", "A runtime reference needs runtime code", span)
    end
    local storage = ctx.builder:var(ctx.body, value.ty, self:expression(ctx, value, value.ty))
    return Ir.Deref(Ir.Local(storage), pointee)
end

-- `Ref(x)`: a reference to the place `x` names. A file-scope binding is module storage, which the
-- interpreter already holds as a record and residual code promotes to a named object, so both modes
-- classify it the same way.
-- A binding whose initialiser is a schema literal is a type definition, so a demand that arrives
-- while it is open is the recursion knot rather than a value demand.
function Eval:isTypeDefinition(slot)
    local def = slot.decl and slot.decl.def
    if not def or #def.binders ~= 1 or #def.values ~= 1 then return false end
    local value = def.values[1]
    -- A schema literal or a type-constructor application denotes a type; anything else is a value,
    -- and a value that demands itself is an initializer cycle rather than a recursive type.
    return value.kind == "SchemaExpr" or value.kind == "Apply"
end

-- Where a place expression's storage comes from: "module" for a file-scope binding, "enclosing" for
-- storage that belongs to an enclosing activation, and nil for storage this activation owns.
function Eval:placeOrigin(ctx, expr)
    if expr.kind == "Reference" then
        local slot = lookup(ctx.scope, expr.name.text)
        if not slot then return nil end
        if slot.atTop then
            -- A type or a scalar binding has no storage to name.
            local held = self:demand(slot, expr.span).value
            if held and (V.tag(held) == "record" or V.tag(held) == "array") then return "module" end
            return nil
        end
        if slot.kind == "param" then return "enclosing" end
        local record = slot.record
        if record and record.module then return "module" end
        if record and record.enclosing then return "enclosing" end
        return nil
    end
    if expr.kind == "FieldSelect" or expr.kind == "IndexExpr" then
        return self:placeOrigin(ctx, expr.base)
    end
    return nil
end

-- `Ptr(place)` takes the address of a place and writes off its lifetime. Unlike a reference there is no
-- target rule to check, and that is the point: from here the program is responsible, so the one place
-- a lifetime is dropped is spelled rather than inferred.
function Eval:evalPtr(ctx, expr)
    if expr.kind == "Reference" then
        local slot = lookup(ctx.scope, expr.name.text)
        -- `Ptr(Node)` inside Node's own definition must not demand Node's layout: a pointer is an
        -- indirection boundary exactly as a reference is, so it names the cell the definition
        -- reserved and the recursion stays finite.
        if slot and slot.open and slot.value == nil and slot.cell and self:isTypeDefinition(slot) then
            if self.referencedCells == nil then self.referencedCells = {} end
            self.referencedCells[slot.cell] = true
            return V.type(S.ptr(S.named(slot.cell)))
        end
        local value = slot and self:demand(slot, expr.span).value or nil
        local held = value and self:asType(value, expr.span) or nil
        if held then return V.type(S.ptr(self:canonicalize(held))) end
    end
    -- Only a non-place expression can be a type, and evaluating a place would read it: taking an
    -- address must not also load what it addresses.
    if expr.kind ~= "Reference" and expr.kind ~= "FieldSelect" and expr.kind ~= "IndexExpr" then
        local asType = self:asType(self:evalExpr(ctx, expr), expr.span)
        if asType then return V.type(S.ptr(self:canonicalize(asType))) end
        D.reject("type-required", "Ptr needs an element type or a place to address", expr.span)
    end
    if ctx.mode ~= "residual" then
        D.reject("runtime-in-normalization", "A raw pointer exists only in compiled code", expr.span)
    end
    -- A place expression names storage directly, so the address is that place and nothing is read.
    local ok, reached = pcall(function() return self:placeOf(ctx, expr, expr.span) end)
    if not (ok and reached.place) then
        -- A local binding to an instance is an alias, so its storage is what the address names; that
        -- storage is created here when the instance only exists as a value so far.
        local held = self:evalExpr(ctx, expr)
        local tag = V.tag(held)
        if tag == "record" then
            reached = { place = self:recordPlace(ctx, held, expr.span), ty = held.ty }
        elseif tag == "array" then
            reached = { place = self:arrayPlace(ctx, held, expr.span), ty = held.ty }
        end
    end
    if not reached.place then
        D.reject("not-a-place", "Ptr needs an element type or a place to address", expr.span)
    end
    if not reached.place then
        D.reject("not-a-place", "Ptr needs a place to address", expr.span)
    end
    local target = self:canonicalize(reached.ty)
    local pointer = S.ptr(target)
    return V.ir(ctx.builder:addr(reached.place, pointer), pointer)
end

function Eval:evalRef(ctx, expr)
    local slot
    if expr.kind == "Reference" then
        slot = lookup(ctx.scope, expr.name.text)
        -- `Ref(Node)` inside Node's own definition must not demand Node's layout: it refers to the
        -- cell that definition reserved, which is what makes the recursion finite.
        if slot and slot.open and slot.value == nil and slot.cell and self:isTypeDefinition(slot) then
            if self.referencedCells == nil then self.referencedCells = {} end
            self.referencedCells[slot.cell] = true
            return V.type(S.ref(S.named(slot.cell)))
        end
    end
    -- A place expression names storage directly, so the reference is that place.
    if expr.kind == "Reference" or expr.kind == "FieldSelect" or expr.kind == "IndexExpr" then
        local held = slot and self:demand(slot, expr.span).value or nil
        local heldType = held and self:asType(held, expr.span) or nil
        if heldType then return V.type(S.ref(self:canonicalize(heldType))) end
        local origin = self:placeOrigin(ctx, expr)
        -- What the place turned out to be decides as much as the route the name spells. A place
        -- reached through a reference to module storage is module storage, and a caller holding its own
        -- reference to one does not change that; the route alone says nothing, so the place is asked.
        local ok, reached = pcall(function() return self:placeOf(ctx, expr, expr.span) end)
        if ok and not reached.place and reached.concrete ~= nil then
            -- The place exists as a compile-time value with no storage of its own, which is how the
            -- interpreter holds a module array's element. Taking an address needs an address, and only
            -- compiled code gives one, so say that rather than blaming the target's lifetime.
            D.reject("runtime-in-normalization",
                "A reference needs storage here, and this place has none while interpreting; compiling"
                .. " the program gives it one", expr.span)
        end
        if ok and reached.place then
            local container = reached.container
            local isModule = origin == "module" or (container ~= nil and container.module == true)
            -- A container whose provenance is not known here is treated as enclosing, which is the
            -- conservative reading: it cannot be proven to be module storage, so it must not escape.
            local isEnclosing = origin == "enclosing"
                or (container ~= nil and (container.enclosing == true or container.retaining == true))
            if isModule or isEnclosing then
                local made = V.ref(S.ref(self:canonicalize(reached.ty)), reached.place, nil,
                    isEnclosing, reached.value)
                -- Building the reference is just an address, which is how a recursive structure is
                -- built; reading or writing through it is what runtime code does.
                made.module = isModule
                return made
            end
        end
    end
    local value = self:evalExpr(ctx, expr)
    local ty = self:asType(value, expr.span)
    if ty then return V.type(S.ref(self:canonicalize(ty))) end
    if slot and slot.atTop and V.tag(value) == "record" then
        -- A file-scope binding has an identity that outlives every activation, so a reference to it
        -- is a reference to named module storage whichever mode built it.
        return self:makeReference(ctx, self:moduleObject(slot, expr.span), expr.span)
    end
    return self:makeReference(ctx, value, expr.span)
end

-- A reference to an enclosing owner cannot outlive that activation, so it and anything holding it
-- stay inside.
function Eval:refEscapeMessage()
    return "A reference to a place in an enclosing activation cannot escape it; use it where the "
        .. "place is still live, or name module storage instead"
end

function Eval:makeReference(ctx, target, span)
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
    return V.ref(S.ref(self:canonicalize(target.ty)), target.place, target.schema,
        kind == "enclosing", held)
end

-- Arrays -----------------------------------------------------------------------------------------
-- An array literal takes its type from its elements, or from the annotation it is checked against,
-- which is what an empty literal needs. A residual array owns fresh local storage, so its elements
-- are writable and a read goes to that storage rather than to the values it was built from.

function Eval:evalArray(ctx, expr, expected)
    local items = {}
    for index, item in ipairs(expr.items) do items[index] = self:evalExpr(ctx, item) end
    local ty = S.isArray(expected) and expected or nil
    if not ty then
        if #items == 0 then
            D.reject("type-required",
                "An empty array literal needs an annotation that gives its element type and length",
                expr.span)
        end
        local element = items[1].ty
        for _, item in ipairs(items) do
            if item.ty ~= element then
                D.reject("type-mismatch", "Array elements must share one type: " .. S.encode(element)
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
    if ctx.mode ~= "residual" then return V.array(ty, items) end
    local exprs, borrowed = {}, false
    for index, item in ipairs(items) do
        exprs[index] = self:expression(ctx, item, ty.element)
        if self:isBorrowed(item) then borrowed = true end
    end
    -- The Make is the value until an element is addressed (an index or a view). `body` is where that
    -- spill goes, so a demand from inside an arm still reaches storage from the outer scope.
    return V.array(ty, nil, nil, borrowed, ctx.builder:make(ty, exprs), ctx.body)
end

-- The place an array value's elements live at. A value that only exists as an SSA value is spilled
-- into storage once, which is what lets a parameter or a call result be indexed.
-- `Slice(array)` is a runtime-length view of an array: the address of its first element and its
-- length. The view borrows the storage it names, so the lifetime rules of a reference apply to it.
function Eval:evalSlice(ctx, expr)
    -- `Slice(Node)` inside Node's own definition must not demand Node's layout: a slice is a pointer
    -- and a length, so its size does not depend on its element either. It names the cell the
    -- definition reserved, exactly as a pointer or a reference does.
    if expr.kind == "Reference" then
        local slot = lookup(ctx.scope, expr.name.text)
        if slot and slot.open and slot.value == nil and slot.cell and self:isTypeDefinition(slot) then
            if self.referencedCells == nil then self.referencedCells = {} end
            self.referencedCells[slot.cell] = true
            return V.type(S.slice(S.named(slot.cell)))
        end
    end
    local container = self:containerOf(ctx, expr, expr.span)
    -- `Slice(T)` is a type, exactly as `Ref(T)` is; only a non-type argument names a view.
    local element = self:asType(container.value, expr.span)
    if element then
        S.checkRuntime(element, expr.span)
        return V.type(S.slice(self:canonicalize(element)))
    end
    local ty = container.ty
    if not S.isArray(ty) then
        D.reject("type-mismatch", "Slice needs an array, found " .. S.encode(ty or S.Unit), expr.span)
    end
    -- A reference to module storage may leave the activation; a view of anything else may not.
    local tied = not (container.container and container.container.module)
    if ctx.mode ~= "residual" then
        local held = container.value
        if not (type(held) == "table" and V.tag(held) == "array" and held.items) then
            D.reject("runtime-in-normalization", "A runtime slice must be built in runtime code", expr.span)
        end
        -- A view names storage rather than being storage, so a view of module storage is not a
        -- compile-time constant: folding it would bake the read into the output. Module
        -- initialization and the reference interpreter execute over that storage, so for them it
        -- is the value; elsewhere the call is compiled instead.
        if container.container and container.container.module
            and not (ctx.session.run or ctx.session.moduleDemand) then
            D.reject("runtime-in-normalization",
                "A view of module storage is built where it is used, not folded while compiling",
                expr.span)
        end
        return V.slice(S.slice(ty.element), held, 0, ty.length, tied)
    end
    if not container.place then
        if not container.value then
            D.reject("not-a-place", "Slice needs an array with storage", expr.span)
        end
        container.place = self:arrayPlace(ctx, container.value, expr.span)
    end
    -- Both halves of a view are pure: an address and a length need no storage of their own.
    local data = ctx.builder:addr(Ir.Index(container.place, ctx.builder:u32(0), ty.element),
        S.ref(ty.element))
    local view = ctx.builder:make(S.slice(ty.element), { data, ctx.builder:u32(ty.length) })
    return V.ir(view, S.slice(ty.element), tied, container.place)
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

function Eval:arrayPlace(ctx, value, span)
    if value.place then
        -- A demand for a place invalidates the construction expression; storage is authoritative.
        value.expr = nil
        return value.place
    end
    if ctx.mode ~= "residual" then
        D.reject("runtime-in-normalization", "A runtime array needs runtime code", span)
    end
    -- The spill goes into the list the value was built in, so it dominates every use even when the
    -- demand comes from inside an arm.
    local storage = ctx.builder:var(value.body or ctx.body, value.ty,
        self:expression(ctx, value, value.ty))
    local place = Ir.Local(storage)
    -- A compile-time value is shared and immutable, so it never remembers a spill: another mode or
    -- capture reading the same value must not see a `place` a residual compilation gave it.
    if not value.items then value.place = place end
    value.expr = nil
    return place
end

-- The place a record value's fields live at. A record that only exists as an SSA value is spilled
-- into storage once, which is what lets a call result be written through its fields.
function Eval:recordPlace(ctx, value, span)
    if value.place then
        -- A demand for a place invalidates the construction expression: storage is authoritative
        -- from here on, so a later store must be visible to every read. A spilled `ir` keeps its SSA
        -- expression as its representation.
        if V.tag(value) == "object" then value.expr = nil end
        return value.place
    end
    if ctx.mode ~= "residual" then
        D.reject("runtime-in-normalization", "A runtime record needs runtime code", span)
    end
    -- A value that only exists as an SSA value is spilled once; the place is initialized from its
    -- expression and storage is authoritative afterwards. The spill goes into the list the value was
    -- built in, so it dominates every use even when the demand comes from inside an arm.
    local storage = ctx.builder:var(value.body or ctx.body, value.ty,
        self:expression(ctx, value, value.ty))
    local place = Ir.Local(storage)
    -- A compile-time record is shared and immutable, so it never remembers a spill: another mode or
    -- capture reading the same value must not see a `place` a residual compilation gave it.
    if not value.fields then value.place = place end
    if V.tag(value) == "object" then value.expr = nil end
    return place
end

-- An array expression. A value backed by storage is read whole, which is a struct copy in C; a
-- compile-time array is built from its elements.
function Eval:arrayExpr(ctx, value)
    -- A residual literal that has not demanded a place is already its construction expression.
    if value.expr then return value.expr end
    if not value.items then
        D.bug("array-value", "An array with neither storage nor elements has no representation")
    end
    local exprs = {}
    for index, item in ipairs(value.items) do
        exprs[index] = self:expression(ctx, item, value.ty.element)
    end
    return ctx.builder:make(value.ty, exprs)
end

function Eval:requireArray(value, span)
    if not S.isArray(value.ty) then
        D.reject("type-mismatch", "Expected an array but found " .. S.encode(value.ty or S.Unit), span)
    end
    return value.ty
end

-- The place an lvalue expression names, without reading it. Every assignable target and every
-- reference target is a chain of selections over a root, so this is the one place that knows how to
-- A name the reference specifies but this implementation does not provide is a known-but-unimplemented
-- feature rather than an unknown name. Nothing is in that state now that F64 exists, so the table is
-- empty; a name goes here when its rules are written down and its implementation is not.
local UNIMPLEMENTED_NAMES = {}
function Eval:unknownName(name, span)
    local note = UNIMPLEMENTED_NAMES[name]
    if note then D.todo("unimplemented", note, span) end
    D.reject("unknown-name", "Unknown name: " .. name, span)
end

-- reach storage. A concrete result describes a compile-time container; a residual one is an
-- `Ir.Place` with the type it refers to.
--   { concrete = "field", record = <value>, name = <field>, ty = <ty> }
--   { concrete = "index", array = <value>, index = <n>, ty = <ty> }
--   { place = <Ir.Place>, ty = <ty> }
function Eval:placeOf(ctx, expr, span)
    if expr.kind == "Reference" then
        local slot = lookup(ctx.scope, expr.name.text)
        if not slot then self:unknownName(expr.name.text, expr.name.span) end
        if slot.atTop then
            -- The binding is demanded first: its named storage is built from the value it computes.
            local demanded = self:demand(slot, expr.name.span)
            local held = demanded.value
            if not held or (V.tag(held) ~= "record" and V.tag(held) ~= "array") then
                D.reject("not-a-place", "Only a record or an array instance is storage: "
                    .. expr.name.text, expr.name.span)
            end
            local object = self:moduleObject(demanded, expr.name.span)
            -- `backing` is the value the storage stands for, which is what normalize code reads;
            -- `container` is the object whose storage holds the selection, which is what the borrow
            -- rules inspect.
            return { place = object.place, ty = object.ty, concrete = object.backing,
                value = object.backing, container = object }
        end
        if slot.kind == "concrete-field" then
            return { concrete = "field", record = slot.record, name = slot.name, ty = slot.ty }
        end
        if slot.kind == "concrete-index" then
            return { concrete = "index", array = slot.array, index = slot.index, ty = slot.ty }
        end
        if slot.kind == "field" then return { place = slot.place, ty = slot.ty } end
        if slot.kind == "param" then return { place = Ir.Local(slot.storage), ty = slot.ty } end
        D.reject("not-a-place", "Only storage can be a place: " .. expr.name.text, expr.name.span)
    end
    if expr.kind == "FieldSelect" then
        local container = self:derefContainer(ctx, self:containerOf(ctx, expr.base, expr.base.span),
            expr.span)
        local name = expr.field.text
        local target = self:resolveType(S.environmentOf(container.ty))
        local ty = S.field(target, name)
        if not ty then D.reject("unknown-member", "Record has no field " .. name, expr.field.span) end
        local base = container.place
        if ctx.mode == "residual" and container.value
            and (not base or (V.tag(container.value) == "object" and container.value.expr)) then
            base = self:recordPlace(ctx, container.value, expr.span)
        end
        local place = base and Ir.Project(base, Ir.Field(name)) or nil
        local held = container.concrete
        if type(held) == "table" and held.tag == "record" and held.fields then
            return { concrete = "field", record = held, name = name, ty = ty,
                place = place, value = held.fields[name], container = container.container }
        end
        if not place or ctx.mode ~= "residual" then
            D.reject("runtime-in-normalization",
                "A field of run-time storage is only reachable from runtime code", expr.span)
        end
        return { place = place, ty = ty, container = container.container }
    end
    if expr.kind == "IndexExpr" then
        local base = self:containerOf(ctx, expr.base, expr.base.span)
        -- An unchecked pointer is indexed by address, before any dereference: `p[i]` is the element at
        -- `p + i`, so the pointer's target is that element rather than a container to index into.
        -- Dereferencing first, the way a reference is handled, would read the element and then try to
        -- index it.
        if base.ty and S.isPtr(base.ty) then
            local element = self:pointeeType(base.ty)
            local index = self:evalExpr(ctx, expr.index)
            self:requireType(index, S.U32, expr.index.span)
            if ctx.mode ~= "residual" then
                D.reject("runtime-in-normalization", "A pointer element needs runtime code", expr.span)
            end
            local view = self:containerExpr(ctx, base)
            local indexExpr = self:expression(ctx, index, S.U32)
            -- No length and so no guard: that is the whole difference from the slice index below.
            return { place = ctx.builder:ptrIndex(view, indexExpr, element), ty = element }
        end
        local container = self:derefContainer(ctx, base, expr.span)
        if S.isSlice(container.ty) then
            local element = container.ty.element
            local index = self:evalExpr(ctx, expr.index)
            self:requireType(index, S.U32, expr.index.span)
            local count = self:sliceCount(container.value)
            if V.isKnown(index) and V.isInteger(index) and count then
                if index.n >= count then
                    D.reject("index-range", "Index " .. tostring(index.n) .. " is outside a slice of "
                        .. "length " .. tostring(count), expr.span)
                end
                local held = self:sliceElement(container.value, index.n)
                if held and ctx.mode ~= "residual" then
                    return { concrete = "element", value = held, ty = element, readonly = true }
                end
            end
            if ctx.mode ~= "residual" then
                D.reject("runtime-in-normalization", "A run-time slice index needs runtime code", expr.span)
            end
            local view = self:containerExpr(ctx, container)
            local indexExpr = self:expression(ctx, index, S.U32)
            -- A run-time index is checked before it is used, exactly as an array's is.
            ctx.builder:emit(ctx.body, Ir.Trap(ctx.builder:bin("Ge", indexExpr,
                ctx.builder:sliceLength(view, S.U32), S.Bool), "index-range"))
            return { place = ctx.builder:sliceIndex(view, indexExpr, element), ty = element,
                readonly = true }
        end
        if not S.isArray(container.ty) then
            D.reject("type-mismatch",
                "Expected an array but found " .. S.encode(container.ty or S.Unit), expr.span)
        end
        local index = self:evalExpr(ctx, expr.index)
        -- A narrower integer index widens, which is free.
        self:requireType(index, S.U32, expr.index.span)
        local length, element = container.ty.length, container.ty.element
        if V.isKnown(index) and V.isInteger(index) then
            if index.n >= length then
                D.reject("index-range", "Index " .. tostring(index.n) .. " is outside an array of "
                    .. "length " .. tostring(length), expr.span)
            end
            -- A place needs a builder, so only residual code builds one; normalize code either uses
            -- the value it names or reports that this storage is runtime-only.
            local base = container.place
            if ctx.mode == "residual" and container.value
                and (not base or (V.tag(container.value) == "array" and container.value.expr)) then
                base = self:arrayPlace(ctx, container.value, expr.span)
            end
            local place = (base and ctx.mode == "residual")
                and Ir.Index(base, ctx.builder:u32(index.n), element) or nil
            local held = container.concrete
            if type(held) == "table" and held.tag == "array" and held.items then
                return { concrete = "index", array = held, index = index.n, ty = element,
                    place = place, value = held.items[index.n + 1], container = container.container }
            end
            if not place or ctx.mode ~= "residual" then
                D.reject("runtime-in-normalization",
                    "An element of run-time storage is only reachable from runtime code", expr.span)
            end
            return { place = place, ty = element, container = container.container }
        end
        if ctx.mode ~= "residual" then
            D.reject("runtime-in-normalization", "A run-time index needs runtime code", expr.span)
        end
        -- A run-time index is checked before it is used, exactly as a run-time divisor is.
        local indexExpr = self:expression(ctx, index, S.U32)
        ctx.builder:emit(ctx.body, Ir.Trap(ctx.builder:bin("Ge", indexExpr,
            ctx.builder:u32(length), S.Bool), "index-range"))
        local place = container.place or self:arrayPlace(ctx, container.value, expr.span)
        -- The container travels too: `Ref(r[i])` has to be able to see that the element it names is
        -- in module storage, even when the route to it is a run-time index.
        return { place = Ir.Index(place, indexExpr, element), ty = element,
            container = container.container }
    end
    D.reject("not-a-place", "This expression does not name storage", span or expr.span)
end

-- A selection whose container is a reference selects through it: the reference names the instance,
-- so the container becomes that instance. A runtime reference is a pointer, so its place is one
-- dereference further on, and it is conservatively retaining because the storage it points at is not
-- known here.
function Eval:derefContainer(ctx, container, span)
    local held = container.value
    if type(held) == "table" and V.tag(held) == "ref" then
        local object = self:placeObject(held)
        if not object then return container end
        return { concrete = object.backing, value = object.backing, place = object.place,
            ty = object.ty, container = object }
    end
    if held and held.ty and S.isRef(held.ty) and V.tag(held) == "ir" then
        local target = self:refTargetType(held.ty)
        local place = ctx.mode == "residual" and self:derefPlace(ctx, held, span) or nil
        return { place = place, ty = target, container = { retaining = true } }
    end
    -- A selection directly off a reference field or a runtime reference: the place holds the
    -- pointer, so the target is one dereference further on. This is checked after the value cases,
    -- because a frontend reference already names the target place.
    if container.ty and S.isPtr(container.ty) then
        -- The pointer is a value, so it is spilled once to reach the record it addresses; from there the
        -- selection is the same route a reference takes.
        local target = self:pointeeType(container.ty)
        if ctx.mode ~= "residual" then
            D.reject("runtime-in-normalization", "A pointer field needs runtime code", span)
        end
        local place = container.place
        if not place then
            local storage = ctx.builder:var(ctx.body, container.ty,
                self:containerExpr(ctx, container))
            place = Ir.Local(storage)
        end
        return { place = Ir.Deref(place, target), ty = target, container = { retaining = true } }
    end
    if container.ty and S.isRef(container.ty) then
        local target = self:refTargetType(container.ty)
        if not container.place then return container end
        return { place = Ir.Deref(container.place, target), ty = target,
            container = { retaining = true } }
    end
    return container
end

-- The container an element or field selection starts from: a compile-time value, or a place with the
-- type it refers to. A selection over a selection does not read the intermediate value.
-- The value a resolved container stands for, as an IR expression: the value it carries when there is
-- one, and otherwise a read of the place it was resolved to. A container that came from `placeOf` has
-- no value attached, so a consumer that needs the expression must be able to read one; assuming a value
-- is there is what turned `Slice(Ptr(U8))` into an internal Lua error rather than a diagnostic.
function Eval:containerExpr(ctx, container)
    if container.value then return self:expression(ctx, container.value, container.ty) end
    if container.place then
        local read = ctx.builder:read(ctx.body, container.ty, container.place)
        return ctx.builder:ref(read, container.ty)
    end
    D.bug("container-value", "A container has neither a value nor a place")
end

function Eval:containerOf(ctx, expr, span)
    if expr.kind == "Reference" or expr.kind == "FieldSelect" or expr.kind == "IndexExpr" then
        local ok, reached = pcall(function() return self:placeOf(ctx, expr, span) end)
        if ok then
            -- The value the selection names travels too, so a reference in it can be dereferenced.
            if reached.concrete == "field" then
                local held = reached.record.fields[reached.name]
                return { concrete = held, value = held, ty = reached.ty, place = reached.place,
                    container = reached.container }
            end
            if reached.concrete == "index" then
                local held = reached.array.items[reached.index + 1]
                return { concrete = held, value = held, ty = reached.ty, place = reached.place,
                    container = reached.container }
            end
            -- A container that has both keeps both: a read uses the value and a reference uses the
            -- place, so a chain of selections does not have to choose here.
            return { place = reached.place, ty = reached.ty, concrete = reached.concrete,
                value = reached.value, container = reached.container or reached.value }
        end
    end
    local value = self:evalExpr(ctx, expr)
    if value.place then return { value = value, place = value.place, ty = value.ty } end
    return { concrete = value, value = value, ty = value.ty }
end

-- `a[i]`: an element read, through the place it names.
function Eval:evalIndex(ctx, expr)
    local reached = self:placeOf(ctx, expr, expr.span)
    -- Residual code reads the storage it names; normalize code reads the value directly. Residual
    -- specialization must not bake a snapshot of module storage, but the reference interpreter
    -- (`session.run`) and a top-level initializer demand (`session.moduleDemand`) both execute over
    -- concrete state, so they read it directly.
    if ctx.mode ~= "residual" and (ctx.session.run or ctx.session.moduleDemand
        or self:placeOrigin(ctx, expr) ~= "module") then
        if reached.concrete == "element" then return reached.value end
        if reached.concrete == "index" then return reached.array.items[reached.index + 1] end
        if reached.concrete == "field" then return reached.record.fields[reached.name] or V.unit() end
    end
    if ctx.mode ~= "residual" then
        D.reject("runtime-in-normalization", "Element is runtime storage", expr.span)
    end
    local read = ctx.builder:read(ctx.body, reached.ty, reached.place)
    return V.ir(ctx.builder:ref(read, reached.ty), reached.ty, nil, reached.place)
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
function Eval:callableArm(value, span)
    if V.tag(value) == "word" then
        local def, bound = value.def, value.args or {}
        local sc = scope(def.lexical)
        local inputs = {}
        for index = 1, #def.params do
            local ty = self:requirement(def, index, sc, span)
            S.checkRuntime(ty, span)
            inputs[index] = S.inValue(ty)
        end
        local results = self:declaredResult(def, sc, span)
        if not results then
            D.reject("callable-branch", "Word " .. tostring(def.name)
                .. " needs declared result types to be selected at run time", span)
        end
        for _, item in ipairs(results) do S.checkRuntime(item, span) end
        local key = V.encode(value)
        if not key then
            D.reject("callable-branch", "A word selected at run time needs static arguments", span)
        end
        self.arms[key] = { kind = "word", def = def, bound = bound }
        return key, S.Unit, S.sig(inputs, results)
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
    return key, plan.envTy, plan.sig
end

-- The tagged representation of one arm: the tag names the code, the payload is its environment.
function Eval:taggedArmValue(ty, key, value, span)
    local envTy = S.caseOf(ty, key)
    if envTy == S.Unit then return V.variant(ty, key, V.unit()) end
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
function Eval:joinCallables(yesValue, noValue, span)
    local keyA, envA, sigA = self:callableArm(yesValue, span)
    local keyB, envB, sigB = self:callableArm(noValue, span)
    if S.encode(sigA) ~= S.encode(sigB) then
        D.reject("callable-branch", "Both arms must be callable the same way: "
            .. S.encode(sigA) .. " and " .. S.encode(sigB), span)
    end
    local ty = S.tagged(sigA, { [keyA] = envA, [keyB] = envB })
    return ty, self:taggedArmValue(ty, keyA, yesValue, span), self:taggedArmValue(ty, keyB, noValue, span)
end

-- Calls one arm. A residual tagged value projects that arm's environment out of the payload; the
-- arm's own code then runs as an ordinary direct call, exactly as a non-tagged callable would.
function Eval:callTaggedArm(ctx, name, variantId, taggedTy, args, span)
    local descriptor = self.arms[name]
    if not descriptor then D.bug("tagged-arm", "Tagged callable has no arm " .. name) end
    local envTy = S.caseOf(taggedTy, name)
    if descriptor.kind == "word" then
        if envTy ~= S.Unit then D.bug("tagged-arm", "A word arm carries no environment") end
        local values = {}
        for _, item in ipairs(descriptor.bound) do values[#values + 1] = item end
        for _, item in ipairs(args) do values[#values + 1] = item end
        return self:applyResidual(ctx, descriptor.def, values, span)
    end
    local plan = descriptor.plan
    local merged = {}
    for _, item in ipairs(descriptor.bound) do merged[#merged + 1] = item end
    for _, item in ipairs(args) do merged[#merged + 1] = item end
    local envExprs = {}
    if envTy ~= S.Unit then
        local id = ctx.builder:valueId()
        ctx.builder:emit(ctx.body, Ir.VariantPayload(id, variantId, taggedTy, name))
        local payload = ctx.builder:ref(id, envTy)
        local envTys = {}
        for _, field in ipairs(S.environmentOf(envTy).fields) do envTys[field.name] = field.type end
        for _, envName in ipairs(plan.envNames) do
            envExprs[#envExprs + 1] = ctx.builder:get(payload, envName, envTys[envName])
        end
    end
    return self:applyClosure(ctx, plan, envExprs, merged, span)
end

-- A call on a tagged callable: test the tag, then run that arm's code directly. Every arm shares the
-- one visible signature, so the results join through a slot per result.
function Eval:applyTagged(ctx, value, args, span)
    local ty = value.ty
    if ctx.mode ~= "residual" then
        D.reject("runtime-in-normalization", "A tagged call needs runtime code", span)
    end
    local expr = value.expr
    if expr == nil then
        -- A tagged value built in this expression has not been emitted yet.
        expr = self:expression(ctx, value, ty)
    end
    if expr.kind ~= "Ref" then D.bug("tagged-call", "A tagged callable must be an SSA value") end
    local variantId = expr.value
    local builder = ctx.builder
    local results = ty.visible.results
    local slots = {}
    for index = 1, #results do slots[index] = builder:var(ctx.body, results[index], nil) end
    local pieces = {}
    for _, name in ipairs(S.casesOf(ty)) do
        local arm = {}
        local armCtx = ctx:arm(arm)
        local result = self:callTaggedArm(armCtx, name, variantId, ty, args, span)
        pieces[#pieces + 1] = { name = name, list = arm, ctx = armCtx, value = result,
            terminated = armCtx.terminated }
    end
    for _, piece in ipairs(pieces) do
        if not piece.terminated then
            local values = self:expand(piece.value)
            if #values ~= #results then
                D.bug("tagged-arity", "A tagged arm returned the wrong number of results")
            end
            for index, item in ipairs(values) do
                builder:store(piece.list, Ir.Local(slots[index]),
                    self:expression(piece.ctx, item, results[index]))
            end
        end
    end
    local child = pieces[#pieces].list
    for index = #pieces - 1, 1, -1 do
        local piece = pieces[index]
        local parent = {}
        local id = builder:valueId()
        builder:emit(parent, Ir.VariantMatches(id, variantId, ty, piece.name))
        builder:emit(parent, Ir.If(builder:ref(id, S.Bool), S.list(piece.list), S.list(child)))
        child = parent
    end
    for _, stmt in ipairs(child) do ctx.body[#ctx.body + 1] = stmt end
    local out = {}
    for index, resultTy in ipairs(results) do
        local place = Ir.Local(slots[index])
        out[index] = V.ir(builder:ref(builder:read(ctx.body, resultTy, place), resultTy), resultTy)
    end
    if #out == 0 then return V.unit() end
    if #out == 1 then return out[1] end
    return V.results(out)
end

-- Materialises a value for a runtime position. `want` is the destination type when the context
-- knows it, which is what lets an unrepresentable callable be rejected with a source diagnostic
-- instead of building mistyped IR.
function Eval:expression(ctx, value, want)
    local tag = V.tag(value)
    if want and (S.isSig(want) or S.isView(want)) and value.ty and S.isTagged(value.ty) then
        self:rejectTaggedErase(ctx.span)
    end
    if (tag == "closure" or tag == "word" or tag == "method") and want
        and (S.isSig(want) or S.isView(want)) then
        if ctx.mode ~= "residual" then
            D.reject("runtime-in-normalization", "A view needs runtime code", ctx.span)
        end
        return self:makeView(ctx, value, S.isView(want) and want.visible or want)
    end
    if tag == "ir" then
        if value.cast then
            value.cast = nil
            value.expr = ctx.builder:convert(value.expr, value.ty)
        end
        return value.expr
    end
    if tag == "string" then return ctx.builder:const(value.ty, Ir.Str(value.bytes)) end
    if tag == "float" then return ctx.builder:float(value.ty, value.n) end
    if tag == "slice" then
        if value.expr then return value.expr end
        D.reject("runtime-in-normalization", "A compile-time slice has no runtime representation", ctx.span)
    end
    if tag == "int" then
        if value.high then return ctx.builder:int64(value.ty, value.high, value.low) end
        return ctx.builder:int(value.ty, value.n)
    end
    if tag == "bool" then return ctx.builder:bool(value.b) end
    if tag == "record" or tag == "object" then return self:recordExpr(ctx, value) end
    if tag == "array" then
        if value.expr then return value.expr end
        if value.place then
            -- Storage is authoritative, so reading the array whole copies its current elements.
            local read = ctx.builder:read(ctx.body, value.ty, value.place)
            return ctx.builder:ref(read, value.ty)
        end
        if ctx.mode ~= "residual" then
            D.reject("runtime-in-normalization", "An array needs runtime code", ctx.span)
        end
        return self:arrayExpr(ctx, value)
    end
    if tag == "ref" then
        if value.place == nil then
            D.reject("ref-target", "A reference to a compile-time value has no address; it can only "
                .. "be used where the value itself is", ctx.span)
        end
        if ctx.mode ~= "residual" then
            D.reject("runtime-in-normalization", "A reference needs runtime code", ctx.span)
        end
        return ctx.builder:addr(value.place, value.ty)
    end
    if tag == "variant" then
        -- A variant already emitted under runtime code refers to its own instruction.
        if value.expr then return value.expr end
        if ctx.mode ~= "residual" then
            D.reject("runtime-in-normalization", "A sum value needs runtime code", ctx.span)
        end
        local caseType = S.caseOf(value.ty, value.case)
        local id = ctx.builder:valueId()
        local payload
        if caseType ~= S.Unit then payload = self:expression(ctx, value.payload, caseType) end
        ctx.builder:emit(ctx.body, Ir.ConstructVariant(id, value.ty, value.case, payload))
        return ctx.builder:ref(id, value.ty)
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
            local entry = self:callableInstance({ plan = plan }, value.bound or {}, ctx.span).target
            local id = ctx.builder:valueId()
            ctx.builder:emit(ctx.body, Ir.View(id, plan.ty, entry, S.list({})))
            return ctx.builder:ref(id, plan.ty)
        end
        -- The value's type is the callable type; its representation is the environment record.
        local fields = {}
        for index, name in ipairs(plan.runtimeOrder) do
            fields[index] = self:expression(ctx, plan.runtime[name])
        end
        return ctx.builder:make(plan.ty, fields)
    end
    D.reject("residual-value", "A " .. S.encode(value.ty or S.Unit) .. " value cannot cross into runtime storage",
        ctx.span)
end

-- A callable argument satisfies a signature requirement when its shape matches. Results are
-- compared only when the callable's own result types are already known.
function Eval:sigMatches(a, b)
    if #a.inputs ~= #b.inputs or #a.results ~= #b.results then return false end
    for index = 1, #a.inputs do
        if S.encode(a.inputs[index]) ~= S.encode(b.inputs[index]) then return false end
    end
    for index = 1, #a.results do
        if S.encode(a.results[index]) ~= S.encode(b.results[index]) then return false end
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
    if S.isOwned(ty) then return self:sigMatches(ty.visible, sig) end
    return false
end

-- A declared signature result must be satisfied by a callable of matching shape. A tagged callable
-- has that shape and still cannot be returned as a signature, because a view cannot retain the
-- environment that carries its tag, so that case reports the erasure rather than a shape mismatch.
function Eval:requireResultSignature(actual, sig, span)
    if actual and actual.ty and S.isTagged(actual.ty) and self:sigMatches(actual.ty.visible, sig) then
        self:rejectTaggedErase(span)
    end
    if not actual or not self:typeMatchesSignature(actual.ty, sig) then
        D.reject("callable-shape", "The returned callable does not match the declared result signature", span)
    end
end

-- Checks a value against a requirement. A signature requirement is satisfied by a callable whose
-- shape matches, which is what lets an unannotated lambda be checked against it.
function Eval:requireAgainst(value, ty, span)
    local wanted = (S.isSig(ty) and ty) or (S.isView(ty) and ty.visible) or nil
    if wanted and value.ty and S.isTagged(value.ty) then
        self:rejectTaggedErase(span)
    end
    if wanted and (V.tag(value) == "closure" or V.tag(value) == "word" or V.tag(value) == "method") then
        if self:callableMatches(value, wanted) == false then
            D.reject("callable-shape", "Callable does not match the required signature", span)
        end
        return
    end
    if S.isView(ty) and V.tag(value) == "ir" and value.ty == ty then return end
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
    if tag == "object" or tag == "record" or tag == "ir" then return value.borrowed == true end
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
    if S.isF64(ty) then
        -- An integer becomes a double implicitly only when the double is exact: rounding can lose a
        -- value, so the rounding is written `F64(x)` where it happens.
        if not S.isInteger(value.ty) then return nil end
        local from = value.ty
        if V.isKnown(value) then
            local high, low = wordsOf(value)
            local rounded
            -- Only a signed wide value is negative: the same bits are a large positive U64.
            if S.isWide(from) and S.isSigned(from) and U64Kernel.slt(high, low, 0, 0) then
                rounded = -U64Kernel.tofloat(U64Kernel.neg(high, low))
            elseif S.isWide(from) then
                rounded = U64Kernel.tofloat(high, low)
            else
                rounded = value.n
            end
            local backHigh, backLow = wordsOfDouble(rounded)
            if backHigh == high and backLow == low then return V.f64(rounded) end
            D.reject("numeric-range", "Value " .. describeWords(from, high, low)
                .. " is not exactly an F64; write F64(x) to round it", span)
        end
        if S.isWide(from) then return nil end
        -- Every value of a 32-bit or narrower type is exactly a double.
        if V.tag(value) == "ir" then
            value.cast = true
            value.ty = S.F64
            return value
        end
        return V.f64(value.n)
    end
    local from = value.ty
    if from == ty then return value end
    if not (S.isInteger(from) and S.isInteger(ty)) then return nil end
    if S.widthOf(from) == S.widthOf(ty) then
        -- The same width with a different signedness: the bits are the value.
        if S.isSigned(from) == S.isSigned(ty) then return nil end
        if V.tag(value) == "ir" then value.cast = true end
        if V.isKnown(value) then return become(value, ty, wordsOf(value)) end
        return become(value, ty, 0, 0)
    end
    if fitsAlways(from, ty) then
        -- Nothing can be lost, so the conversion is applied where the value is materialised.
        if V.tag(value) == "ir" then value.cast = true end
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
    if S.isInteger(value.ty) and S.isInteger(ty) then
        D.reject("numeric-range", "Expected " .. S.encode(ty) .. " but found " .. S.encode(value.ty)
            .. "; narrow a run-time value with an explicit conversion such as "
            .. S.encode(ty):lower() .. "(x)", span)
    end
    D.reject("type-mismatch", "Expected " .. S.display(ty) .. " but found " .. S.display(value.ty), span)
end

-- Expressions ---------------------------------------------------------------------------------

function Eval:evalExpr(ctx, expr)
    self:step(expr.span)
    -- Tail position belongs to this node alone, so it is taken here and handed back only to a construct
    -- whose child really is the returned expression: a call that is the whole expression, and the arms
    -- of a conditional. An operand of `+`, an index or an argument is never a tail position, so a
    -- self-call there stays a real call instead of becoming a back edge whose result is Unit.
    local tail = ctx.tail
    ctx.tail = false
    local kind = expr.kind
    if kind == "U32Literal" then
        -- A literal adapts to another operand's type when it fits, which is decided from the syntax.
        local literal = V.u32(expr.value)
        literal.literal = true
        return literal
    elseif kind == "U64Literal" then
        -- A literal that does not fit a word is a 64-bit literal, held as its two words.
        local literal = V.int64(S.U64, expr.high, expr.low)
        literal.literal = true
        return literal
    elseif kind == "BoolLiteral" then return V.bool(expr.value)
    elseif kind == "UnitLiteral" then return V.unit()
    elseif kind == "Reference" then return self:evalReference(ctx, expr)
    elseif kind == "UnaryExpr" then return self:evalUnary(ctx, expr)
    elseif kind == "BinaryExpr" then return self:evalBinary(ctx, expr)
    elseif kind == "Condition" then ctx.tail = tail; return self:evalCondition(ctx, expr, nil)
    elseif kind == "Apply" then ctx.tail = tail; return self:evalApply(ctx, expr)
    elseif kind == "SchemaExpr" then return self:evalSchema(ctx, expr)
    elseif kind == "StringLiteral" then return V.string(S.String, expr.bytes)
    elseif kind == "FloatLiteral" then return V.f64(expr.value)
    elseif kind == "ArrayExpr" then return self:evalArray(ctx, expr, nil)
    elseif kind == "IndexExpr" then return self:evalIndex(ctx, expr)
    elseif kind == "RecordSupply" then ctx.tail = tail; return self:evalSupply(ctx, expr)
    elseif kind == "FieldSelect" then return self:evalFieldSelect(ctx, expr)
    elseif kind == "Lambda" then return self:evalLambda(ctx, expr, nil)
    elseif kind == "SignatureExpr" then return self:evalSignature(ctx, expr)
    end
    D.todo("expression", "Unsupported expression form: " .. tostring(kind), expr.span)
end

-- A signature is a static value: a calling requirement, never runtime data.
function Eval:evalSignature(ctx, expr)
    -- A signature's inputs carry the value/place distinction, so each becomes an InValue here.
    local inputs = {}
    for index, item in ipairs(expr.inputs) do
        inputs[index] = S.inValue(self:typeOf(item, ctx.scope, expr.span))
    end
    local results = {}
    if expr.results.kind == "Single" then
        results[1] = self:typeOf(expr.results.type, ctx.scope, expr.span)
    else
        for index, item in ipairs(expr.results.types) do results[index] = self:typeOf(item, ctx.scope, expr.span) end
    end
    return V.type(S.sig(inputs, results))
end

function Eval:evalReference(ctx, expr)
    local name = expr.name.text
    local slot = lookup(ctx.scope, name)
    if not slot then self:unknownName(name, expr.name.span) end
    if slot.kind == "value" then
        local demanded = self:demand(slot, expr.name.span)
        if demanded.value == nil then D.reject("value-required", name .. " has no value", expr.name.span) end
        if slot.atTop and ctx.mode == "residual"
            and (V.tag(demanded.value) == "record"
                or (V.tag(demanded.value) == "array" and demanded.value.place == nil)) then
            -- Runtime code reaches a *file-scope* binding through its named storage. A local
            -- aggregate keeps its value and spills to local storage only when demanded. Normalize
            -- code keeps the value itself, so it can still specialise a call that reads one.
            return self:moduleObject(demanded, expr.name.span)
        end
        return demanded.value
    elseif slot.kind == "word" then
        return V.word(slot.def, {}, expr.name.span)
    elseif slot.kind == "field" then
        return self:readFieldValue(ctx, slot, expr.name.span)
    elseif slot.kind == "concrete-field" then
        return slot.record.fields[slot.name] or V.unit()
    elseif slot.kind == "param" then
        if ctx.mode ~= "residual" then
            D.reject("runtime-in-normalization", "Parameter " .. slot.name .. " is runtime storage", expr.name.span)
        end
        local read = ctx.builder:read(ctx.body, slot.ty, Ir.Local(slot.storage))
        return V.ir(ctx.builder:ref(read, slot.ty), slot.ty)
    end
    D.bug("binding", "Unknown binding kind " .. tostring(slot.kind))
end

-- Reads an implicit receiver field (or a bound local field place).
function Eval:readFieldValue(ctx, slot, span)
    if slot.static then return slot.static end
    if ctx.mode ~= "residual" then
        -- Normalize code reads the frontend value a borrowed or module place stands for directly.
        local record = slot.record and slot.record.backing
        -- A module object is read the same way, but only where reading it is the point: module
        -- initialization and the reference interpreter both execute over concrete state, while
        -- residual specialization must not bake a snapshot of module storage into the output.
        if record and record.fields
            and (not slot.record.module or ctx.session.run or ctx.session.moduleDemand) then
            local held = record.fields[slot.name]
            if held == nil then D.bug("module-field", "Module storage has no field " .. slot.name) end
            return held
        end
        D.reject("runtime-in-normalization", "Field " .. slot.name .. " is runtime storage", span)
    end
    -- A field of a record that still holds its construction expression is a pure projection; a
    -- record that demanded a place reads storage so a store is observed.
    if slot.record and slot.record.expr then
        return V.ir(ctx.builder:get(slot.record.expr, slot.name, slot.ty), slot.ty)
    end
    local read = ctx.builder:read(ctx.body, slot.ty, slot.place)
    -- The place travels with the value: a reference read from storage needs it to reach its target.
    return V.ir(ctx.builder:ref(read, slot.ty), slot.ty, nil, slot.place)
end

-- Arithmetic and comparison on IEEE-754 doubles. Both sides must be F64 once a literal has adopted the
-- other side's type, exactly as an integer operation needs one width: an integer that is not a literal
-- needs an explicit conversion, because rounding it may lose a value. IEEE decides the rest, so a
-- division by zero is an infinity or a NaN rather than a trap and a NaN comparison is false.
function Eval:floatOp(ctx, op, left, right, leftSpan, rightSpan, span)
    for _, side in ipairs({ { left, leftSpan }, { right, rightSpan } }) do
        local value, where = side[1], side[2]
        if value.ty ~= S.F64 then
            if S.isInteger(value.ty) and value.literal then
                -- A literal adopts F64, which is what lets `2.0 * 3` read as it looks.
                self:requireType(value, S.F64, where)
            else
                D.reject("type-mismatch", "A float operation needs two F64 values, found "
                    .. S.encode(left.ty or S.Unit) .. " and " .. S.encode(right.ty or S.Unit)
                    .. "; convert one side explicitly", span)
            end
        end
    end
    local irOp = FLOAT_ARITH[op] or COMPARE[op]
    if not irOp then
        D.reject("type-mismatch", "Operator " .. op .. " has no meaning for F64", span)
    end
    if V.isKnown(left) and V.isKnown(right) then
        local a, b = left.n, right.n
        if op == "+" then return V.f64(a + b) end
        if op == "-" then return V.f64(a - b) end
        if op == "*" then return V.f64(a * b) end
        if op == "/" then return V.f64(a / b) end
        local result
        if op == "==" then result = a == b
        elseif op == "!=" then result = a ~= b
        elseif op == "<" then result = a < b
        elseif op == "<=" then result = a <= b
        elseif op == ">" then result = a > b
        else result = a >= b end
        return V.bool(result)
    end
    local ty = COMPARE[op] and S.Bool or S.F64
    return V.ir(ctx.builder:bin(irOp, self:expression(ctx, left), self:expression(ctx, right), ty), ty)
end

function Eval:evalUnary(ctx, expr)
    local value = self:evalExpr(ctx, expr.operand)
    local op = expr.operator
    if op == "not" then
        self:requireType(value, S.Bool, expr.operand.span)
        if V.tag(value) == "bool" then return V.bool(not value.b) end
        return V.ir(ctx.builder:un("Not", self:expression(ctx, value), S.Bool), S.Bool)
    end
    if S.isF64(value.ty) then
        -- Only negation applies to a float; complement and shift are integer operations.
        if op ~= "-" then
            D.reject("type-mismatch", "Negation is the only unary operator F64 has, not " .. op,
                expr.operand.span)
        end
        if V.isKnown(value) then return V.f64(-value.n) end
        return V.ir(ctx.builder:un("Neg", self:expression(ctx, value), S.F64), S.F64)
    end
    if not S.isInteger(value.ty) then
        D.reject("type-mismatch", "Expected an integer but found " .. S.encode(value.ty), expr.operand.span)
    end
    local ty = value.ty
    if V.isInteger(value) then
        if S.isWide(ty) then
            local high, low = wordsOf(value)
            if op == "-" then return V.int64(ty, U64Kernel.neg(high, low)) end
            return V.int64(ty, U64Kernel.bnot(high, low))
        end
        local n = op == "-" and wrap(ty, -value.n) or wrap(ty, bit.bnot(value.n))
        return V.int(ty, n)
    end
    return V.ir(ctx.builder:un(op == "-" and "Neg" or "BitNot", self:expression(ctx, value), ty), ty)
end

function Eval:evalBinary(ctx, expr)
    local op = expr.operator
    if op == "and" or op == "or" then return self:evalShortCircuit(ctx, expr) end
    local left = self:evalExpr(ctx, expr.left)
    local right = self:evalExpr(ctx, expr.right)
    return self:binaryOp(ctx, op, left, right, expr.left.span, expr.right.span, expr.span)
end

-- One implementation of every binary operator, shared by expressions and compound stores.
function Eval:binaryOp(ctx, op, left, right, leftSpan, rightSpan, span)
    if S.isPtr(left.ty) or S.isPtr(right.ty) then
        -- Two addresses of one element type compare by address. A pointer has no order and no integer
        -- value, so nothing else about it is offered.
        if (op ~= "==" and op ~= "!=") or left.ty ~= right.ty then
            D.reject("type-mismatch", "A pointer compares only with a pointer of one element type, found "
                .. S.encode(left.ty or S.Unit) .. " and " .. S.encode(right.ty or S.Unit), span)
        end
        if ctx.mode ~= "residual" then
            D.reject("runtime-in-normalization", "A pointer comparison needs runtime code", span)
        end
        return V.ir(ctx.builder:bin(COMPARE[op], self:expression(ctx, left),
            self:expression(ctx, right), S.Bool), S.Bool)
    end
    if S.isF64(left.ty) or S.isF64(right.ty) then
        return self:floatOp(ctx, op, left, right, leftSpan, rightSpan, span)
    end
    leftSpan, rightSpan, span = leftSpan or ctx.span, rightSpan or ctx.span, span or ctx.span
    if (op == "==" or op == "!=") and S.isString(left.ty) and S.isString(right.ty) then
        -- Strings compare by content: a byte sequence has no identity a program can observe, so
        -- pointer equality would be a surprising answer rather than the useful one.
        if V.tag(left) == "string" and V.tag(right) == "string" then
            return V.bool((left.bytes == right.bytes) == (op == "=="))
        end
        if ctx.mode ~= "residual" then
            D.reject("runtime-in-normalization", "A run-time string comparison needs runtime code", span)
        end
        return V.ir(ctx.builder:bin(COMPARE[op], self:expression(ctx, left), self:expression(ctx, right),
            S.Bool), S.Bool)
    end
    if (op == "==" or op == "!=") and S.isBool(left.ty) and S.isBool(right.ty) then
        -- A Bool compares by value. The operation is not ordered: section 7 offers Bool only
        -- equality, exactly as it offers only equality for Unit.
        if V.isKnown(left) and V.isKnown(right) then
            return V.bool((left.b == right.b) == (op == "=="))
        end
        return V.ir(ctx.builder:bin(COMPARE[op], self:expression(ctx, left),
            self:expression(ctx, right), S.Bool), S.Bool)
    end
    if (op == "==" or op == "!=") and S.isUnit(left.ty) and S.isUnit(right.ty) then
        -- Unit has one value and no runtime representation, so both operands already ran for their
        -- effects and the answer is known: Unit equals Unit.
        return V.bool(op == "==")
    end
    if COMPARE[op] then
        -- A comparison widens both sides, which is always safe and never narrows.
        if S.isInteger(left.ty) and S.isInteger(right.ty) and left.ty ~= right.ty then
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
        if not S.isInteger(left.ty) or left.ty ~= right.ty then
            D.reject("type-mismatch", "Comparison needs two integers of one width, found "
                .. S.encode(left.ty or S.Unit) .. " and " .. S.encode(right.ty or S.Unit), span)
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
            return V.bool(result)
        end
        return V.ir(ctx.builder:bin(COMPARE[op], self:expression(ctx, left), self:expression(ctx, right), S.Bool),
            S.Bool)
    end
    local irOp = ARITH[op]
    if not irOp then D.bug("operator", "Unknown binary operator " .. tostring(op)) end
    -- A shift takes its amount as a plain U32; every other operator needs both sides at one width.
    if op == "<<" or op == ">>" then
        if not S.isInteger(left.ty) then
            D.reject("type-mismatch", "A shift needs an integer to shift, found "
                .. S.encode(left.ty or S.Unit), leftSpan)
        end
        self:requireType(right, S.U32, rightSpan)
    else
        if not S.isInteger(left.ty) or not S.isInteger(right.ty) then
            D.reject("type-mismatch", "Arithmetic needs two integers, found "
                .. S.encode(left.ty or S.Unit) .. " and " .. S.encode(right.ty or S.Unit), span)
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
    if S.isWide(ty) and V.isInteger(left) and V.isInteger(right) then
        local ah, al = wordsOf(left)
        local bh, bl = wordsOf(right)
        local high, low
        if op == "+" then high, low = U64Kernel.add(ah, al, bh, bl)
        elseif op == "-" then high, low = U64Kernel.sub(ah, al, bh, bl)
        elseif op == "*" then high, low = U64Kernel.mul(ah, al, bh, bl)
        elseif op == "/" then
            if S.isSigned(ty) then high, low = U64Kernel.sdivmod(ah, al, bh, bl)
            else high, low = U64Kernel.divmod(ah, al, bh, bl) end
        elseif op == "%" then
            if S.isSigned(ty) then _, _, high, low = U64Kernel.sdivmod(ah, al, bh, bl)
            else _, _, high, low = U64Kernel.divmod(ah, al, bh, bl) end
        elseif op == "^" then high, low = U64Kernel.pow(ah, al, bh, bl)
        elseif op == "<<" then high, low = U64Kernel.shl(ah, al, bl)
        elseif op == ">>" then
            if S.isSigned(ty) then high, low = U64Kernel.sar(ah, al, bl)
            else high, low = U64Kernel.shr(ah, al, bl) end
        elseif op == "&" then high, low = U64Kernel.band(ah, al, bh, bl)
        elseif op == "|" then high, low = U64Kernel.bor(ah, al, bh, bl)
        else high, low = U64Kernel.bxor(ah, al, bh, bl) end
        return V.int64(ty, high, low)
    end
    if V.isInteger(left) and V.isInteger(right) then
        local x, y = left.n, right.n
        local result
        if op == "+" then result = wrap(ty, x + y)
        elseif op == "-" then result = wrap(ty, x - y)
        elseif op == "*" then result = exact(ty, "*", x, y)
        elseif op == "/" then result = S.isSigned(ty) and signedDiv(ty, x, y) or math.floor(x / y)
        elseif op == "%" then
            result = S.isSigned(ty) and signedRem(ty, x, y) or x - y * math.floor(x / y)
        elseif op == "^" then
            if S.isSigned(ty) and y < 0 then
                D.reject("numeric-range", "A signed power needs a power that is not negative", span)
            end
            result = pow(ty, x, y)
        elseif op == "<<" then result = wrap(ty, x * 2 ^ y)
        elseif op == ">>" then
            -- A signed shift is arithmetic: it keeps the sign bit.
            result = S.isSigned(ty) and math.floor(x / 2 ^ y) or math.floor(x / 2 ^ y)
        elseif op == "&" then result = wrap(ty, bit.band(x, y))
        elseif op == "|" then result = wrap(ty, bit.bor(x, y))
        else result = wrap(ty, bit.bxor(x, y)) end
        return V.int(ty, result)
    end
    local builder = ctx.builder
    local leftExpr, rightExpr = self:expression(ctx, left), self:expression(ctx, right)
    -- A signed power with a negative exponent has no result, so a run-time one is checked first.
    if op == "^" and S.isSigned(ty) then
        if V.isKnown(right) and right.n < 0 then
            D.reject("numeric-range", "A signed power needs a power that is not negative", rightSpan)
        end
        if not V.isKnown(right) then
            builder:emit(ctx.body, Ir.Trap(builder:bin("Lt", rightExpr,
                builder:int(right.ty, 0), S.Bool), "numeric-range"))
        end
    end
    if (op == "/" or op == "%") and not V.isInteger(right) then
        builder:trap(ctx.body, builder:bin("Eq", rightExpr, builder:u32(0), S.Bool), "division-zero")
    end
    return V.ir(builder:bin(irOp, leftExpr, rightExpr, ty), ty)
end

function Eval:evalShortCircuit(ctx, expr)
    local left = self:evalExpr(ctx, expr.left)
    self:requireType(left, S.Bool, expr.left.span)
    local isOr = expr.operator == "or"
    if V.tag(left) == "bool" then
        local short = isOr and left.b or (not isOr and not left.b)
        if short then return V.bool(isOr) end
        local right = self:evalExpr(ctx, expr.right)
        self:requireType(right, S.Bool, expr.right.span)
        return right
    end
    local test = self:expression(ctx, left)
    local yesList, noList = {}, {}
    local yesCtx = ctx:arm(yesList)
    local yesValue = self:evalExpr(yesCtx, expr.right)
    self:requireType(yesValue, S.Bool, expr.right.span)
    local builder = ctx.builder
    local storage = builder:var(ctx.body, S.Bool, nil)
    local place = Ir.Local(storage)
    builder:store(yesList, place, self:expression(yesCtx, yesValue))
    builder:store(noList, place, builder:bool(isOr))
    builder:emit(ctx.body, Ir.If(test, S.list(yesList), S.list(noList)))
    return V.ir(builder:ref(builder:read(ctx.body, S.Bool, place), S.Bool), S.Bool)
end

-- Evaluates an expression in an expected-signature position. Only a lambda (or a conditional
-- choosing between lambdas) consumes the expectation; anything else evaluates normally.
function Eval:evalExpected(ctx, expr, expected)
    if expected == nil then return self:evalExpr(ctx, expr) end
    if expr.kind == "Lambda" then return self:evalLambda(ctx, expr, expected) end
    if expr.kind == "ArrayExpr" then return self:evalArray(ctx, expr, expected) end
    if expr.kind == "Condition" then return self:evalCondition(ctx, expr, expected) end
    return self:evalExpr(ctx, expr)
end

function Eval:evalCondition(ctx, expr, expected)
    -- The test is not a tail position; both arms are.
    local tail = ctx.tail
    ctx.tail = false
    local test = self:evalExpr(ctx, expr.test)
    self:requireType(test, S.Bool, expr.test.span)
    if V.tag(test) == "bool" then
        return self:evalExpected(ctx, test.b and expr.yes or expr.no, expected)
    end
    local builder = ctx.builder
    local testExpr = self:expression(ctx, test)
    local yesList, noList = {}, {}
    -- Both arms are tail positions, so each arm context inherits the flag.
    ctx.tail = tail
    local yesCtx, noCtx = ctx:arm(yesList), ctx:arm(noList)
    ctx.tail = false
    local yesValue = self:evalExpected(yesCtx, expr.yes, expected)
    local yesTerminated = yesCtx.terminated or false
    local noValue = self:evalExpected(noCtx, expr.no, expected)
    local noTerminated = noCtx.terminated or false
    -- An arm that transfers control (a tail back edge) never reaches the continuation.
    if yesTerminated and noTerminated then
        ctx.terminated = true
        return V.unit()
    end
    if not yesTerminated and not noTerminated then
        -- Two callable arms whose types differ join into one tagged callable, unless they are the
        -- same code identity, in which case their callable type already agrees.
        local yesCallable, noCallable = self:isCallableValue(yesValue), self:isCallableValue(noValue)
        local sameCallable = yesCallable and noCallable and yesValue.ty ~= nil and yesValue.ty == noValue.ty
        if yesCallable and noCallable and not sameCallable then
            local _, joinedYes, joinedNo = self:joinCallables(yesValue, noValue, expr.span)
            yesValue, noValue = joinedYes, joinedNo
        elseif (yesCallable or noCallable) and yesValue.ty ~= noValue.ty then
            local other = yesCallable and noValue or yesValue
            D.reject("branch-result", "One arm is a callable and the other is "
                .. (other.ty and S.encode(other.ty) or "a bare word with no callable type"), expr.span)
        end
        if yesValue.ty ~= noValue.ty then
            D.reject("branch-result", "Conditional arms have different types: "
                .. S.encode(yesValue.ty) .. " and " .. S.encode(noValue.ty), expr.span)
        end
    end
    -- When both continuing arms agree on one known scalar, the value is that scalar whatever the
    -- test. The arms still run for their effects, but there is no join slot to allocate and no read
    -- to copy back out.
    if not yesTerminated and not noTerminated and self:sameKnownScalar(yesValue, noValue) then
        -- The test expression is pure, so an arm list that is empty on both sides has no effect to
        -- keep: there is no `If` to emit at all.
        if #yesList > 0 or #noList > 0 then
            builder:emit(ctx.body, Ir.If(testExpr, S.list(yesList), S.list(noList)))
        end
        return yesValue
    end
    local ty = yesTerminated and noValue.ty or yesValue.ty
    local storage = builder:var(ctx.body, ty, nil)
    local place = Ir.Local(storage)
    -- The arm's own statements must receive any reads materialising its result: an aggregate
    -- result is canonicalised into reads of the storage it was built into, which belongs to the
    -- arm, not to the continuation.
    if not yesTerminated then builder:store(yesList, place, self:expression(yesCtx, yesValue)) end
    if not noTerminated then builder:store(noList, place, self:expression(noCtx, noValue)) end
    builder:emit(ctx.body, Ir.If(testExpr, S.list(yesList), S.list(noList)))
    return V.ir(builder:ref(builder:read(ctx.body, ty, place), ty), ty)
end

-- Schemas and records -------------------------------------------------------------------------

-- A schema literal: data fields, methods, and no bound fields yet.
function Eval:evalSchema(ctx, expr)
    return self:newSchema(ctx, expr, nil, nil, nil)
end

-- Builds a schema, or a specialised copy of `base` with extra static (readonly) fields.
function Eval:newSchema(ctx, expr, statics, readonly, base)
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
        return V.schema(def)
    end
    for _, member in ipairs(expr.members) do
        if member.kind == "FieldMember" then
            local name = member.name.text
            local ty = self:typeOf(member.type, ctx.scope, member.span)
            -- A field declared as a signature is represented by the borrowed callable ABI: the
            -- field holds an invocation pointer and an environment pointer, not callable code.
            if S.isSig(ty) then ty = S.view(ty) end
            if def.fields[name] or def.methods[name] then
                D.reject("duplicate", "Duplicate schema member " .. name, member.name.span)
            end
            def.fields[name] = ty
            def.fieldOrder[#def.fieldOrder + 1] = name
        else
            local name = member.def.name.text
            if def.fields[name] or def.methods[name] then
                D.reject("duplicate", "Duplicate schema member " .. name, member.def.name.span)
            end
            local method = self:define(member.def, ctx.scope, def)
            def.methods[name] = method
        end
    end
    local names = {}
    for name in pairs(def.fields) do names[#names + 1] = name end
    local fields = {}
    for _, name in ipairs(names) do fields[name] = def.fields[name] end
    def.type = S.record(fields)
    def.fieldNames = names
    return V.schema(def)
end

-- `Schema { field = value }`: either a partial (static) supply or a construction.
function Eval:evalSupply(ctx, expr)
    -- The tail position belongs to a keyed invocation, not to the base or the supplied values.
    local tail = ctx.tail
    ctx.tail = false
    local base = self:evalExpr(ctx, expr.schema)
    if V.tag(base) == "ctor" then
        -- A sum alternative with a record payload is built like a record, then tagged.
        if #expr.fields == 0 and base.caseType == S.Unit then
            return self:makeVariant(ctx, base, nil, expr.span)
        end
        if not S.isRecord(base.caseType) then
            D.reject("variant-payload",
                "Alternative " .. base.case .. " does not take a record; apply it to one value instead",
                expr.span)
        end
        local values = {}
        for _, field in ipairs(expr.fields) do
            local name = field.name.text
            if not S.field(base.caseType, name) then
                D.reject("unknown-member", "Alternative " .. base.case .. " has no field " .. name,
                    field.name.span)
            end
            if values[name] ~= nil then
                D.reject("duplicate", "Field " .. name .. " is supplied twice", field.name.span)
            end
            values[name] = self:evalExpr(ctx, field.value)
        end
        for _, field in ipairs(base.caseType.fields) do
            if values[field.name] == nil then
                D.reject("variant-payload", "Alternative " .. base.case .. " is missing field "
                    .. field.name, expr.span)
            end
        end
        return self:makeVariant(ctx, base, self:constructRecord(ctx, base.caseType, values, nil), expr.span)
    end
    if V.tag(base) == "variant" or (V.tag(base) == "ir" and S.isSum(base.ty)) then
        return self:evalMatch(ctx, base, expr, nil)
    end
    if V.tag(base) == "word" and base.def.keyed then
        return self:applyKeyed(ctx, base, expr.fields, expr.span, tail)
    end
    if V.tag(base) ~= "schema" then
        D.reject("schema-required", "Keyed supply needs a schema on the left", expr.schema.span)
    end
    local def = base.def
    local supplied = {}
    for _, field in ipairs(expr.fields) do
        local name = field.name.text
        if not def.fields[name] then
            D.reject("unknown-member", "Schema has no field " .. name, field.name.span)
        end
        if supplied[name] ~= nil or def.statics[name] ~= nil then
            D.reject("duplicate", "Field " .. name .. " is supplied twice", field.name.span)
        end
        supplied[name] = self:evalExpr(ctx, field.value)
    end

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
        return self:newSchema(ctx, def.node, statics, readonly, def)
    end

    -- Saturated construction: the instance owns mutable storage for every data field.
    local values = {}
    for name, value in pairs(def.statics) do values[name] = value end
    for name, value in pairs(supplied) do values[name] = value end
    for _, name in ipairs(def.fieldOrder) do
        if values[name] == nil then D.bug("schema-fields", "A data field was not supplied") end
    end
    local ty = def.type
    if ctx.mode ~= "residual" then
        -- Static evaluation builds a concrete record; it is not runtime storage.
        local fields = {}
        for _, name in ipairs(def.fieldNames) do fields[name] = values[name] end
        return V.record(ty, fields, def)
    end
    return self:constructRecord(ctx, ty, values, def)
end

-- Builds a record value of `ty` from a field-name keyed supply. `def` supplies methods and static
-- bindings when the record came from a source schema; it is absent for a sum alternative.
function Eval:constructRecord(ctx, ty, values, def)
    if ctx.mode ~= "residual" then
        local fields = {}
        for _, name in ipairs(S.fieldNames(ty)) do fields[name] = values[name] or V.unit() end
        return V.record(ty, fields, def)
    end
    local exprs, borrowed = {}, false
    for index, field in ipairs(ty.fields) do
        local fieldValue = values[field.name] or V.unit()
        exprs[index] = self:expression(ctx, fieldValue, field.type)
        -- A signature-typed field is a view whose environment points at a local adapter, so an
        -- instance holding one is itself tied to this activation.
        if self:isBorrowed(fieldValue) or S.isView(field.type) then borrowed = true end
    end
    -- The Make is the value until a place is demanded (a field store, a reference, or a borrowed
    -- receiver). `body` is where that spill goes, so a demand from inside an arm still names storage
    -- the outer scope remembers. No storage exists until something needs an address.
    return V.object(ty, nil, def, borrowed, nil, ctx.builder:make(ty, exprs), ctx.body)
end

function Eval:evalFieldSelect(ctx, expr)
    local base = self:evalExpr(ctx, expr.base)
    local name = expr.field.text
    -- Selection through a reference selects from the instance it names, so the reference is read as
    -- that instance and the ordinary member rules apply.
    base = self:placeObject(base) or base
    if base.ty and S.isSlice(base.ty) and name == "length" then
        local known = self:sliceCount(base)
        if known then return V.u32(known) end
        if ctx.mode ~= "residual" then
            D.reject("runtime-in-normalization", "A runtime slice length needs runtime code", expr.span)
        end
        return V.ir(ctx.builder:sliceLength(self:expression(ctx, base, base.ty), S.U32), S.U32)
    end
    local tag = V.tag(base)
    if tag == "object" then
        local def = base.schema
        if def.methods[name] then return V.method(def.methods[name], base) end
        if def.fields[name] then return self:readFieldValue(ctx, self:fieldSlot(def, base, name), expr.span) end
        D.reject("unknown-member", "Value has no member " .. name, expr.field.span)
    elseif tag == "record" then
        if base.schema and base.schema.methods[name] then
            return V.method(base.schema.methods[name], base)
        end
        if base.fields[name] ~= nil then return base.fields[name] end
        D.reject("unknown-member", "Record has no field " .. name, expr.field.span)
    elseif tag == "schema" then
        if base.def.methods[name] then return V.method(base.def.methods[name], nil) end
        D.reject("unknown-member", "Schema has no member " .. name, expr.field.span)
    elseif tag == "namespace" then
        local member = base.members[name]
        if not member then
            D.reject("unknown-member", "Module " .. tostring(base.module) .. " does not export " .. name,
                expr.field.span)
        end
        return member
    elseif tag == "type" and S.isSum(base.value) then
        -- A sum type's member names a constructor for one alternative.
        local caseType = S.caseOf(base.value, name)
        if not caseType then D.reject("unknown-member", "Sum type has no alternative " .. name, expr.field.span) end
        return V.ctor(base.value, name, caseType)
    elseif tag == "ir" and (S.isRef(base.ty) or S.isPtr(base.ty)) then
        -- A reference and a raw pointer reach the record they address the same way, so the field is
        -- the same projection one dereference on; only the lifetime rule differs, and a pointer has
        -- none to check.
        -- A runtime reference is a pointer, so the field lives at the place it points to.
        local ty = S.field(self:refTargetType(base.ty), name)
        if not ty then D.reject("unknown-member", "Record has no field " .. name, expr.field.span) end
        local place = Ir.Project(self:derefPlace(ctx, base, expr.span), Ir.Field(name))
        local read = ctx.builder:read(ctx.body, ty, place)
        return V.ir(ctx.builder:ref(read, ty), ty)
    elseif tag == "ir" and S.isRecord(base.ty) then
        local ty = S.field(base.ty, name)
        if not ty then D.reject("unknown-member", "Record has no field " .. name, expr.field.span) end
        if ctx.mode ~= "residual" then
            D.reject("runtime-in-normalization", "Cannot read a runtime record field here", expr.span)
        end
        -- A record value spilled into storage for a store must read through that storage, so a store
        -- and a later read observe the same instance instead of the pre-spill value.
        if base.place then
            local place = Ir.Project(base.place, Ir.Field(name))
            local read = ctx.builder:read(ctx.body, ty, place)
            return V.ir(ctx.builder:ref(read, ty), ty, nil, place)
        end
        return V.ir(ctx.builder:get(base.expr, name, ty), ty)
    end
    D.reject("member-required", "Cannot select from " .. S.encode(base.ty or S.Unit), expr.span)
end

function Eval:fieldSlot(def, object, name)
    -- A compile-time object has no storage, so the place is only built when there is one; such a
    -- slot is read and written through the frontend value instead.
    return { kind = "field", name = name, ty = def.fields[name],
        place = object.place and Ir.Project(object.place, Ir.Field(name)) or nil, record = object,
        static = def.statics[name], readonly = def.readonly[name] and true or false }
end

-- Stores -------------------------------------------------------------------------------------

function Eval:execStore(ctx, stmt)
    local slot, place = self:storeTarget(ctx, stmt.target)
    if slot.readonly then
        D.reject("readonly-field", "Field " .. slot.name .. " was bound by static supply and cannot be assigned",
            stmt.target.span)
    end
    local operator = stmt.operator
    if operator == "=" then
        local value = self:evalExpr(ctx, stmt.value)
        self:requireAgainst(value, slot.ty, stmt.value.span)
        return self:writeSlot(ctx, slot, place, value)
    end
    local binary = COMPOUND[operator]
    if not binary then D.bug("operator", "Unknown assignment operator " .. tostring(operator)) end
    -- The target is evaluated once, the old value read once, then the RHS runs.
    local old = self:readSlot(ctx, slot, place, stmt.target.span)
    local value = self:evalExpr(ctx, stmt.value)
    local combined = self:binaryOp(ctx, binary, old, value, stmt.target.span, stmt.value.span, stmt.span)
    return self:writeSlot(ctx, slot, place, combined)
end

-- Either a residual IR place or a concrete interpreter field.
function Eval:readSlot(ctx, slot, place, span)
    if slot.kind == "concrete-field" then return slot.record.fields[slot.name] or V.unit() end
    if slot.kind == "concrete-index" then return slot.array.items[slot.index + 1] end
    return self:readFieldValue(ctx, slot, span)
end

function Eval:writeSlot(ctx, slot, place, value)
    if slot.kind == "concrete-index" then
        slot.array.items[slot.index + 1] = value
        if self:isBorrowed(value) then slot.array.borrowed = true end
        return
    end
    if slot.kind == "concrete-field" then
        slot.record.fields[slot.name] = value
        if self:isBorrowed(value) then slot.record.borrowed = true end
        return
    end
    -- Assigning callable code to a signature-typed field builds a view whose environment is a
    -- local adapter, so the assignment is a borrow even when the code itself is not.
    local becomesBorrowed = self:isBorrowed(value) or S.isView(slot.ty)
    if V.tag(value) == "ref" and value.tied and (slot.retaining or (slot.record and slot.record.module)) then
        D.reject("ref-escape", self:refEscapeMessage(), ctx.span)
    end
    if becomesBorrowed and (slot.retaining or (slot.record and slot.record.module)) then
        D.reject("borrow-escape",
            "Module storage outlives the activation that made this borrow, so it cannot hold one",
            ctx.span)
    end
    ctx.builder:store(ctx.body, place, self:expression(ctx, value, slot.ty))
    -- Storing a borrow into an instance makes that instance non-retaining too.
    if becomesBorrowed and slot.record then slot.record.borrowed = true end
end

-- Resolves a store target to a place, plus the slot describing it.
function Eval:storeTarget(ctx, target)
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
    local reached = self:placeOf(ctx, target, target.span)
    -- A store in residual code goes to storage. Normalize code writes the concrete value it names so
    -- a later read observes it: a local or enclosing aggregate, or module storage under the reference
    -- interpreter (`session.run`), which executes the program rather than specialising it. Module
    -- storage is runtime state, so compile-time initialization and residual specialization never
    -- write it; a mutating top-level initializer rejects instead of baking a moved start value.
    local origin = ctx.mode ~= "residual" and self:placeOrigin(ctx, target) or nil
    -- `placeOrigin` names the route a *name* spells, so a write through a local binding that holds a
    -- reference to module storage looks like a local write. What the place turned out to be is the
    -- other half of the question, and without it such a write is folded away with its effect lost.
    local modules = origin == "module"
        or (reached.container ~= nil and reached.container.module == true)
    -- Module storage is runtime state: residual specialization never writes it, because such a store
    -- would not appear in the generated code. Initialization (`session.moduleDemand`) and the reference
    -- interpreter (`session.run`) execute over concrete state and do write it.
    if ctx.mode ~= "residual" and modules
        and not (ctx.session.run or ctx.session.moduleDemand) then
        D.reject("runtime-in-normalization",
            "Module storage is runtime state, so only module initialization may write it", target.span)
    end
    if ctx.mode ~= "residual" then
        if reached.concrete == "field" then
            return { kind = "concrete-field", name = reached.name, record = reached.record,
                ty = reached.ty }, nil
        end
        if reached.concrete == "index" then
            return { kind = "concrete-index", array = reached.array, index = reached.index,
                ty = reached.ty }, nil
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
    return { kind = "field", name = target.kind == "IndexExpr" and "[index]" or "field",
        ty = reached.ty, place = reached.place, static = nil, readonly = false,
        record = reached.container, retaining = (reached.container and reached.container.enclosing)
            and true or false }, reached.place
end

-- Either a residual IR place or a concrete interpreter field.
function Eval:readSlot(ctx, slot, place, span)
    if slot.kind == "concrete-field" then return slot.record.fields[slot.name] or V.unit() end
    if slot.kind == "concrete-index" then return slot.array.items[slot.index + 1] end
    return self:readFieldValue(ctx, slot, span)
end

function Eval:writeSlot(ctx, slot, place, value)
    if slot.kind == "concrete-index" then
        slot.array.items[slot.index + 1] = value
        if self:isBorrowed(value) then slot.array.borrowed = true end
        return
    end
    if slot.kind == "concrete-field" then
        slot.record.fields[slot.name] = value
        if self:isBorrowed(value) then slot.record.borrowed = true end
        return
    end
    -- Assigning callable code to a signature-typed field builds a view whose environment is a
    -- local adapter, so the assignment is a borrow even when the code itself is not.
    local becomesBorrowed = self:isBorrowed(value) or S.isView(slot.ty)
    if V.tag(value) == "ref" and value.tied and (slot.retaining or (slot.record and slot.record.module)) then
        D.reject("ref-escape", self:refEscapeMessage(), ctx.span)
    end
    if becomesBorrowed and (slot.retaining or (slot.record and slot.record.module)) then
        D.reject("borrow-escape",
            "Module storage outlives the activation that made this borrow, so it cannot hold one",
            ctx.span)
    end
    ctx.builder:store(ctx.body, place, self:expression(ctx, value, slot.ty))
    -- Storing a borrow into an instance makes that instance non-retaining too.
    if becomesBorrowed and slot.record then slot.record.borrowed = true end
end


-- Closure application: a static closure is evaluated now; otherwise a direct call carries the
-- captured environment as leading arguments.
function Eval:applyClosure(ctx, plan, envExprs, args, span, bound)
    local def = plan.def
    bound = bound or {}
    local supplied = #bound + #args
    if supplied > #def.params then D.reject("arity", "Overapplication is not supported", span) end
    if supplied < #def.params then
        -- Partial application of a closure binds static arguments, exactly as for a named word.
        local merged = {}
        for _, value in ipairs(bound) do merged[#merged + 1] = value end
        for _, value in ipairs(args) do merged[#merged + 1] = value end
        for index, value in ipairs(merged) do
            if not V.isStatic(value) then
                D.reject("static-required", "Partial application needs a static value for parameter "
                    .. def.params[index].name.text, span)
            end
        end
        return V.closure(plan, merged)
    end
    args = (function()
        local all = {}
        for _, value in ipairs(bound) do all[#all + 1] = value end
        for _, value in ipairs(args) do all[#all + 1] = value end
        return all
    end)()
    if envExprs == nil and #plan.runtimeOrder == 0 then
        local allKnown = true
        for _, value in ipairs(args) do if not V.isKnown(value) then allKnown = false end end
        if allKnown and ctx.mode == "normalize" then
            return self:applyClosureStatically(plan, args, span)
        end
    end
    if ctx.mode ~= "residual" then
        D.reject("runtime-in-normalization", "This closure call needs runtime code", span)
    end
    local callable = { plan = plan, env = self:closureEnvironment(plan, envExprs) }
    return self:callClosure(ctx, callable, args, span)
end

-- Binds a known callable's hidden inputs in a local adapter and yields a view value.
function Eval:makeView(ctx, value, sig)
    local viewType = S.view(sig)
    local entry, slots, borrowed = nil, {}, false
    local tag = V.tag(value)
    if tag == "closure" then
        local plan = value.plan
        entry = self:callableInstance({ plan = plan }, value.bound or {}, ctx.span).target
        for _, name in ipairs(plan.runtimeOrder) do
            local capture = plan.runtime[name]
            slots[#slots + 1] = Ir.ValueArg(self:expression(ctx, capture, capture.ty))
        end
        for _, name in ipairs(plan.borrowedOrder) do
            slots[#slots + 1] = Ir.BorrowArg(plan.borrowed[name].place)
            borrowed = true
        end
    elseif tag == "word" then
        entry = self:instanceFor(value.def, ctx.span, value.args).target
    elseif tag == "method" then
        -- A method value borrows its receiver, which is exactly the hidden prefix of its instance.
        local def = value.def
        local instance = self:instanceFor(def, ctx.span, {}, value.receiver)
        local sc = scope(def.lexical)
        local inputs = {}
        for index = 1, #def.params do
            inputs[index] = S.inValue(self:requirement(def, index, sc, ctx.span))
        end
        if not self:sigMatches(S.sig(inputs, instance.results), sig) then
            D.reject("callable-shape", "Method " .. tostring(def.name)
                .. " does not match the required signature", ctx.span)
        end
        entry = instance.target
        slots[#slots + 1] = Ir.BorrowArg(self:recordPlace(ctx, value.receiver, ctx.span))
        borrowed = true
    else
        D.bug("c-view", "Only known code can be bound into a view")
    end
    local id = ctx.builder:valueId()
    ctx.builder:emit(ctx.body, Ir.View(id, viewType, entry, S.list(slots)))
    -- The environment points at a local adapter, so the view is not retaining. The frontend value
    -- records that, so the borrow can be tracked to its escape.
    ctx.borrowedViews = ctx.borrowedViews or {}
    ctx.borrowedViews[id.id] = true
    return ctx.builder:ref(id, viewType)
end

-- An opaque callable is invoked through its view: the environment pointer plus the argument list.
function Eval:applyView(ctx, value, args, span)
    if ctx.mode ~= "residual" then
        D.reject("runtime-in-normalization", "An opaque callable needs runtime code", span)
    end
    local sig = value.ty.visible
    if #args ~= #sig.inputs then D.reject("arity", "Opaque callable arity mismatch", span) end
    local operands = {}
    for index, input in ipairs(sig.inputs) do
        if input.kind ~= "InValue" then
            D.todo("view-input", "Only by-value callable inputs are supported", span)
        end
        self:requireType(args[index], input.type, span)
        operands[#operands + 1] = Ir.ValueArg(self:expression(ctx, args[index]))
    end
    local results = {}
    for _ = 1, #sig.results do results[#results + 1] = ctx.builder:valueId() end
    ctx.builder:emit(ctx.body, Ir.Indirect(S.list(results), value.expr, S.list(operands)))
    if #sig.results == 0 then return V.unit() end
    if #sig.results == 1 then
        return V.ir(ctx.builder:ref(results[1], sig.results[1]), sig.results[1])
    end
    local out = {}
    for index, ty in ipairs(sig.results) do
        out[index] = V.ir(ctx.builder:ref(results[index], ty), ty)
    end
    return V.results(out)
end

-- An Owned IR value carries its environment; the captured fields are its arguments.
function Eval:applyOwned(ctx, value, args, span)
    local plan = self:planOf(value.ty, span)
    if #plan.borrowedOrder > 0 then
        D.bug("borrowed-callable-value",
            "A closure with borrowed captures must not have a materialised value")
    end
    if S.environmentOf(value.ty) == S.Unit then
        -- Pure code carries no environment, so there is nothing to project: the call is direct.
        return self:applyClosure(ctx, plan, {}, args, span, value.bound)
    end
    local envTys = {}
    for _, field in ipairs(value.ty.environment.fields or {}) do envTys[field.name] = field.type end
    local envExprs = {}
    for _, name in ipairs(plan.envNames) do
        envExprs[#envExprs + 1] = ctx.builder:get(value.expr, name, envTys[name])
    end
    return self:applyClosure(ctx, plan, envExprs, args, span)
end

-- Evaluating a capture-free closure with known arguments produces a value, not a call.
function Eval:applyClosureStatically(plan, args, span)
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
        declare(sc, param.name.text, { kind = "value", name = param.name.text, value = args[index] }, param.span)
    end
    local result = self:execBody(self:context("normalize", sc, span), plan.def.body, span)
    if #result == 0 then return V.unit() end
    if #result == 1 then return result[1] end
    return V.results(result)
end

-- Closures ------------------------------------------------------------------------------------
--
-- A closure is a lambda definition plus captured bindings. Captures that are static become part of
-- the code identity; the rest form a by-value environment that is passed to the compiled lambda as
-- leading hidden inputs. Because the environment type carries the code key, an IR value of that
-- type is directly callable: no function pointer is needed while the code is known.

local function envFieldName(index) return string.format("c%02d", index) end

-- Materialises the value a free name refers to at closure-creation time.
function Eval:captureValue(ctx, name, span)
    local slot = lookup(ctx.scope, name)
    if not slot then D.reject("unknown-name", "Unknown captured name: " .. name, span) end
    if slot.kind == "value" then
        local demanded = self:demand(slot, span)
        return demanded.value or V.unit()
    elseif slot.kind == "concrete-field" then
        return slot.record.fields[slot.name] or V.unit()
    elseif slot.kind == "field" or slot.kind == "param" then
        if ctx.mode ~= "residual" then
            D.reject("runtime-in-normalization", "Cannot capture runtime storage " .. name, span)
        end
        -- Reading a field captures its value; the field path must not be flattened to the root.
        local place = slot.kind == "field" and slot.place or Ir.Local(slot.storage)
        local read = ctx.builder:read(ctx.body, slot.ty, place)
        return V.ir(ctx.builder:ref(read, slot.ty), slot.ty)
    elseif slot.kind == "word" then
        return V.word(slot.def, {}, span)
    end
    D.bug("capture", "Unknown capture binding kind " .. tostring(slot.kind))
end

function Eval:evalLambda(ctx, expr, expected)
    local order = Resolve.captures(expr)

    local plan = { def = self:define(expr, moduleTop(ctx.scope), nil, "|lambda|"), order = order,
        static = {},
        runtime = {}, runtimeOrder = {}, captures = order }
    plan.def.lambda = true
    plan.borrowed, plan.borrowedOrder = {}, {}
    for _, name in ipairs(order) do
        local value = self:captureValue(ctx, name, expr.span)
        local tag = V.tag(value)
        if V.isStatic(value) then
            plan.static[name] = value
        elseif tag == "object" or tag == "method" or tag == "record" or tag == "array" then
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
            local place = object.place
            if ctx.mode == "residual" then
                if S.isArray(object.ty) then
                    place = self:arrayPlace(ctx, object, expr.span)
                else
                    place = self:recordPlace(ctx, object, expr.span)
                end
            end
            plan.borrowedOrder[#plan.borrowedOrder + 1] = name
            if S.isArray(object.ty) then
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
            if ctx.mode == "residual" and not place then
                D.reject("runtime-in-normalization", "Cannot capture runtime storage " .. name, expr.span)
            end
        elseif tag == "closure" then
            -- A nested borrowed closure would need a place for a callable environment.
            D.reject("borrow-escape",
                "Capturing a borrowed closure needs a callable environment, which is not supported; "
                .. "capture its receiver instead", expr.span)
        else
            if ctx.mode ~= "residual" then
                D.reject("runtime-in-normalization", "This closure captures runtime value " .. name, expr.span)
            end
            plan.runtimeOrder[#plan.runtimeOrder + 1] = name
            plan.runtime[name] = value
        end
    end

    local inputs, results = {}, {}
    for index, param in ipairs(expr.params) do
        if param.annotation then
            inputs[index] = S.inValue(self:typeOf(param.annotation, ctx.scope, expr.span))
        else
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
            local input = expected.inputs[index]
            if input.kind ~= "InValue" then
                D.todo("lambda-annotation", "A lambda parameter cannot be a borrowed place", param.span)
            end
            inputs[index] = input
        end
    end
    if expr.annotation then results[1] = expr.annotation end
    -- Resolved parameter types travel with the plan: a contextually typed lambda has no annotation
    -- to re-evaluate when its body is compiled.
    plan.paramTypes = {}
    for index, input in ipairs(inputs) do plan.paramTypes[index] = input.type end
    plan.sig = S.sig(inputs, results)
    plan.envNames = {}
    local envFields = {}
    for index, name in ipairs(plan.runtimeOrder) do
        plan.envNames[index] = envFieldName(index)
        envFields[envFieldName(index)] = plan.runtime[name].ty
    end
    plan.envTy = #plan.runtimeOrder > 0 and S.record(envFields) or S.Unit
    plan.key = "closure:" .. tostring(plan.def.id)
    for _, capture in ipairs(order) do
        local static, borrowed = plan.static[capture], plan.borrowed[capture]
        if borrowed then
            -- A record borrow is keyed by its schema identity; an array borrow has no schema, so its
            -- type is the identity.
            local shape = tostring(borrowed.kind) .. ":"
                .. (borrowed.schema and tostring(borrowed.schema.id) or S.encode(borrowed.ty))
            if borrowed.method then shape = shape .. ":" .. tostring(borrowed.method.id) end
            plan.key = plan.key .. "|" .. capture .. "=@" .. shape
        else
            plan.key = plan.key .. (static and ("|" .. capture .. "=" .. (V.encode(static) or "?"))
                or ("|" .. capture .. "=#"))
        end
    end
    self.plans = self.plans or {}
    self.plans[plan.key] = plan
    -- Build the base instance now: its result types become the visible signature of the closure
    -- type, and a call-site specialisation must agree with them.
    -- Compile the base instance now: its result types complete the closure's visible signature,
    -- which is what lets a callable argument be checked against a required signature. Code that is
    -- never called is left to the C compiler to discard.
    local base = self:callableInstance({ plan = plan }, {}, expr.span)
    plan.sig = S.sig(inputs, base.results)
    plan.ty = S.owned(plan.key, plan.sig, plan.envTy)
    return V.closure(plan)
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
            parts[#parts + 1] = (ty and S.isOwned(ty)) and ("!" .. ty.entry) or "*"
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

function Eval:callClosure(ctx, callable, args, span)
    local instance = self:callableInstance(callable, args, span)
    if instance.status == "building" and not instance.results then
        D.reject("recursive-result", "Recursive closure needs an explicit result annotation", span)
    end
    -- Environment arguments precede the declared parameters for the compiled lambda.
    return self:emitCallableCall(ctx, instance, callable.env, args, span)
end

function Eval:emitCallableCall(ctx, instance, envArgs, args, span)
    local builder = ctx.builder
    local operands = {}
    for index, arg in ipairs(envArgs) do
        if arg.kind == "place" then
            operands[#operands + 1] = Ir.BorrowArg(arg.place)
        else
            operands[#operands + 1] = Ir.ValueArg(arg.expr or self:expression(ctx, arg.value,
                instance.inputTypes[index]))
        end
    end
    for index, position in ipairs(instance.paramPositions) do
        -- After the environment, the declared parameters follow in signature order.
        operands[#operands + 1] = Ir.ValueArg(self:expression(ctx, args[position],
            instance.inputTypes[#envArgs + index]))
    end
    local runtime = instance.runtimeResults or self:runtimeResults(instance.results)
    local results = {}
    for _ = 1, #runtime do results[#results + 1] = builder:valueId() end
    builder:emit(ctx.body, Ir.Call(S.list(results), instance.target, S.list(operands)))
    local ir = {}
    for index, ty in ipairs(runtime) do
        ir[index] = V.ir(builder:ref(results[index], ty), ty)
    end
    local out = self:logicalResults(instance.results, ir)
    if #out == 0 then return V.unit() end
    if #out == 1 then return out[1] end
    return V.results(out)
end

function Eval:callableInstance(callable, args, span)
    local key = self:callableKey(callable.plan, args)
    local existing = self.instances[key]
    if existing then return existing end
    local count = 0
    for _ in pairs(self.instances) do count = count + 1 end
    if count >= (self.limits.keys or 1024) then D.resource("keys", "Residual instance budget exhausted", span) end
    return self:buildCallableInstance(key, callable, args, span)
end

function Eval:buildCallableInstance(key, callable, args, span)
    self:enterBuild(span)
    local plan, def = callable.plan, callable.plan.def
    self.nextFn = self.nextFn + 1
    local instance = { key = key, def = def, plan = plan, target = "wordletfn_" .. self.nextFn,
        status = "building", args = args, paramPositions = {}, inputTypes = {} }
    self.instances[key] = instance
    self.order[#self.order + 1] = instance

    local body, setup = {}, {}
    local builder = IR.builder({ id = instance.target })
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
        declare(sc, name, { kind = "value", name = name, value = V.ir(builder:ref(value, ty), ty) }, span)
    end
    for _, name in ipairs(plan.borrowedOrder) do
        local borrowed = plan.borrowed[name]
        local storage = builder:storageId()
        params[#params + 1] = Ir.PlaceParam(#inputs, storage, borrowed.ty)
        inputs[#inputs + 1] = S.inPlace(borrowed.ty)
        paramTypes[#paramTypes + 1] = borrowed.ty
        instance.inputTypes[#instance.inputTypes + 1] = borrowed.ty
        -- The place parameter belongs to the caller, so the object is an enclosing owner here.
        if S.isArray(borrowed.ty) then
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

    for index, param in ipairs(def.params) do
        -- A contextually typed lambda carries its resolved parameter types on the plan.
        local ty = plan.paramTypes[index] or self:requirement(def, index, sc, span)
        local supplied = args[index]
        local bound = false
        if S.isSig(ty) then
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
            elseif supplied ~= nil and V.tag(supplied) == "ir" and S.isOwned(supplied.ty) then
                ty = supplied.ty
            elseif supplied ~= nil and V.tag(supplied) == "ir" and S.isView(supplied.ty) then
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
        if not bound and ty == S.Unit then
            -- A Unit parameter carries no information, so it is not a runtime input at all: the
            -- name is bound to the Unit value and neither the ABI nor the call site mentions it.
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
                if S.isRecord(ty) then
                    declare(sc, param.name.text, { kind = "value", name = param.name.text,
                        value = V.object(ty, nil, { fields = S.fieldsOf(ty),
                            fieldNames = S.fieldNames(ty), statics = {}, readonly = {}, methods = {}, type = ty },
                            nil, false, builder:ref(value, ty), setup) },
                        param.span)
                else
                    declare(sc, param.name.text, { kind = "value", name = param.name.text,
                        value = V.ir(builder:ref(value, ty), ty) }, param.span)
                end
            end
        end
    end

    instance.results = self:declaredResult(def, sc, span)
    local ctx = setmetatable({ session = self, mode = "residual", scope = sc, span = span,
        builder = builder, body = body, fn = { id = instance.target }, instance = instance }, Ctx)
    self:execBodyResidual(ctx, def.body, span)
    if not instance.results then instance.results = ctx.resultTypes end
    if not instance.results then D.reject("recursive-result", "Closure has no returning path", span) end
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
    self:leaveBuild()
    instance.status = "done"
    return instance
end

-- Calling a closure value or an IR value whose Owned type names its code.
function Eval:applyCallable(ctx, def, codeKey, envValues, envTys, args, span)
    local plan = self:planOf({ entry = codeKey }, span)
    local callable = { plan = plan, envValues = envValues }
    if envValues == nil then
        -- The environment is inside the callable value; read its fields positionally.
        callable.envExprs = {}
    end
    return self:callClosure(ctx, callable, args, span)
end

-- Bodies --------------------------------------------------------------------------------------

-- A deferred action hands the rest of the list to a nested block over the same context, so every way
-- out of what follows passes through a `return`, which the action is attached to. A second action
-- nests inside the first, which is what makes several of them run in reverse order. The action itself
-- runs at the return rather than here: a return inside a statement conditional's arm is an exit from
-- this block too, and running the action here would miss that path and could only ever produce one
-- value.
function Eval:execDefer(ctx, statements, index, stmt)
    local frame = { pending = self:deferredCall(ctx, stmt), parent = ctx.deferFrame, span = stmt.span }
    ctx.deferFrame = frame
    local terminated = self:execBlock(ctx, statements, index + 1)
    ctx.deferFrame = frame.parent
    return terminated
end

-- Every deferred action pending at a return, innermost first, which is the reverse of the order the
-- `defer` statements were written. Running them here is what makes a transfer out of the block in
-- the middle of a conditional reach them as well.
function Eval:runPendingDefers(ctx)
    local frame = ctx.deferFrame
    while frame do
        self:invoke(ctx, frame.pending.callee, frame.pending.args, frame.pending.span)
        frame = frame.parent
    end
end

-- The callee and the arguments of a deferred action are evaluated where the `defer` is written, so a
-- read of mutable storage there is a snapshot of what the program had rather than of what the names
-- mean later.
function Eval:deferredCall(ctx, stmt)
    local callee = self:evalExpr(ctx, stmt.call.callee)
    local args = self:evalArguments(ctx, stmt.call.arguments, callee)
    return { callee = callee, args = args, span = stmt.call.span }
end

-- Runs an already-evaluated call, which is how a deferred action is invoked without evaluating its
-- source a second time. The callee kinds are the ones `evalApply` dispatches on; a new kind has to be
-- added here as well.
function Eval:invoke(ctx, callee, args, span)
    local tag = V.tag(callee)
    if tag == "word" then return self:apply(ctx, callee, args, span) end
    if tag == "method" then return self:applyMethod(ctx, callee, args, span) end
    if tag == "closure" then
        return self:applyClosure(ctx, callee.plan, nil, args, span, callee.bound)
    end
    if tag == "ir" and S.isOwned(callee.ty) then return self:applyOwned(ctx, callee, args, span) end
    if tag == "ir" and S.isView(callee.ty) then return self:applyView(ctx, callee, args, span) end
    if (tag == "ir" or tag == "variant") and callee.ty and S.isTagged(callee.ty) then
        return self:applyTagged(ctx, callee, args, span)
    end
    D.reject("callable-required", "A deferred action must be a call, found "
        .. (callee.ty and S.encode(callee.ty) or V.describe(callee)), span)
end


function Eval:execBlock(ctx, statements, from)
    -- A statement list is not a tail position; only a `return` inside it is, and it sets the flag.
    ctx.tail = false
    for index = from or 1, #statements do
        local stmt = statements[index]
        self:step(stmt.span)
        local kind = stmt.kind
        if kind == "Defer" then return self:execDefer(ctx, statements, index, stmt) end
        if kind == "ValueStmt" then
            local values = self:expand(self:evalValueDef(ctx, stmt.def))
            for index, binder in ipairs(stmt.def.binders) do
                declare(ctx.scope, binder.name.text,
                    { kind = "value", name = binder.name.text, value = values[index] or V.unit() }, binder.span)
            end
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
            local values = self:evalList(ctx, stmt.values)
            ctx.expectedResult, ctx.tail = savedExpected, savedTail
            self:checkReturn(values, stmt.span)
            if ctx.terminated then return true end
            ctx.terminated = savedTerminated
            if ctx.mode == "residual" then
                local exprs = self:materializeAll(ctx, values,
                    ctx.instance and ctx.instance.results or nil)
                ctx.resultTypes = {}
                for index, value in ipairs(values) do ctx.resultTypes[index] = value.ty end
                -- The action runs after the returned expression has been evaluated and before the value
                -- leaves. `materializeAll` above is what takes the snapshot the returned value names,
                -- so a read of storage the action changes still yields what it was at the return.
                self:runPendingDefers(ctx)
                ctx.builder:emit(ctx.body, Ir.Return(S.list(exprs)))
            else
                -- The interpreter executes the program rather than compiling it, so the actions run as
                -- ordinary calls on the way out of the block.
                self:runPendingDefers(ctx)
                ctx.result = values
            end
            return true
        elseif kind == "IfStmt" then
            if self:execIfStatement(ctx, stmt) then return true end
        elseif kind == "CallStmt" then
            self:evalApply(ctx, stmt.call)
        elseif kind == "StoreStmt" then
            self:execStore(ctx, stmt)
        else
            D.todo("statement", "Unsupported statement form: " .. tostring(kind), stmt.span)
        end
    end
    return false
end

function Eval:materializeAll(ctx, values, wants)
    local out = {}
    for index, value in ipairs(values) do
        -- A Unit slot is logical but has no runtime representation, exactly as a Unit parameter has
        -- none, so it is dropped here and the IR result list is the erased one.
        if value.ty ~= S.Unit then
            out[#out + 1] = self:expression(ctx, value, wants and wants[index] or nil)
        end
    end
    return out
end

-- A Unit slot erases from a result vector the way it erases from a parameter list (syntax.md §6).
-- The function's IR results are the non-Unit ones; a call site reinserts the Unit values so a
-- binding list keeps its positions, while a return simply drops them.
function Eval:runtimeResults(results)
    local out = {}
    for _, ty in ipairs(results or {}) do if ty ~= S.Unit then out[#out + 1] = ty end end
    return out
end

function Eval:logicalResults(results, runtime)
    local out, index = {}, 1
    for _, ty in ipairs(results or {}) do
        if ty == S.Unit then out[#out + 1] = V.unit()
        else out[#out + 1] = runtime[index]; index = index + 1 end
    end
    return out
end

function Eval:execIfStatement(ctx, stmt)
    local test = self:evalExpr(ctx, stmt.test)
    self:requireType(test, S.Bool, stmt.test.span)
    if V.tag(test) == "bool" then
        if test.b then return self:execBlock(ctx, stmt.yes) end
        return self:execBlock(ctx, stmt.no)
    end
    local testExpr = self:expression(ctx, test)
    local yesList, noList = {}, {}
    local yesReturned = self:execBlock(ctx:arm(yesList), stmt.yes)
    local noReturned = self:execBlock(ctx:arm(noList), stmt.no)
    if #yesList > 0 or #noList > 0 then
        ctx.builder:emit(ctx.body, Ir.If(testExpr, S.list(yesList), S.list(noList)))
    end
    return yesReturned and noReturned
end

-- Value definitions and annotations -----------------------------------------------------------

function Eval:evalValueDef(ctx, def)
    -- Evaluate signature annotations first: they supply missing lambda parameter types.
    local expectations = {}
    for index, binder in ipairs(def.binders) do
        if binder.annotation then
            local ty = self:typeOf(binder.annotation, ctx.scope, binder.span)
            -- A signature annotation types an unannotated lambda; any other annotation is what an
            -- array literal with no elements of its own has to take its type from.
            if S.isSig(ty) or S.isArray(ty) then expectations[index] = ty end
        end
    end
    local values = {}
    for index, expr in ipairs(def.values) do
        local value = self:evalExpected(ctx, expr, expectations[index])
        if index < #def.values then
            values[#values + 1] = self:first(value)
        else
            for _, item in ipairs(self:expand(value)) do values[#values + 1] = item end
        end
    end
    local bound = {}
    for index, binder in ipairs(def.binders) do
        bound[index] = self:checkAnnotation(ctx, binder, values[index] or V.unit())
    end
    if #bound == 1 then return bound[1] end
    return V.results(bound)
end

function Eval:checkAnnotation(ctx, binder, value)
    if not binder.annotation then return value end
    local ty = self:typeOf(binder.annotation, ctx.scope, binder.span)
    self:requireAgainst(value, ty, binder.span)
    return value
end

-- A type expression is a Type value or a schema (which denotes its record type).
function Eval:asType(value, span)
    if V.tag(value) == "type" then return value.value end
    if V.tag(value) == "schema" then return value.def.type end
    return nil
end

function Eval:typeOf(expr, sc, span)
    if expr.kind == "Reference" then
        local slot = lookup(sc, expr.name.text)
        -- The name is being computed right now, so this is the recursion knot: hand back the cell it
        -- reserved rather than demanding its layout.
        if slot and slot.open and slot.cell and self:isTypeDefinition(slot) then
            if self.referencedCells == nil then self.referencedCells = {} end
            self.referencedCells[slot.cell] = true
            return S.named(slot.cell)
        end
    end
    local value = self:evalExpr(self:context("normalize", sc, span), expr)
    local ty = self:asType(value, span)
    if not ty then D.reject("type-required", "Expected a type", expr.span) end
    return ty
end

function Eval:requirement(def, index, sc, span)
    local param = def.params[index]
    if not param.annotation then
        D.reject("type-required", "Parameter " .. param.name.text .. " needs a type annotation", param.span)
    end
    return self:typeOf(param.annotation, sc, param.span)
end

-- Integer arithmetic -------------------------------------------------------------------------------
-- One implementation of the per-width rules, shared by the interpreter and by the builder when it
-- folds constants. Wrapping is masked at the type's own width, so a narrower integer wraps the way
-- U32 wraps at 32 bits.

local U32Kernel = require("wordletkit.u32")

-- Wrapping is a modulus rather than a bit mask: Lua's bit operations are signed 32-bit, so masking a
-- value at or above 2^31 would turn it negative. A signed width maps the wrapped value back into its
-- own range, which is what makes two's complement wrap around.
function wrap(ty, n)
    local wrapped = n % S.modulusOf(ty)
    if S.isSigned(ty) and wrapped > S.maxOf(ty) then wrapped = wrapped - S.modulusOf(ty) end
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

-- A product and a power can exceed what a Lua number holds exactly for a 32-bit width, so those two
-- go through the exact kernel; the narrower widths fit exactly either way.
function exact(ty, op, x, y)
    if ty == S.U32 then
        if op == "*" then return U32Kernel.mul(x, y) end
    end
    return wrap(ty, x * y)
end

function pow(ty, base, exponent)
    if ty == S.U32 then return U32Kernel.pow(base, exponent) end
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
function Eval:evalArguments(ctx, exprs, callee)
    local def, offset
    local tag = V.tag(callee)
    if tag == "word" then
        def = callee.def
        offset = #callee.args
    elseif tag == "closure" then
        def = callee.plan.def
        offset = 0
    elseif tag == "method" then
        def = callee.def
        offset = #(callee.args or {})
    end
    local sc = (def and offset == 0) and scope(def.lexical) or nil
    local values = {}
    for index, expr in ipairs(exprs) do
        local param = sc and def.params[index] or nil
        if param and param.isType then
            -- A builtin parameter that names a type is resolved on the type path, which is the path that
            -- hands back the cell an open definition reserved instead of demanding its layout. Without
            -- this, `Array(Node, 2)` inside Node's own definition was refused as an eager initializer
            -- cycle before the cycle checker could say what was actually wrong.
            local held = V.type(self:typeOf(expr, sc, expr.span))
            values[#values + 1] = held
            if param.name and param.name.text then
                declare(sc, param.name.text, { kind = "value", name = param.name.text, value = held },
                    param.span)
            end
        else
            local expected
            -- The requirement decides, not how it was spelled: an alias of a signature is a signature,
            -- so a lambda passed to `f: Endo` gets its parameter type from it just as one passed to a
            -- written `(U32): U32` does. Only a signature is used this way, as that is what types a
            -- lambda.
            if param and param.annotation then
                local ty = self:typeOf(param.annotation, sc, param.span)
                if S.isSig(ty) then expected = ty end
            end
            local value = self:evalExpected(ctx, expr, expected)
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
        end
    end

    return values
end

-- `U8(x)`, `U16(x)` and `U32(x)` convert between integer widths: widening is free, narrowing traps
-- when the value does not fit, and a known value outside the target is rejected while compiling.
-- An integer becomes the nearest double, rounding once with ties to even. The exact kernel does the
-- rounding, because a Lua division would round twice for a value above 2^53.
function Eval:roundToFloat(ctx, value, span)
    local from = value.ty
    if V.isKnown(value) then
        local high, low = wordsOf(value)
        if S.isWide(from) and S.isSigned(from) and U64Kernel.slt(high, low, 0, 0) then
            return V.f64(-U64Kernel.tofloat(U64Kernel.neg(high, low)))
        end
        if S.isWide(from) then return V.f64(U64Kernel.tofloat(high, low)) end
        return V.f64(value.n)
    end
    return V.ir(ctx.builder:convert(self:expression(ctx, value), S.F64), S.F64)
end

-- A float becomes an integer by truncation toward zero. A value the target cannot hold rejects when it
-- is known and stops a run-time one, which is also what keeps a NaN from becoming some integer: a NaN
-- compares false against every bound, so it is trapped on its own.
function Eval:truncateToInt(ctx, ty, value, span)
    local maxDouble, minDouble = floatBounds(ty)
    if V.isKnown(value) then
        -- Truncation toward zero, which is what a conversion to an integer means; `math.modf` is
        -- that operation, while a modulo would floor toward negative infinity instead.
        local truncated = math.modf(value.n)
        if truncated ~= truncated or truncated < minDouble or truncated >= maxDouble then
            D.reject("numeric-range", "Value " .. string.format("%.17g", value.n)
                .. " does not fit in " .. S.encode(ty), span)
        end
        if S.isWide(ty) then return V.int64(ty, wordsOfDouble(truncated)) end
        return V.int(ty, truncated)
    end
    local builder, expr = ctx.builder, self:expression(ctx, value)
    builder:emit(ctx.body, Ir.Trap(builder:bin("Ne", expr, expr, S.Bool), "numeric-range"))
    builder:emit(ctx.body, Ir.Trap(builder:bin("Lt", expr, builder:float(S.F64, minDouble), S.Bool),
        "numeric-range"))
    builder:emit(ctx.body, Ir.Trap(builder:bin("Ge", expr, builder:float(S.F64, maxDouble), S.Bool),
        "numeric-range"))
    return V.ir(builder:convert(expr, ty), ty)
end

-- `F64(x)` rounds an integer to the nearest double, and `U32(f)` truncates a float toward zero with
-- the target's range checked. Both directions are explicit here even where the value would be exact,
-- because that is what names the rounding at the point it happens.
function Eval:applyConversion(ctx, ty, args, span)
    if #args ~= 1 then D.reject("arity", "A conversion takes one value", span) end
    local value = args[1]
    if S.isF64(ty) then
        if S.isF64(value.ty) then return value end
        if not S.isInteger(value.ty) then
            D.reject("type-mismatch", "F64 needs a number, found " .. S.encode(value.ty or S.Unit), span)
        end
        return self:roundToFloat(ctx, value, span)
    end
    if S.isInteger(ty) and S.isF64(value.ty) then
        return self:truncateToInt(ctx, ty, value, span)
    end
    if #args ~= 1 then D.reject("arity", "A conversion takes one value", span) end
    local value = args[1]
    if not S.isInteger(value.ty) then
        D.reject("type-mismatch", S.encode(ty) .. " needs an integer, found "
            .. S.encode(value.ty or S.Unit), span)
    end
    local reinterprets = S.widthOf(value.ty) == S.widthOf(ty)
        and S.isSigned(value.ty) ~= S.isSigned(ty)
    if reinterprets then
        -- The same width read the other way keeps every bit, so nothing is checked.
        if V.isKnown(value) then return become(value, ty, wordsOf(value)) end
        return V.ir(ctx.builder:convert(self:expression(ctx, value), ty), ty)
    end
    local converted = self:convert(value, ty, span)
    if converted then return converted end
    if V.isKnown(value) then
        local high, low = wordsOf(value)
        if wordsFit(ty, high, low) then return become(value, ty, high, low) end
        D.reject("numeric-range", "Value " .. describeWords(value.ty, high, low) .. " does not fit in "
            .. S.encode(ty), span)
    end
    local expr = self:expression(ctx, value)
    if not reinterprets then
        -- A run-time value that cannot fit the target is refused when it is converted. The check is
        -- needed for a bound of the source that the target cannot hold.
        local sourceMinHigh, sourceMinLow = S.minWordsOf(value.ty)
        local sourceMaxHigh, sourceMaxLow = S.maxWordsOf(value.ty)
        local minHigh, minLow = S.minWordsOf(ty)
        local maxHigh, maxLow = S.maxWordsOf(ty)
        -- A bound only needs a check when the source can go beyond it, which is a strict comparison.
        local compare = (S.isSigned(value.ty) or S.isSigned(ty)) and U64Kernel.slt or U64Kernel.lt
        if compare(sourceMinHigh, sourceMinLow, minHigh, minLow) then
            ctx.builder:emit(ctx.body, Ir.Trap(ctx.builder:bin("Lt", expr,
                self:constInt(ctx, value.ty, minHigh, minLow), S.Bool), "numeric-range"))
        end
        if compare(maxHigh, maxLow, sourceMaxHigh, sourceMaxLow) then
            ctx.builder:emit(ctx.body, Ir.Trap(ctx.builder:bin("Gt", expr,
                self:constInt(ctx, value.ty, maxHigh, maxLow), S.Bool), "numeric-range"))
        end
    end
    return V.ir(ctx.builder:convert(expr, ty), ty)
end

-- An integer constant of a type, which a 64-bit one holds as its two words.
function Eval:constInt(ctx, ty, high, low)
    if S.isWide(ty) then return ctx.builder:int64(ty, high, low) end
    return ctx.builder:int(ty, low)
end

function Eval:evalApply(ctx, expr)
    -- The invocation is in tail position when this call is the whole returned expression, but the
    -- callee and the arguments never are.
    local tail = ctx.tail
    ctx.tail = false
    local callee = self:evalExpr(ctx, expr.callee)
    if V.tag(callee) == "word" and callee.def.sliceOf and #callee.args == 0 and #expr.arguments == 1 then
        return self:evalSlice(ctx, expr.arguments[1])
    end
    if V.tag(callee) == "word" and callee.def.ptrOf and #callee.args == 0 and #expr.arguments == 1 then
        return self:evalPtr(ctx, expr.arguments[1])
    end
    if V.tag(callee) == "word" and callee.def.refOf and #callee.args == 0 and #expr.arguments == 1 then
        return self:evalRef(ctx, expr.arguments[1])
    end
    local args = self:evalArguments(ctx, expr.arguments, callee)
    ctx.tail = tail
    local tag = V.tag(callee)
    if tag == "word" then return self:apply(ctx, callee, args, expr.span) end
    if tag == "method" then return self:applyMethod(ctx, callee, args, expr.span) end
    if tag == "closure" then
        return self:applyClosure(ctx, callee.plan, nil, args, expr.span, callee.bound)
    end
    if tag == "ir" and S.isOwned(callee.ty) then
        return self:applyOwned(ctx, callee, args, expr.span)
    end
    if tag == "ir" and S.isView(callee.ty) then
        return self:applyView(ctx, callee, args, expr.span)
    end
    if (tag == "ir" or tag == "variant") and callee.ty and S.isTagged(callee.ty) then
        return self:applyTagged(ctx, callee, args, expr.span)
    end
    if tag == "type" then
        -- `Unit()` is the Unit value (syntax.md §1). An integer or float type converts; any other
        -- type is not a call.
        if callee.value == S.Unit then
            if #args ~= 0 then D.reject("arity", "Unit() takes no value", expr.span) end
            return V.unit()
        end
        if S.isInteger(callee.value) or S.isF64(callee.value) then
            return self:applyConversion(ctx, callee.value, args, expr.span)
        end
        D.reject("callable-required", S.encode(callee.value) .. " is a type, not a callable",
            expr.callee.span)
    end
    if tag == "ctor" then
        -- An alternative whose payload is not a record takes one positional argument; a Unit
        -- alternative takes none.
        if callee.caseType == S.Unit then
            if #args ~= 0 then D.reject("arity", "A Unit alternative takes no value", expr.span) end
            return self:makeVariant(ctx, callee, nil, expr.span)
        end
        if #args ~= 1 then D.reject("arity", "A variant constructor takes one value", expr.span) end
        self:requireAgainst(args[1], callee.caseType, expr.span)
        return self:makeVariant(ctx, callee, args[1], expr.span)
    end
    D.reject("callable-required", "Only words, methods and closures can be applied", expr.callee.span)
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
function Eval:foreignInstance(def, span)
    local existing = self.foreignInstances[def]
    if existing then return existing end
    local sc = scope(def.lexical)
    local plan, types, inputs = {}, {}, {}
    for index, param in ipairs(def.params) do
        local ty = self:requirement(def, index, sc, span)
        S.checkRuntime(ty, span)
        types[#types + 1] = ty
        inputs[#inputs + 1] = S.inValue(ty)
        plan[#plan + 1] = { kind = "value", position = index }
    end
    local declared, requirements = self:declaredResult(def, sc, span)
    if not declared or next(requirements or {}) ~= nil then
        D.reject("result-required", "Foreign word " .. def.name
            .. " needs a concrete result, as in `: U32`", span)
    end
    for _, ty in ipairs(declared) do
        if ty == false then
            D.reject("result-required", "Foreign word " .. def.name .. " needs a concrete result", span)
        end
        S.checkRuntime(ty, span)
    end
    -- A single `Unit` result is erased, exactly as a Wordlet result contract's Unit is: there is no
    -- value to carry, and emitting one would declare a `void` variable.
    if #declared == 1 and declared[1] == S.Unit then declared = {} end
    local instance = { target = def.symbol, def = def, foreign = true, inputPlan = plan,
        inputTypes = types, inputs = inputs, results = declared }
    self.foreignInstances[def] = instance
    self.foreignOrder[#self.foreignOrder + 1] = instance
    return instance
end

-- A foreign call is an effect the compiler cannot see into, so it exists only where there is code to
-- emit: it is never folded, and the reference interpreter has no binding to call.
function Eval:applyForeign(ctx, def, values, span)
    if ctx.mode ~= "residual" then
        D.reject("foreign-effect", "A foreign call exists only in compiled code: " .. def.name
            .. "; a constant argument does not make the host call foldable", span)
    end
    return self:emitCall(ctx, self:foreignInstance(def, span), values, span, nil)
end

function Eval:apply(ctx, word, args, span)
    local def = word.def
    if def.builtin then
        local bound = {}
        for _, value in ipairs(word.args) do bound[#bound + 1] = value end
        for _, value in ipairs(args) do bound[#bound + 1] = value end
        if #bound > #def.params then D.reject("arity", "Overapplication is not supported", span) end
        if #bound < #def.params then
            for _, value in ipairs(bound) do
                if not V.isStatic(value) then
                    D.reject("static-required", "A partial argument must be static", span)
                end
            end
            return V.word(def, bound, span)
        end
        return def.builtin(self, ctx, bound, span)
    end
    local bound = {}
    for _, value in ipairs(word.args) do bound[#bound + 1] = value end
    for _, value in ipairs(args) do bound[#bound + 1] = value end
    if #bound > #def.params then D.reject("arity", "Overapplication is not supported", span) end
    if def.keyed and #bound < #def.params then
        D.reject("keyed-required", "A keyed word is supplied by name, as in word { key = value }", span)
    end
    if #bound < #def.params then
        for index, value in ipairs(bound) do
            if not V.isStatic(value) then
                D.reject("static-required",
                    "Partial application needs a static value for parameter " .. def.params[index].name.text, span)
            end
        end
        return V.word(def, bound, span)
    end
    if def.foreign then return self:applyForeign(ctx, def, bound, span) end
    local allKnown, allStatic = true, true
    for _, value in ipairs(bound) do
        if not V.isKnown(value) then allKnown = false end
        if not V.isStatic(value) then allStatic = false end
    end
    if allKnown and (ctx.mode == "normalize" or allStatic) then
        -- Folding a known call is an optimization in residual code and a requirement in normalize
        -- code. A body that needs runtime storage cannot be folded and must instead be compiled, so
        -- the rejection is the signal to compile it; normalize code has no runtime code to fall
        -- back to, so for it the same rejection is the answer.
        if ctx.mode == "residual" then
            -- The attempt may have nested other folds, so the depth is restored either way before
            -- the call is compiled instead.
            local savedDepth = self.staticDepth
            local ok, value = pcall(self.applyStatically, self, def, bound, span, nil)
            self.staticDepth = savedDepth
            if ok then return value end
            if not (D.is(value) and (value.code == "runtime-in-normalization"
                or value.code == "static-depth" or value.code == "foreign-effect")) then
                error(value, 0)
            end
        else
            return self:applyStatically(def, bound, span, nil)
        end
    end
    if ctx.mode ~= "residual" then
        D.reject("runtime-in-normalization", "This call needs runtime storage or values", span)
    end
    return self:applyResidual(ctx, def, bound, span)
end

-- `Word { key = value }`: supply a word's keyed requirements. Values are evaluated in written
-- order; a name that is not a requirement, or one supplied twice, rejects. Supplying every key
-- invokes the body; otherwise the supplied values, which must be static, become part of a
-- specialized word that still awaits the rest.
function Eval:applyKeyed(ctx, word, fields, span, tail)
    local def = word.def
    local params = def.params
    local known = {}
    for _, param in ipairs(params) do known[param.name.text] = true end
    local bound = {}
    for name, value in pairs(def.statics or {}) do bound[name] = value end
    for _, field in ipairs(fields) do
        local name = field.name.text
        if not known[name] then
            D.reject("unknown-member", "Word " .. def.name .. " has no keyed requirement " .. name,
                field.name.span)
        end
        if bound[name] ~= nil then
            D.reject("duplicate", "Keyed requirement " .. name .. " is supplied twice", field.name.span)
        end
        bound[name] = self:evalExpr(ctx, field.value)
    end
    local remaining = {}
    for _, param in ipairs(params) do
        if bound[param.name.text] == nil then remaining[#remaining + 1] = param end
    end
    if #remaining == 0 then
        local values = {}
        for index, param in ipairs(params) do values[index] = bound[param.name.text] end
        ctx.tail = tail and true or false
        return self:apply(ctx, V.word(def, values, span), {}, span)
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
    return V.word(specialized, {}, span)
end

function Eval:applyMethod(ctx, method, args, span)
    local def, receiver = method.def, method.receiver
    local bound = {}
    for _, value in ipairs(method.args or {}) do bound[#bound + 1] = value end
    for _, value in ipairs(args) do bound[#bound + 1] = value end
    if #bound > #def.params then D.reject("arity", "Overapplication is not supported", span) end
    if #bound < #def.params then
        for index, value in ipairs(bound) do
            if not V.isStatic(value) then
                D.reject("static-required",
                    "Partial application needs a static value for parameter " .. def.params[index].name.text, span)
            end
        end
        return setmetatable({ tag = "method", def = def, receiver = receiver, args = bound }, V.mt)
    end
    if not receiver then
        D.reject("missing-receiver", "Bind the receiver before calling " .. def.name, span)
    end
    local allKnown = true
    for _, value in ipairs(bound) do if not V.isKnown(value) then allKnown = false end end
    if allKnown and V.tag(receiver) == "record" then
        -- A method body that needs runtime storage is compiled rather than folded, for the same
        -- reason a word call is.
        if ctx.mode == "residual" then
            local savedDepth = self.staticDepth
            local ok, value = pcall(self.applyStatically, self, def, bound, span, receiver)
            self.staticDepth = savedDepth
            if ok then return value end
            if not (D.is(value) and (value.code == "runtime-in-normalization"
                or value.code == "static-depth" or value.code == "foreign-effect")) then
                error(value, 0)
            end
        else
            return self:applyStatically(def, bound, span, receiver)
        end
    end
    if ctx.mode ~= "residual" then
        D.reject("runtime-in-normalization", "This method call needs runtime storage", span)
    end
    return self:applyMethodResidual(ctx, def, bound, receiver, span)
end

-- Shared scope construction: parameters, and receiver fields for methods.
function Eval:parameterScope(def, values, receiver)
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
    for index, param in ipairs(def.params) do
        -- Check each requirement against the supplied value before binding the next parameter,
        -- since a later annotation may depend on an earlier parameter.
        local ty = self:requirement(def, index, sc, def.span)
        local value = self:copyArgument(values[index])
        if value then self:requireAgainst(value, ty, param.span) end
        declare(sc, param.name.text, { kind = "value", name = param.name.text, value = value }, param.span)
    end
    return sc
end

-- Ordinary parameter binding copies record data; a local alias keeps its instance, an argument
-- does not. Field values are immutable, so a shallow copy of the field table is a value copy.
function Eval:copyArgument(value)
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

function Eval:applyStatically(def, values, span, receiver)
    self:enterStatic(def, span)
    local sc = self:parameterScope(def, values, receiver)
    local declared, requirements = self:declaredResult(def, sc, span)
    local ctx = self:context("normalize", sc, span)
    ctx.expectedResult = self:resultExpectation(requirements)
    local result = self:execBody(ctx, def.body, span)
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
            local actual = result[index]
            self:requireResultSignature(actual, requirement, span)
        end
    end
    self:leaveStatic()
    if #result == 0 then return V.unit() end
    if #result == 1 then return result[1] end
    return V.results(result)
end

function Eval:applyResidual(ctx, def, values, span)
    local instance = self:instanceFor(def, span, values)
    if instance.status == "building" and not instance.results then
        D.reject("recursive-result", "Recursive word " .. def.name .. " needs an explicit result annotation", span)
    end
    -- A tail call to the instance currently being built is a back edge, not a recursive call.
    -- A block with a pending deferred action does not become a loop: the action runs after the call
    -- returns and before the value leaves, which is not the order a back edge would give.
    if ctx.tail and not ctx.deferFrame and ctx.instance == instance and instance.loopTargets then
        self:emitLoopBack(ctx, instance, values, span)
        return V.unit()
    end
    return self:emitCall(ctx, instance, values, span, nil)
end

-- Evaluate every next argument before assigning any parameter, then transfer to the loop head.
function Eval:emitLoopBack(ctx, instance, values, span)
    local builder = ctx.builder
    local temporaries = {}
    for index, target in ipairs(instance.loopTargets) do
        local value = values[target.position]
        self:requireType(value, target.ty, span)
        local id = builder:valueId()
        builder:emit(ctx.body, Ir.Let(id, target.ty, self:expression(ctx, value)))
        temporaries[index] = builder:ref(id, target.ty)
    end
    for index, target in ipairs(instance.loopTargets) do
        builder:store(ctx.body, Ir.Local(target.storage), temporaries[index])
    end
    builder:emit(ctx.body, Ir.Next)
    instance.loopBack = true
    ctx.terminated = true
end

function Eval:applyMethodResidual(ctx, def, values, receiver, span)
    local instance = self:instanceFor(def, span, values, receiver)
    if instance.status == "building" and not instance.results then
        D.reject("recursive-result", "Recursive method " .. def.name .. " needs an explicit result annotation", span)
    end
    return self:emitCall(ctx, instance, values, span, receiver)
end

-- Builds the argument list from the instance's input plan.
function Eval:emitCall(ctx, instance, values, span, receiver)
    local builder = ctx.builder
    local args = {}
    for index, input in ipairs(instance.inputPlan) do
        if input.kind == "place" then
            -- A borrowed receiver must be a place; a record still carrying its construction
            -- expression materialises once here.
            args[#args + 1] = Ir.BorrowArg(self:recordPlace(ctx, receiver, span))
        else
            args[#args + 1] = Ir.ValueArg(self:expression(ctx, values[input.position],
                instance.inputTypes[index]))
        end
    end
    local runtime = instance.runtimeResults or self:runtimeResults(instance.results)
    local results = {}
    for _ = 1, #runtime do results[#results + 1] = builder:valueId() end
    builder:emit(ctx.body, Ir.Call(S.list(results), instance.target, S.list(args)))
    local ir = {}
    for index, ty in ipairs(runtime) do
        ir[index] = V.ir(builder:ref(results[index], ty), ty)
    end
    local out = self:logicalResults(instance.results, ir)
    if #out == 0 then return V.unit() end
    if #out == 1 then return out[1] end
    return V.results(out)
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
            parts[#parts + 1] = (ty and S.isOwned(ty)) and ("!" .. ty.entry) or "*"
        end
    end
    return table.concat(parts, "/")
end

function Eval:instanceFor(def, span, values, receiver)
    values = values or {}
    local key = self:instanceKey(def, values, receiver)
    local existing = self.instances[key]
    if existing then return existing end
    local count = 0
    for _ in pairs(self.instances) do count = count + 1 end
    if count >= (self.limits.keys or 1024) then D.resource("keys", "Residual instance budget exhausted", span) end
    return self:buildInstance(key, def, values, span, receiver)
end

function Eval:loopTarget(instance, position, storage, ty)
    instance.loopTargets = instance.loopTargets or {}
    instance.loopTargets[#instance.loopTargets + 1] = { position = position, storage = storage, ty = ty }
end

function Eval:buildInstance(key, def, values, span, receiver)
    self:enterBuild(span)
    self.nextFn = self.nextFn + 1
    local instance = { key = key, def = def, target = "wordletfn_" .. self.nextFn,
        status = "building", args = values, inputPlan = {}, inputTypes = {} }
    self.instances[key] = instance
    self.order[#self.order + 1] = instance

    local body, setup = {}, {}
    local builder = IR.builder({ id = instance.target })
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

    for index, param in ipairs(def.params) do
        local ty = self:requirement(def, index, sc, span)
        if S.isSig(ty) then
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
            elseif supplied ~= nil and V.tag(supplied) == "ir" and S.isOwned(supplied.ty) then
                ty = supplied.ty
            elseif supplied ~= nil and V.tag(supplied) == "ir" and S.isView(supplied.ty) then
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
            -- `Type` and the other compile-time descriptors have no runtime representation, so a
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
        if ty == S.Unit then
            -- Erased exactly like a Unit result: no input, no ABI slot, name bound directly.
            declare(sc, param.name.text, { kind = "value", name = param.name.text, value = V.unit() }, param.span)
            goto continue
        end
        do
        local supplied = values[index]
        -- A supplied argument is checked against the requirement here whichever branch binds it. The
        -- static branch below already did; a run-time argument used to reach the IR checker unchecked,
        -- where a wrong type was reported as a compiler bug instead of a source error.
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
            if S.isArray(ty) then
                -- A by-value array parameter owns fresh storage only when an element is addressed;
                -- a whole-value use reads the input directly.
                declare(sc, param.name.text, { kind = "value", name = param.name.text,
                    value = V.array(ty, nil, nil, false, builder:ref(value, ty), setup) }, param.span)
            elseif S.isRecord(ty) then
                -- A by-value record parameter owns fresh storage only when a write or an address
                -- demands one, so a read-only parameter reads the input directly. A loop-carried
                -- parameter needs its storage up front because the back edge names it.
                local fields = { fields = S.fieldsOf(ty),
                    fieldNames = S.fieldNames(ty), statics = {}, readonly = {}, methods = {}, type = ty }
                if def.tailSelf then
                    local storage = builder:storageId()
                    setup[#setup + 1] = Ir.Var(storage, ty, builder:ref(value, ty))
                    declare(sc, param.name.text, { kind = "value", name = param.name.text,
                        value = V.object(ty, Ir.Local(storage), fields) }, param.span)
                    self:loopTarget(instance, index, storage, ty)
                else
                    declare(sc, param.name.text, { kind = "value", name = param.name.text,
                        value = V.object(ty, nil, fields, nil, false, builder:ref(value, ty), setup) },
                        param.span)
                end
            elseif def.tailSelf then
                -- Loop-carried parameters need mutable storage so a back edge can rebind them.
                local storage = builder:storageId()
                setup[#setup + 1] = Ir.Var(storage, ty, builder:ref(value, ty))
                self:loopTarget(instance, index, storage, ty)
                -- A value parameter is immutable, so one read per iteration is equivalent to reading at
                -- every mention. Sharing the read is what lets expressions built from the parameter be
                -- shared too, because reads are never interned.
                local read = builder:valueId()
                instance.loopHeader = instance.loopHeader or {}
                instance.loopHeader[#instance.loopHeader + 1] = Ir.Read(read, ty, Ir.Local(storage))
                declare(sc, param.name.text, { kind = "value", name = param.name.text,
                    value = V.ir(builder:ref(read, ty), ty) }, param.span)
            else
                declare(sc, param.name.text, { kind = "value", name = param.name.text,
                    value = V.ir(builder:ref(value, ty), ty) }, param.span)
            end
        end
        end
        ::continue::
    end

    local declared, requirements = self:declaredResult(def, sc, span)
    instance.results, instance.resultRequirements = declared, requirements
    local ctx = setmetatable({ session = self, mode = "residual", scope = sc, span = span,
        builder = builder, body = body, fn = { id = instance.target }, instance = instance,
        expectedResult = self:resultExpectation(requirements) }, Ctx)
    self:execBodyResidual(ctx, def.body, span)
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
    self:leaveBuild()
    instance.status = "done"
    return instance
end

-- A result annotation that is a signature states what the returned callable must look like, not a
-- concrete type: the body fixes the code identity, so that slot stays open until the body returns.
function Eval:declaredResult(def, sc, span)
    local result = def.result
    if not result then return nil, nil end
    sc = sc or def.lexical
    local expressions = {}
    if result.kind == "Single" then
        expressions[1] = result.type
    else
        for index, item in ipairs(result.types) do expressions[index] = item end
    end
    local types, requirements = {}, {}
    for index, expr in ipairs(expressions) do
        local ty = self:typeOf(expr, sc, span)
        if S.isSig(ty) then
            types[index], requirements[index] = false, ty
        else
            S.checkRuntime(ty, span)
            types[index] = ty
        end
    end
    if next(requirements) == nil then return types, nil end
    return types, requirements
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

function Eval:execBody(ctx, body, span)
    if body.kind == "Expression" then
        local value = self:evalExpected(ctx, body.value, ctx.expectedResult)
        local values = self:expand(value)
        self:checkReturn(values, span)
        return values
    end
    ctx.result = nil
    local returned = self:execBlock(ctx, body.statements)
    if not returned then D.reject("no-return", "Every reachable path must return a value", span) end
    return ctx.result
end

function Eval:execBodyResidual(ctx, body, span)
    if body.kind == "Expression" then
        ctx.tail, ctx.terminated = true, false
        local value = self:evalExpected(ctx, body.value, ctx.expectedResult)
        if ctx.terminated then return end
        ctx.tail = false
        local values = self:expand(value)
        self:checkReturn(values, span)
        ctx.builder:return_(ctx.body, self:materializeAll(ctx, values,
            ctx.instance and ctx.instance.results or nil))
        ctx.resultTypes = {}
        for index, item in ipairs(values) do ctx.resultTypes[index] = item.ty end
        return
    end
    local returned = self:execBlock(ctx, body.statements)
    if not returned then D.reject("no-return", "Every reachable path must return a value", span) end
end

return M
