-- Verification of well-formed IR. Reaching a `bug` here means the builder produced something
-- inconsistent; source mistakes are rejected earlier with spans.
local S = require("wordlet.schema")
local IR = require("wordlet.ir")
local D = require("wordlet.diag")
local M = {}

local Ir = S.Ir

-- A statement list falls through unless its last statement definitely terminates.
local function falls(list)
    if #list == 0 then return true end
    local last = list[#list]
    local kind = last.kind
    if kind == "Return" or kind == "Trap" or kind == "Next" then return false end
    if kind == "Loop" then return false end
    if kind == "If" then return falls(last.yes) or falls(last.no) end
    if kind == "Switch" then
        -- A switch falls through only if some case can fall; it selects exactly one case.
        for _, case in ipairs(last.cases) do if falls(case.body) then return true end end
        return false
    end
    return true
end
M.falls = falls

function M.function_(fn, definitions, seeded)
    -- `visible` is the set of values in scope at this point. Arm bodies get a copy so an
    -- arm-local definition cannot be referenced from the continuation.
    -- `visible` maps each value in scope to its type, so later statements can cross-check the
    -- values they refer to. Only truthiness of the entry is used for scope tests.
    local function bind(visible, id, ty)
        if visible[id] then D.bug("value-duplicate", "IR defines value " .. id .. " twice") end
        visible[id] = ty or true
    end
    -- Arm bodies get a copy of the scope; the mapped types must travel with it.
    local function copy(set)
        local out = {}
        for key, value in pairs(set) do out[key] = value end
        return out
    end

    -- The storage a place reads or writes through: a projection or an index reaches the same cell,
    -- so the local at the end of the base chain is what must have a value. A view element names a
    -- view value rather than a cell, so it roots nowhere.

    -- The storages every one of these arm sets established. Each arm set starts from the incoming
    -- one, so an id already initialized is in all of them unless an arm is missing.
    local function everyArm(sets)
        local kept = {}
        for id in pairs(sets[1] or {}) do
            local inEvery = true
            for index = 2, #sets do
                if not sets[index][id] then inEvery = false; break end
            end
            if inEvery then kept[id] = true end
        end
        return kept
    end

    -- Replace a set's contents with another's, so callers that hold the same table see the change.
    local function replace(target, source)
        for id in pairs(target) do if not source[id] then target[id] = nil end end
        for id in pairs(source) do target[id] = true end
    end

    local function rootOf(place)
        while place do
            if place.kind == "Local" then return place.storage.id end
            if place.kind == "Project" or place.kind == "Deref" or place.kind == "Index" then
                place = place.base
            else
                return nil
            end
        end
        return nil
    end
    -- `initialized` is the set of storages that have a value on every path to the current
    -- statement; it is narrowed by an `If` or a `Switch` and never widened by a `Loop`.

    local function checkList(list, visible, storages, inLoop, initialized)
        for _, stmt in ipairs(list) do
            local kind = stmt.kind
            if kind == "Let" then
                if M.expr(stmt.expr, visible, storages) ~= stmt.type then
                    D.bug("ir-type", "Let type does not match its expression")
                end
                bind(visible, stmt.value.id, stmt.type)
            elseif kind == "Read" then
                local placeType = M.place(stmt.place, storages, visible)
                if placeType ~= stmt.type then
                    D.bug("ir-type", "Read type does not match the place's type")
                end
                if stmt.place.kind == "Local" and not storages[stmt.place.storage.id] then
                    D.bug("ir-place", "Read of undeclared storage " .. stmt.place.storage.id)
                end
                local root = rootOf(stmt.place)
                if root and not initialized[root] then
                    D.bug("ir-initialized", "Read of storage " .. root
                        .. " whose value is not established on every path to it")
                end
                bind(visible, stmt.value.id, stmt.type)
            elseif kind == "Var" then
                storages[stmt.storage.id] = stmt.type
                if stmt.initial then
                    if M.expr(stmt.initial, visible, storages) ~= stmt.type then
                        D.bug("ir-type", "Var initialiser does not match the storage type")
                    end
                    initialized[stmt.storage.id] = true
                end
            elseif kind == "Store" then
                local placeType = M.place(stmt.place, storages, visible)
                if M.expr(stmt.value, visible, storages) ~= placeType then
                    D.bug("ir-type", "Store value does not match the place's type")
                end
                local root = rootOf(stmt.place)
                if root then initialized[root] = true end
            elseif kind == "If" then
                M.expr(stmt.test, visible, storages)
                -- A storage has a value after the `If` only if both arms gave it one. Each arm set
                -- starts from the incoming one, so this also keeps anything already initialized,
                -- and it *adds* a storage both arms stored to even though it had no initializer:
                -- that is exactly the if-expression result storage, declared, stored by each arm,
                -- and then read.
                local yesInitialized, noInitialized = copy(initialized), copy(initialized)
                checkList(stmt.yes, copy(visible), storages, inLoop, yesInitialized)
                checkList(stmt.no, copy(visible), storages, inLoop, noInitialized)
                -- Only an arm that reaches the continuation takes part: an arm ending in `Next`,
                -- `Return` or `Trap` transfers control away, and an empty arm passes the incoming
                -- set through, which its copy already holds.
                local reaching = {}
                if falls(stmt.yes) then reaching[#reaching + 1] = yesInitialized end
                if falls(stmt.no) then reaching[#reaching + 1] = noInitialized end
                if #reaching > 0 then replace(initialized, everyArm(reaching)) end
            elseif kind == "Switch" then
                if not stmt.sum:isTaggedType() then D.bug("ir-type", "Switch needs a sum type") end
                if visible[stmt.variant.id] ~= stmt.sum then
                    D.bug("ir-type", "Switch tests a value that is not of that sum type")
                end
                -- The set after the `Switch` is what every arm established. A case the builder
                -- omitted would fall through with the incoming set, so a switch that does not
                -- name every alternative keeps only what was already initialized.
                local incoming, reaching = copy(initialized), {}
                for _, case in ipairs(stmt.cases) do
                    if not S.caseOf(stmt.sum, case.tag) then
                        D.bug("ir-type", "Switch has no alternative " .. case.tag)
                    end
                    local arm = copy(initialized)
                    checkList(case.body, copy(visible), storages, inLoop, arm)
                    -- A case body that transfers control does not reach the continuation.
                    if falls(case.body) then reaching[#reaching + 1] = arm end
                end
                -- An alternative the builder did not name falls through with the incoming set.
                if #stmt.cases < #S.alternatives(stmt.sum) then reaching[#reaching + 1] = incoming end
                if #reaching > 0 then replace(initialized, everyArm(reaching)) end
            elseif kind == "Loop" then
                -- A self-tail call becomes a `Loop`. The emitter puts the continuation inside the
                -- `for (;;)`, so falling off the end of the body reaches the statements after the
                -- loop with whatever the body's fall-through established, while a `Next` starts the
                -- next iteration from the set the loop was entered with -- which is why the body
                -- starts from the incoming set: a storage only the back edge gave a value is not
                -- initialized on the first iteration.
                local bodyEnd = copy(initialized)
                checkList(stmt.body, copy(visible), storages, true, bodyEnd)
                replace(initialized, bodyEnd)
            elseif kind == "Call" or kind == "Indirect" then
                local target = definitions[stmt.target]
                if kind == "Call" and not target then
                    D.bug("ir-target", "Call to unknown function " .. stmt.target)
                end
                if target and #stmt.results ~= #target.results then
                    D.bug("ir-arity", "Call result count does not match " .. stmt.target)
                end
                if kind == "Indirect" then
                    local callable = M.expr(stmt.callable, visible, storages)
                    if not callable:isView() then D.bug("ir-type", "Indirect needs a view-typed callable") end
                    if #stmt.results ~= #callable.visible.results then
                        D.bug("ir-arity", "Indirect result count does not match the view's signature")
                    end
                    for index, arg in ipairs(stmt.arguments) do
                        local input = callable.visible.inputs[index]
                        if not input then D.bug("ir-arity", "Indirect passes too many arguments") end
                        if M.arg(arg, visible, storages) ~= input.type then
                            D.bug("ir-type", "Indirect argument does not match the view's input")
                        end
                    end
                    if #stmt.arguments ~= #callable.visible.inputs then
                        D.bug("ir-arity", "Indirect argument count does not match the view's signature")
                    end
                    for index, result in ipairs(stmt.results) do
                        bind(visible, result.id, callable.visible.results[index])
                    end
                end
                for index, arg in ipairs(stmt.arguments) do
                    -- The argument is checked once, and its type is what the target input is compared
                    -- against; re-deriving it here would check the same node twice.
                    local argType = M.arg(arg, visible, storages)
                    if target then
                        local input = target.inputs[index]
                        if not input then
                            D.bug("ir-arity", "Call passes more arguments than " .. stmt.target .. " accepts")
                        end
                        if input.kind == "InValue" and arg.kind ~= "ValueArg" then
                            D.bug("ir-arg", "A by-value input needs a value argument")
                        end
                        if input.kind == "InPlace" and arg.kind ~= "BorrowArg" then
                            D.bug("ir-arg", "A borrowed input needs a place argument")
                        end
                        if argType ~= input.type then
                            D.bug("ir-type", "Call argument type does not match the target input")
                        end
                    end
                end
                if target and #stmt.arguments ~= #target.inputs then
                    D.bug("ir-arity", "Call argument count does not match " .. stmt.target)
                end
                if kind == "Call" then
                    for index, result in ipairs(stmt.results) do
                        bind(visible, result.id, target.results[index])
                    end
                end
            elseif kind == "View" then
                -- A view binds a known callable's hidden prefix in a local adapter, or represents
                -- pure code: an owned callable with an empty environment and no bound prefix.
                if not stmt.type:isView() and not (stmt.type:isOwned()
                    and S.environmentOf(stmt.type) == S.Unit) then
                    D.bug("ir-type", "View needs a view or an empty-environment callable type")
                end
                local target = definitions[stmt.entry]
                if not target then D.bug("ir-target", "View binds unknown code " .. stmt.entry) end
                if #stmt.slots > #target.inputs then
                    D.bug("ir-arity", "View binds more inputs than " .. stmt.entry .. " has")
                end
                for index, slot in ipairs(stmt.slots) do
                    local input = target.inputs[index]
                    if input.kind == "InValue" and slot.kind ~= "ValueArg" then
                        D.bug("ir-arg", "A by-value hidden input needs a value slot")
                    end
                    if input.kind == "InPlace" and slot.kind ~= "BorrowArg" then
                        D.bug("ir-arg", "A borrowed hidden input needs a place slot")
                    end
                    if slot.kind == "ValueArg" and M.expr(slot.value, visible, storages) ~= input.type then
                        D.bug("ir-type", "View slot type does not match the hidden input")
                    end
                    if slot.kind == "BorrowArg" and M.place(slot.place, storages, visible) ~= input.type then
                        D.bug("ir-type", "View slot place does not match the hidden input")
                    end
                end
                -- The visible remainder must match the view's signature.
                for index, input in ipairs(stmt.type.visible.inputs) do
                    local hidden = target.inputs[#stmt.slots + index]
                    -- Both are interned `Ty.Input` values, so identity is the comparison.
                    if hidden == nil or hidden ~= input then
                        D.bug("ir-type", "View signature does not match the remaining inputs")
                    end
                end
                bind(visible, stmt.value.id, stmt.type)
            elseif kind == "ConstructVariant" then
                if not stmt.type:isTaggedType() then
                    D.bug("ir-type", "ConstructVariant needs a sum or tagged type")
                end
                local caseType = S.caseOf(stmt.type, stmt.tag)
                if not caseType then D.bug("ir-type", "Sum type has no alternative " .. stmt.tag) end
                if caseType == S.Unit then
                    if stmt.payload then
                        D.bug("ir-type", "A Unit alternative must not carry a payload")
                    end
                else
                    if not stmt.payload then
                        D.bug("ir-type", "Alternative " .. stmt.tag .. " needs a payload")
                    end
                    if M.expr(stmt.payload, visible, storages) ~= caseType then
                        D.bug("ir-type", "Variant payload does not match alternative " .. stmt.tag)
                    end
                end
                bind(visible, stmt.value.id, stmt.type)
            elseif kind == "VariantMatches" then
                if not stmt.sum:isTaggedType() then
                    D.bug("ir-type", "VariantMatches needs a sum or tagged type")
                end
                if not S.caseOf(stmt.sum, stmt.tag) then
                    D.bug("ir-type", "Sum type has no alternative " .. stmt.tag)
                end
                if visible[stmt.variant.id] ~= stmt.sum then
                    D.bug("ir-type", "VariantMatches tests a value that is not of that sum type")
                end
                bind(visible, stmt.value.id, S.Bool)
            elseif kind == "VariantPayload" then
                local caseType = S.caseOf(stmt.sum, stmt.tag)
                if not caseType then D.bug("ir-type", "Sum type has no alternative " .. stmt.tag) end
                if caseType == S.Unit then
                    D.bug("ir-type", "A Unit alternative has no payload to project")
                end
                if visible[stmt.variant.id] ~= stmt.sum then
                    D.bug("ir-type", "VariantPayload projects a value that is not of that sum type")
                end
                bind(visible, stmt.value.id, caseType)
            elseif kind == "Trap" then
                M.expr(stmt.failure, visible, storages)
            elseif kind == "Return" then
                if #stmt.values ~= #fn.results then
                    D.bug("ir-return", "Function " .. fn.id .. " returns " .. #stmt.values
                        .. " values but declares " .. #fn.results)
                end
                for index, value in ipairs(stmt.values) do
                    if M.expr(value, visible, storages) ~= fn.results[index] then
                        D.bug("ir-return", "Returned value type does not match the declared result")
                    end
                end
            elseif kind == "Next" then
                if not inLoop then D.bug("ir-next", "Next appears outside any Loop") end
            else
                D.bug("ir-stmt", "Unknown statement variant " .. tostring(kind))
            end
        end
    end
    local visible = {}
    for _, param in ipairs(fn.params) do
        if param.kind ~= "ValueParam" and param.kind ~= "PlaceParam" then
            D.bug("ir-param", "Unknown parameter variant " .. tostring(param.kind))
        end
        if param.kind == "ValueParam" then bind(visible, param.binding.id, param.type) end
    end
    -- A module-level storage and a borrowed place parameter both hold a value when the function is

    -- entered, so they start initialized; a `Var` adds its own storage only when it has an

    -- initializer (interfaces.md §6 item 3).

    local storages, initialized = {}, {}
    for id, ty in pairs(seeded or {}) do storages[id], initialized[id] = ty, true end
    for _, param in ipairs(fn.params) do
        if param.kind == "PlaceParam" then
            storages[param.binding.id], initialized[param.binding.id] = param.type, true
        end
    end
    checkList(fn.body, visible, storages, nil, initialized)
    if falls(fn.body) then
        D.bug("ir-fallthrough", "Function " .. fn.id .. " can fall through without returning")
    end
    return true
end

function M.expr(expr, locals, storages)
    local kind = expr.kind
    if kind == "Const" then
        if expr.type:isInteger() then
            if expr.literal.kind == "UInt64" then
                -- A two-word constant is only meaningful for a 64-bit type.
                if not expr.type:isWide() then
                    D.bug("ir-literal", "A two-word constant needs a 64-bit type")
                end
            elseif expr.literal.kind ~= "UInt" then
                D.bug("ir-literal", "An integer constant needs a UInt literal")
            elseif expr.type:isWide() then
                -- A one-word constant of a 64-bit type has to be a word.
                if expr.literal.value > 4294967295 then
                    D.bug("ir-literal", "A one-word constant is out of range")
                end
            elseif expr.literal.value > S.maxOf(expr.type) then
                D.bug("ir-literal", "A constant does not fit in its own width")
            end
        elseif expr.type == S.F64 then
            if expr.literal.kind ~= "Float" then D.bug("ir-literal", "F64 constant needs a Float literal") end
        elseif expr.type == S.Bool then
            if expr.literal.kind ~= "Boolean" then D.bug("ir-literal", "Bool constant needs a Boolean literal") end
        elseif expr.type:isSlice() then
            -- A byte slice is the one aggregate with a literal spelling, and its bytes are the
            -- constant. Any other element type has no literal, so a Str there is a compiler bug.
            if expr.literal.kind ~= "Str" then
                D.bug("ir-literal", "A slice constant needs a string literal")
            end
            if not expr.type:isString() then
                D.bug("ir-literal", "Only a byte slice has a literal spelling")
            end
        else
            D.bug("ir-const", "Unsupported constant type " .. S.encode(expr.type))
        end
        return expr.type
    elseif kind == "Ref" then
        if not locals[expr.value.id] then
            D.bug("ir-scope", "Reference to value " .. expr.value.id .. " is not in scope")
        end
        return expr.type
    elseif kind == "Make" then
        if expr.type:isSlice() then
            -- A slice is a data pointer and a length. The pointer is an ordinary reference to the
            -- element, so constructing a view needs no new kind of value.
            if #expr.fields ~= 2 then D.bug("ir-arity", "A slice needs a data pointer and a length") end
            local data = M.expr(expr.fields[1], locals, storages)
            if not data:isRef() or data.target ~= expr.type.element then
                D.bug("ir-type", "Slice data must be a reference to the element type")
            end
            if M.expr(expr.fields[2], locals, storages) ~= S.U32 then
                D.bug("ir-type", "A slice length is a U32")
            end
            return expr.type
        end
        local record = S.environmentOf(expr.type)
        if record:isArray() then
            if #expr.fields ~= record.length then
                D.bug("ir-arity", "Make element count " .. #expr.fields .. " does not match the array length "
                    .. record.length .. " of " .. S.encode(expr.type))
            end
            for _, item in ipairs(expr.fields) do
                if M.expr(item, locals, storages) ~= record.element then
                    D.bug("ir-type", "Make element type does not match the array element")
                end
            end
            return expr.type
        end
        if not record:isRecord() then D.bug("ir-type", "Make needs a record or callable type") end
        if #expr.fields ~= #record.fields then
            D.bug("ir-arity", "Make field count does not match the record type")
        end
        for index, field in ipairs(record.fields) do
            if M.expr(expr.fields[index], locals, storages) ~= field.type then
                D.bug("ir-type", "Make field type does not match " .. field.name)
            end
        end
        return expr.type
    elseif kind == "Addr" then
        -- An address is a pure computation over a place: it reads nothing. The same node serves a
        -- reference and a raw pointer, because they share a representation and differ only in a
        -- lifetime rule the checker does not decide, so only the recorded type is verified here.
        if not expr.type:isRef() and not expr.type:isPtr() then
            D.bug("ir-type", "Addr needs a reference or a pointer type")
        end
        local placeType = M.place(expr.place, storages, locals)
        if placeType == nil then D.bug("ir-place", "Addr needs a place with a known type") end
        if not expr.type.target:isNamed() and placeType ~= expr.type.target then
            D.bug("ir-type", "Addr place type does not match the address target")
        end
        return expr.type
    elseif kind == "Get" then
        local aggregate = S.environmentOf(M.expr(expr.aggregate, locals, storages))
        if not aggregate:isRecord() then D.bug("ir-type", "Get needs a record aggregate") end
        local field = S.field(aggregate, expr.field.name)
        if not field then D.bug("ir-field", "Get names an unknown field " .. expr.field.name) end
        if field ~= expr.type then D.bug("ir-type", "Get type does not match the field type") end
        return expr.type
    elseif kind == "Convert" then
        -- A conversion is between integer widths, or between an integer and F64, and its type is what
        -- it converts to.
        local operand = M.expr(expr.operand, locals, storages)
        if not ((operand:isInteger() and expr.type:isInteger())
            or (operand:isF64() ~= expr.type:isF64())) then
            D.bug("ir-type", "Convert needs two integer widths, or one integer and F64")
        end
        return expr.type
    elseif kind == "Un" then
        local operand = M.expr(expr.operand, locals, storages)
        local op = expr.op.kind
        if op == "Not" then
            if operand ~= S.Bool or expr.type ~= S.Bool then D.bug("ir-type", "Not requires Bool") end
        elseif op == "Neg" or op == "BitNot" then
            -- F64 has negation but no complement: IEEE defines no bitwise operation on a double.
            local doubleNegation = op == "Neg" and operand:isF64() and operand == expr.type
            if not doubleNegation and (not operand:isInteger() or operand ~= expr.type) then
                D.bug("ir-type", "Unary " .. op .. " requires one integer width")
            end
        else
            D.bug("ir-op", "Unknown unary operation " .. tostring(op))
        end
        return expr.type
    elseif kind == "Bin" then
        local left = M.expr(expr.left, locals, storages)
        local right = M.expr(expr.right, locals, storages)
        local op = expr.op.kind
        local arithmetic = { Add = true, Sub = true, Mul = true, Div = true, Rem = true, Pow = true,
            BitAnd = true, BitOr = true, BitXor = true }
        if arithmetic[op] then
            -- F64 is one type on both sides too, but it has no remainder and no power: IEEE puts
            -- those outside the arithmetic operators rather than making them a rounding question.
            if not (left:isInteger() or left:isF64()) or left ~= right or expr.type ~= left then
                D.bug("ir-type", "Arithmetic " .. op .. " requires one integer width or F64 on both sides")
            end
            if left:isF64() and op ~= "Add" and op ~= "Sub" and op ~= "Mul" and op ~= "Div" then
                D.bug("ir-op", "F64 has no " .. op .. " operator")
            end
        elseif op == "Shl" or op == "Shr" then
            -- The amount is a plain U32; the value keeps its own width.
            if not left:isInteger() or right ~= S.U32 or expr.type ~= left then
                D.bug("ir-type", "A shift needs an integer value and a U32 amount")
            end
        elseif op == "Eq" or op == "Ne" then
            if left ~= right or expr.type ~= S.Bool then D.bug("ir-type", "Equality requires matching types") end
        elseif op == "Lt" or op == "Le" or op == "Gt" or op == "Ge" then
            -- F64 orders as IEEE does, which is what C's operators already implement.
            if not (left:isInteger() or left:isF64()) or left ~= right or expr.type ~= S.Bool then
                D.bug("ir-type", "Ordering requires two integers or two F64 values")
            end
        else
            D.bug("ir-op", "Unknown binary operation " .. tostring(op))
        end
        return expr.type
    elseif kind == "Null" then
        -- The null pointer of a Ptr type, and of nothing else: there is no null reference.
        if not expr.type:isPtr() then D.bug("ir-type", "Null needs a Ptr type") end
        return expr.type
    elseif kind == "SliceLength" then
        local view = S.environmentOf(M.expr(expr.view, locals, storages))
        if not view:isSlice() then D.bug("ir-type", "SliceLength needs a slice view") end
        if expr.type ~= S.U32 then D.bug("ir-type", "A slice length is a U32") end
        return expr.type
    end
    D.bug("ir-expr", "Unknown expression variant " .. tostring(kind))
end

-- Returns the type the place refers to, or nil for places without a known type yet.
function M.place(place, storages, locals)
    local kind = place.kind
    if kind == "Index" then
        -- The element type is recorded on the node, so the base only has to be an array of it and the
        -- index has to be a U32.
        local base = M.place(place.base, storages, locals)
        if not base:isArray() then D.bug("ir-place", "Index needs an array base") end
        if base.element ~= place.type then D.bug("ir-type", "Index element type does not match") end
        if M.expr(place.index, locals, storages) ~= S.U32 then
            D.bug("ir-type", "Index needs a U32 index")
        end
        return place.type
    end
    if kind == "Deref" then
        -- A reference names the place it points at. The pointee type is recorded on the node, and
        -- the base must itself be a place holding a reference.
        local base = M.place(place.base, storages, locals)
        -- Deref is the route through a reference *or* a raw pointer: they share a representation, and
        -- the difference between them is a lifetime rule this checker does not decide.
        if not base:isRef() and not base:isPtr() then
            D.bug("ir-place", "Deref needs a reference or a pointer place")
        end
        return place.type
    end
    if kind == "Local" then
        local ty = storages and storages[place.storage.id]
        if not ty then D.bug("ir-place", "Place refers to undeclared storage " .. place.storage.id) end
        return ty
    end
    if kind == "Project" then
        local base = M.place(place.base, storages, locals)
        if base == nil then return nil end
        if not base:isRecord() then D.bug("ir-type", "Project needs a record base") end
        local field = S.field(base, place.field.name)
        if not field then D.bug("ir-field", "Project names an unknown field " .. place.field.name) end
        return field
    end
    if kind == "PtrIndex" then
        -- A pointer is a value, so its type is checked like any expression; there is no length to
        -- compare against, which is exactly what makes this different from a slice index. The
        -- element type is recorded on the node and travels with it, as Deref's pointee does: a
        -- pointer's own target may still name a definition whose layout is not yet sealed, so the
        -- two are checked for shape, not compared by identity.
        local view = S.environmentOf(M.expr(place.view, locals, storages))
        if not view:isPtr() then D.bug("ir-place", "PtrIndex needs a pointer view") end
        if M.expr(place.index, locals, storages) ~= S.U32 then
            D.bug("ir-type", "PtrIndex needs a U32 index")
        end
        return place.type
    end
    if kind == "SliceIndex" then
        -- The view is a value rather than a place, so its type is checked like any expression;
        -- the element type is recorded on the node and the index has to be a U32.
        local view = S.environmentOf(M.expr(place.view, locals, storages))
        if not view:isSlice() then D.bug("ir-place", "SliceIndex needs a slice view") end
        if view.element ~= place.type then
            D.bug("ir-type", "SliceIndex element type does not match the view")
        end
        if M.expr(place.index, locals, storages) ~= S.U32 then
            D.bug("ir-type", "SliceIndex needs a U32 index")
        end
        return place.type
    end
    D.bug("ir-place", "Unknown place variant " .. tostring(kind))
end

function M.arg(arg, locals, storages)
    if arg.kind == "ValueArg" then return M.expr(arg.value, locals, storages) end
    if arg.kind == "BorrowArg" then return M.place(arg.place, storages, locals) end
    D.bug("ir-arg", "Unknown argument variant " .. tostring(arg.kind))
end

function M.program(fnList, modules, foreigns)
    local definitions = {}
    -- A foreign target is declared rather than defined, so it has a result contract and no body, which
    -- is all the call check needs to know about it.
    for _, foreign in ipairs(foreigns or {}) do
        definitions[foreign.target] = { results = foreign.results, inputs = foreign.inputs,
            foreign = true }
    end
    for _, fn in ipairs(fnList) do
        if definitions[fn.id] then D.bug("ir-duplicate", "Duplicate function id " .. fn.id) end
        if fn.role.kind ~= "Body" and fn.role.kind ~= "Entry" then
            D.bug("ir-role", "Unknown function role")
        end
        if fn.hidden > #fn.inputs then D.bug("ir-hidden", "Hidden prefix exceeds the input vector") end
        if #fn.params ~= #fn.inputs then
            D.bug("ir-param", "Function " .. fn.id .. " must declare one parameter per input")
        end
        for index, param in ipairs(fn.params) do
            if param.input ~= index - 1 then
                D.bug("ir-param", "Function " .. fn.id .. " parameters must be ordered by input index")
            end
        end
        definitions[fn.id] = { results = fn.results, inputs = fn.inputs, fn = fn }
    end
    -- Module-level storages are declared outside every function, so the verifier is seeded with
    -- them rather than expecting a Var in the body.
    local seeded = {}
    for _, module in ipairs(modules or {}) do seeded[module.storage.id] = module.type end
    for _, fn in ipairs(fnList) do M.function_(fn, definitions, seeded) end
    return true
end

return M
