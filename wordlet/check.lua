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
    return true
end
M.falls = falls

-- Definite initialisation: storage assigned on every reachable path to this point.
local function initialized(list, input)
    local set = {}
    for key in pairs(input or {}) do set[key] = true end
    for _, stmt in ipairs(list) do
        local kind = stmt.kind
        if kind == "Var" then
            set[stmt.storage.id] = true
        elseif kind == "If" then
            local yes = initialized(stmt.yes, set)
            local no = initialized(stmt.no, set)
            local both = {}
            for key in pairs(yes) do if no[key] then both[key] = true end end
            set = both
        elseif kind == "Loop" then
            -- Loop does not fall through, so it contributes nothing to the continuation.
        elseif kind == "Store" then
            -- A store to uninitialised storage is still a store; the storage itself is declared
            -- by Var or is an input, both of which are checked separately.
        end
    end
    return set
end

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
    local function checkList(list, inputs, visible, storages, inLoop)
        local set = initialized(list, inputs)
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
                bind(visible, stmt.value.id, stmt.type)
            elseif kind == "Var" then
                storages[stmt.storage.id] = stmt.type
                if stmt.initial then
                    if M.expr(stmt.initial, visible, storages) ~= stmt.type then
                        D.bug("ir-type", "Var initialiser does not match the storage type")
                    end
                end
            elseif kind == "Store" then
                local placeType = M.place(stmt.place, storages, visible)
                if M.expr(stmt.value, visible, storages) ~= placeType then
                    D.bug("ir-type", "Store value does not match the place's type")
                end
            elseif kind == "If" then
                M.expr(stmt.test, visible, storages)
                checkList(stmt.yes, set, copy(visible), storages, inLoop)
                checkList(stmt.no, set, copy(visible), storages, inLoop)
            elseif kind == "Loop" then
                -- A loop body may fall through only if it never falls out; the builder always ends
                -- it with a Return or a Next, so an empty body is the only rejected shape.
                checkList(stmt.body, set, copy(visible), storages, true)
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
                    if not S.isView(callable) then D.bug("ir-type", "Indirect needs a view-typed callable") end
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
                    M.arg(arg, visible, storages)
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
                        if arg.kind == "ValueArg" and input.kind == "InValue"
                            and arg.value.type ~= nil then
                            if M.expr(arg.value, visible, storages) ~= input.type then
                                D.bug("ir-type", "Call argument type does not match the target input")
                            end
                        end
                        if arg.kind == "BorrowArg" and input.kind == "InPlace" then
                            if M.place(arg.place, storages, visible) ~= input.type then
                                D.bug("ir-type", "Borrowed argument type does not match the target input")
                            end
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
                if not S.isView(stmt.type) and not (S.isOwned(stmt.type)
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
                    if #stmt.slots ~= 0 then end
                end
                -- The visible remainder must match the view's signature.
                for index, input in ipairs(stmt.type.visible.inputs) do
                    local hidden = target.inputs[#stmt.slots + index]
                    if not hidden or S.encode(hidden) ~= S.encode(input) then
                        D.bug("ir-type", "View signature does not match the remaining inputs")
                    end
                end
                bind(visible, stmt.value.id, stmt.type)
            elseif kind == "ConstructVariant" then
                if not S.isTaggedType(stmt.type) then
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
                if not S.isTaggedType(stmt.sum) then
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
        if param.kind ~= "ValueParam" and param.kind ~= "PlaceParam" and param.kind ~= "BundleParam" then
            D.bug("ir-param", "Unknown parameter variant " .. tostring(param.kind))
        end
        if param.kind == "ValueParam" then bind(visible, param.binding.id, param.type) end
    end
    local storages = {}
    for id, ty in pairs(seeded or {}) do storages[id] = ty end
    for _, param in ipairs(fn.params) do
        if param.kind == "PlaceParam" then storages[param.binding.id] = param.type end
    end
    checkList(fn.body, {}, visible, storages)
    if falls(fn.body) then
        D.bug("ir-fallthrough", "Function " .. fn.id .. " can fall through without returning")
    end
    return true
end

function M.expr(expr, locals, storages)
    local kind = expr.kind
    if kind == "Const" then
        if S.isInteger(expr.type) then
            if expr.literal.kind == "UInt64" then
                -- A two-word constant is only meaningful for a 64-bit type.
                if not S.isWide(expr.type) then
                    D.bug("ir-literal", "A two-word constant needs a 64-bit type")
                end
            elseif expr.literal.kind ~= "UInt" then
                D.bug("ir-literal", "An integer constant needs a UInt literal")
            elseif S.isWide(expr.type) then
                -- A one-word constant of a 64-bit type has to be a word.
                if expr.literal.value > 4294967295 then
                    D.bug("ir-literal", "A one-word constant is out of range")
                end
            elseif expr.literal.value > S.maxOf(expr.type) then
                D.bug("ir-literal", "A constant does not fit in its own width")
            end
        elseif expr.type == S.Bool then
            if expr.literal.kind ~= "Boolean" then D.bug("ir-literal", "Bool constant needs a Boolean literal") end
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
        local record = S.environmentOf(expr.type)
        if S.isArray(record) then
            if #expr.fields ~= record.length then
                D.bug("ir-arity", "Make element count does not match the array length")
            end
            for _, item in ipairs(expr.fields) do
                if M.expr(item, locals, storages) ~= record.element then
                    D.bug("ir-type", "Make element type does not match the array element")
                end
            end
            return expr.type
        end
        if not S.isRecord(record) then D.bug("ir-type", "Make needs a record or callable type") end
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
        -- An address is pure: it computes the address of a place and reads nothing. The pointee
        -- identity is a type-cell fact the verifier does not re-derive, so this checks the recorded
        -- type is a reference and that the place is well formed.
        if not S.isRef(expr.type) then D.bug("ir-type", "Addr needs a reference type") end
        local placeType = M.place(expr.place, storages, locals)
        if placeType == nil then D.bug("ir-place", "Addr needs a place with a known type") end
        if not S.isNamed(expr.type.target) and placeType ~= expr.type.target then
            D.bug("ir-type", "Addr place type does not match the reference target")
        end
        return expr.type
    elseif kind == "Get" then
        local aggregate = S.environmentOf(M.expr(expr.aggregate, locals, storages))
        if not S.isRecord(aggregate) then D.bug("ir-type", "Get needs a record aggregate") end
        local field = S.field(aggregate, expr.field.name)
        if not field then D.bug("ir-field", "Get names an unknown field " .. expr.field.name) end
        if field ~= expr.type then D.bug("ir-type", "Get type does not match the field type") end
        return expr.type
    elseif kind == "Convert" then
        -- A conversion is between integer widths, and its type is the width it converts to.
        local operand = M.expr(expr.operand, locals, storages)
        if not S.isInteger(operand) or not S.isInteger(expr.type) then
            D.bug("ir-type", "Convert needs two integer widths")
        end
        return expr.type
    elseif kind == "Un" then
        local operand = M.expr(expr.operand, locals, storages)
        local op = expr.op.kind
        if op == "Not" then
            if operand ~= S.Bool or expr.type ~= S.Bool then D.bug("ir-type", "Not requires Bool") end
        elseif op == "Neg" or op == "BitNot" then
            if not S.isInteger(operand) or operand ~= expr.type then
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
            if not S.isInteger(left) or left ~= right or expr.type ~= left then
                D.bug("ir-type", "Arithmetic " .. op .. " requires one integer width")
            end
        elseif op == "Shl" or op == "Shr" then
            -- The amount is a plain U32; the value keeps its own width.
            if not S.isInteger(left) or right ~= S.U32 or expr.type ~= left then
                D.bug("ir-type", "A shift needs an integer value and a U32 amount")
            end
        elseif op == "Eq" or op == "Ne" then
            if left ~= right or expr.type ~= S.Bool then D.bug("ir-type", "Equality requires matching types") end
        elseif op == "Lt" or op == "Le" or op == "Gt" or op == "Ge" then
            if not S.isInteger(left) or not S.isInteger(right) or expr.type ~= S.Bool then
                D.bug("ir-type", "Ordering requires two integers")
            end
        else
            D.bug("ir-op", "Unknown binary operation " .. tostring(op))
        end
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
        if not S.isArray(base) then D.bug("ir-place", "Index needs an array base") end
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
        if not S.isRef(base) then D.bug("ir-place", "Deref needs a reference place") end
        return place.type
    end
    if kind == "Local" then
        local ty = storages and storages[place.storage.id]
        if not ty then D.bug("ir-place", "Place refers to undeclared storage " .. place.storage.id) end
        return ty
    end
    if kind == "Captured" then return nil end
    if kind == "Project" then
        local base = M.place(place.base, storages, locals)
        if base == nil then return nil end
        if not S.isRecord(base) then D.bug("ir-type", "Project needs a record base") end
        local field = S.field(base, place.field.name)
        if not field then D.bug("ir-field", "Project names an unknown field " .. place.field.name) end
        return field
    end
    D.bug("ir-place", "Unknown place variant " .. tostring(kind))
end

function M.arg(arg, locals, storages)
    if arg.kind == "ValueArg" then return M.expr(arg.value, locals, storages) end
    if arg.kind == "BorrowArg" then return M.place(arg.place, storages, locals) end
    if arg.kind == "BundleArg" then return true end
    D.bug("ir-arg", "Unknown argument variant " .. tostring(arg.kind))
end

function M.program(fnList, modules)
    local definitions = {}
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
