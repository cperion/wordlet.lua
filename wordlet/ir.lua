-- IR construction: per-function expression interning, value/storage allocators and emitters.
-- Effects are occurrences and are never interned; only pure `Ir.Expr` descriptions are.
local S = require("wordlet.schema")
local D = require("wordlet.diag")
local M = {}

local Ir = S.Ir
M.Ir = Ir

-- Exhaustive expression walker. Not a reflective field walk: adding an Ir.Expr variant must
-- extend this function, which is the point.
function M.eachExpr(expr, fn)
    fn(expr)
    local kind = expr.kind
    if kind == "Const" then
        return
    elseif kind == "Ref" then
        return
    elseif kind == "Un" then
        M.eachExpr(expr.operand, fn)
    elseif kind == "Bin" then
        M.eachExpr(expr.left, fn); M.eachExpr(expr.right, fn)
    elseif kind == "Get" then
        M.eachExpr(expr.aggregate, fn)
    elseif kind == "Make" then
        for _, field in ipairs(expr.fields) do M.eachExpr(field, fn) end
    elseif kind == "Null" then
        return
    elseif kind == "SliceLength" then
        M.eachExpr(expr.view, fn)
    elseif kind == "Convert" then
        M.eachExpr(expr.operand, fn)
    elseif kind == "Addr" then
        -- An address is a pure computation over a place, which is a root plus field names; there is
        -- no sub-expression to walk and nothing is read.
        return
    else
        D.bug("ir-expr", "Unknown expression variant: " .. tostring(kind))
    end
end

-- Exhaustive statement walker over one list, in order. Nested lists are visited recursively.
function M.eachStmt(statements, fn)
    for _, stmt in ipairs(statements) do
        fn(stmt)
        local kind = stmt.kind
        if kind == "Let" then
            M.eachExpr(stmt.expr, fn)
        elseif kind == "Read" then
            -- reads a Place, not an expression
        elseif kind == "Var" then
            if stmt.initial then M.eachExpr(stmt.initial, fn) end
        elseif kind == "Store" then
            -- places are not expressions
        elseif kind == "View" then
            -- view slots are Arg values, walked by the caller when needed
        elseif kind == "Call" or kind == "Indirect" then
            for _, arg in ipairs(stmt.arguments) do
                if arg.kind == "ValueArg" then M.eachExpr(arg.value, fn) end
            end
            if stmt.kind == "Indirect" then M.eachExpr(stmt.callable, fn) end
        elseif kind == "If" then
            M.eachExpr(stmt.test, fn)
            M.eachStmt(stmt.yes, fn); M.eachStmt(stmt.no, fn)
        elseif kind == "Switch" then
            for _, case in ipairs(stmt.cases) do M.eachStmt(case.body, fn) end
        elseif kind == "Loop" then
            M.eachStmt(stmt.body, fn)
        elseif kind == "Trap" then
            M.eachExpr(stmt.failure, fn)
        elseif kind == "ConstructVariant" then
            if stmt.payload then M.eachExpr(stmt.payload, fn) end
        elseif kind == "VariantMatches" then
            -- operands are values, not expressions
        elseif kind == "VariantPayload" then
            -- operand is a value, not an expression
        elseif kind == "Return" then
            for _, value in ipairs(stmt.values) do M.eachExpr(value, fn) end
        elseif kind == "Next" then
            -- no operands
        else
            D.bug("ir-stmt", "Unknown statement variant: " .. tostring(kind))
        end
    end
end

-- Builder: one per Ir.Fn under construction.
local Builder = {}
Builder.__index = Builder

function M.builder()
    return setmetatable({ memo = {}, values = 0, storage = 0, expressions = 0 }, Builder)
end

function Builder:valueId()
    self.values = self.values + 1
    return Ir.Value(self.values)
end
function Builder:storageId()
    self.storage = self.storage + 1
    return Ir.Storage(self.storage)
end

-- Interned pure expressions. The key names each operand by its own interned id, never by
-- re-encoding the subtree, so a key costs the same however deep an operand is. Structural equality
-- still wins, because equal operands are the same interned object and therefore the same id.
function Builder:intern(key, make)
    local existing = self.memo[key]
    if existing then return existing end
    local expr = make()
    self.expressions = self.expressions + 1
    expr.id = self.expressions
    self.memo[key] = expr
    return expr
end

function Builder:const(ty, literal)
    return self:intern("const|" .. S.encode(ty) .. "|" .. S.encode(literal), function()
        return Ir.Const(ty, literal)
    end)
end
function Builder:u32(n) return self:const(S.U32, Ir.UInt(n)) end
function Builder:int(ty, n) return self:const(ty, Ir.UInt(n)) end
function Builder:int64(ty, high, low) return self:const(ty, Ir.UInt64(high, low)) end
function Builder:bool(b) return self:const(S.Bool, Ir.Boolean(b)) end
-- A float constant. Its intern key is the value's own exact encoding, so two equal doubles share a
-- node and two unequal ones do not.
function Builder:float(ty, n) return self:const(ty, Ir.Float(n)) end
function Builder:ref(value, ty)
    return self:intern("ref|" .. value.id .. "|" .. S.encode(ty), function()
        return Ir.Ref(value, ty)
    end)
end
function Builder:un(op, operand, ty)
    local constructor = Ir[op]
    if not constructor then D.bug("ir-op", "Unknown unary operation: " .. tostring(op)) end
    return self:intern("un|" .. op .. "|" .. operand.id .. "|" .. S.encode(ty), function()
        return Ir.Un(constructor, operand, ty)
    end)
end

-- A binary operation. The evaluator is the one authority on per-width arithmetic, so a constant
-- operation is left to it rather than re-folded here.
function Builder:bin(op, left, right, ty)
    local constructor = Ir[op]
    if not constructor then D.bug("ir-op", "Unknown binary operation: " .. tostring(op)) end
    return self:intern("bin|" .. op .. "|" .. left.id .. "|" .. right.id .. "|" .. S.encode(ty),
        function() return Ir.Bin(constructor, left, right, ty) end)
end

function Builder:get(aggregate, name, ty)
    -- Get of a Make is the made component.
    if aggregate.kind == "Make" then
        for index, field in ipairs(aggregate.fields) do
            if aggregate.type.fields[index].name == name then return field end
        end
    end
    return self:intern("get|" .. aggregate.id .. "|" .. name .. "|" .. S.encode(ty), function()
        return Ir.Get(aggregate, Ir.Field(name), ty)
    end)
end

-- A `Make` is pure, so it is interned like any other expression and carries an id for its users.
function Builder:make(ty, fields)
    local key = { "make", S.encode(ty) }
    for index, field in ipairs(fields) do key[#key + 1] = field.id end
    return self:intern(table.concat(key, "|"), function() return Ir.Make(ty, S.list(fields)) end)
end
-- An integer conversion, interned like every other pure expression.
function Builder:convert(operand, ty)
    if operand.type == ty then return operand end
    return self:intern("convert|" .. operand.id .. "|" .. S.encode(ty), function()
        return Ir.Convert(operand, ty)
    end)
end
function Builder:addr(place, ty)
    return self:intern("addr|" .. S.encode(place) .. "|" .. S.encode(ty), function()
        return Ir.Addr(place, ty)
    end)
end
-- The length of a slice value. Pure, like a record field projection, so it is interned and keyed
-- by the view's own id rather than by re-encoding it.
function Builder:sliceLength(view, ty)
    return self:intern("slicelen|" .. view.id .. "|" .. S.encode(ty), function()
        return Ir.SliceLength(view, ty)
    end)
end

-- The null pointer of a Ptr type. Pure, and interned by its type, so every null of one type is one
-- node, and two nulls of that type are the same object.
function Builder:nullPtr(ty)
    return self:intern("null|" .. S.encode(ty), function() return Ir.Null(ty) end)
end

-- An element place of a pointer. A pointer carries no length, so unlike a slice index this one has
-- no bounds check to emit; it is a place because the element can be written through it.
function Builder:ptrIndex(view, index, ty)
    return Ir.PtrIndex(view, index, ty)
end

function Builder:sliceIndex(view, index, ty)
    return Ir.SliceIndex(view, index, ty)
end

-- Statement emitters append to a list and return any result values.
function Builder:emit(list, stmt)
    list[#list + 1] = stmt
    return stmt
end
-- A trap whose condition an identical adjacent trap already checked is redundant. The condition is
-- a pure expression over immutable SSA values, so the two checks agree; `/` and `%` by one run-time
-- divisor are the common case.
function Builder:trap(list, failure, tag)
    local last = list[#list]
    if last and last.kind == "Trap" and last.failure == failure then return last end
    return self:emit(list, Ir.Trap(failure, tag))
end
function Builder:let(list, ty, expr)
    local value = self:valueId()
    self:emit(list, Ir.Let(value, ty, expr))
    return value, expr
end
function Builder:var(list, ty, initial)
    local storage = self:storageId()
    self:emit(list, Ir.Var(storage, ty, initial))
    return storage
end
function Builder:read(list, ty, place)
    local value = self:valueId()
    self:emit(list, Ir.Read(value, ty, place))
    return value
end
function Builder:store(list, place, value)
    self:emit(list, Ir.Store(place, value))
end
function Builder:return_(list, values)
    self:emit(list, Ir.Return(S.list(values)))
end

return M
