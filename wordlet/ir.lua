-- IR construction: per-function expression interning, value/storage allocators and emitters.
-- Effects are occurrences and are never interned; only pure `Ir.Expr` descriptions are.
local S = require("wordlet.schema")
local D = require("wordlet.diag")
local M = {}

local Ir = S.Ir
M.Ir = Ir

-- Structural traversal. These are the schema's own structural questions, so they live on the
-- classes: `Ir.Expr:each(fn)` calls `fn` on the expression operands of a node, `Ir.Place:each`
-- and `Ir.Arg:each` on the expressions a place or an argument names, and `Ir.Stmt:each(fn)` on a
-- statement's child statements. `fn` therefore always receives an `Ir.Expr` from the first three,
-- and an `Ir.Stmt` from the last. Nothing semantic moves here: control completion, effects and
-- purity stay in the passes that own them (`check.lua`'s explicit visitor), because `ASDL.md`
-- says reflection answers structure, not semantics (structure.md §0.3).
--
-- Install order is a correctness condition, not style. A class's metatable propagates the FIRST
-- write of a key to every member of the sum, so a parent default installed after the arms would
-- overwrite all of them. The four defaults therefore come first, and every arm is installed here
-- and nowhere else: no pass module may assign to a class (structure.md §0.2).
function Ir.Expr:each(fn)
    D.bug("ir-expr", "Ir.Expr variant has no :each method: " .. tostring(self.kind))
end
function Ir.Stmt:each(fn)
    D.bug("ir-stmt", "Ir.Stmt variant has no :each method: " .. tostring(self.kind))
end
function Ir.Place:each(fn)
    D.bug("ir-place", "Ir.Place variant has no :each method: " .. tostring(self.kind))
end
function Ir.Arg:each(fn)
    D.bug("ir-arg", "Ir.Arg variant has no :each method: " .. tostring(self.kind))
end

-- The child statements of one statement list, in order.
local function eachStatement(list, fn)
    for _, statement in ipairs(list) do fn(statement) end
end

-- An `Ir.Expr` hands over its operand expressions. A frozen operand (a constant, a value reference,
-- a null) has none, and a place operand contributes the expressions the place itself names.
function Ir.Const:each(fn) end
function Ir.Ref:each(fn) end
function Ir.Null:each(fn) end
function Ir.Un:each(fn) fn(self.operand) end
function Ir.Bin:each(fn)
    fn(self.left)
    fn(self.right)
end
function Ir.Get:each(fn) fn(self.aggregate) end
function Ir.Make:each(fn)
    for _, field in ipairs(self.fields) do fn(field) end
end
function Ir.Convert:each(fn) fn(self.operand) end
function Ir.Addr:each(fn) self.place:each(fn) end
function Ir.SliceLength:each(fn) fn(self.view) end

-- An `Ir.Place` hands over the expressions reaching it: its base is a place rather than an
-- expression, so the base chain is followed and its index or view expressions are the operands.
function Ir.Local:each(fn) end
function Ir.Project:each(fn) self.base:each(fn) end
function Ir.Deref:each(fn) self.base:each(fn) end
function Ir.Index:each(fn)
    self.base:each(fn)
    fn(self.index)
end
function Ir.SliceIndex:each(fn)
    fn(self.view)
    fn(self.index)
end
function Ir.PtrIndex:each(fn)
    fn(self.view)
    fn(self.index)
end

-- An `Ir.Arg` hands over the expressions of the value or place it carries.
function Ir.ValueArg:each(fn) fn(self.value) end
function Ir.BorrowArg:each(fn) self.place:each(fn) end

-- An `Ir.Stmt` hands over the statements nested in it, one level at a time: the arms of an `If`,
-- the body of a `Loop`, and the body of every `Switch` case. A statement with no nested list has
-- no child statements, and the effects it carries are the pass visitor's business, not this one.
function Ir.Let:each(fn) end
function Ir.Var:each(fn) end
function Ir.Read:each(fn) end
function Ir.Store:each(fn) end
function Ir.View:each(fn) end
function Ir.Call:each(fn) end
function Ir.Indirect:each(fn) end
function Ir.If:each(fn)
    eachStatement(self.yes, fn)
    eachStatement(self.no, fn)
end
function Ir.Switch:each(fn)
    for _, case in ipairs(self.cases) do eachStatement(case.body, fn) end
end
function Ir.Loop:each(fn) eachStatement(self.body, fn) end
-- A fieldless variant is a single value, and `Ir.Next` names that value rather than a class, so
-- this arm is installed on the value. Its class keeps the propagated default, which is what a
-- forgotten arm on a future fieldless variant would report.
function Ir.Next:each(fn) end
function Ir.Trap:each(fn) end
function Ir.ConstructVariant:each(fn) end
function Ir.VariantMatches:each(fn) end
function Ir.VariantPayload:each(fn) end
function Ir.Return:each(fn) end

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
function Builder:u32(n) return self:const(S.u32, Ir.UInt(n)) end
function Builder:int(ty, n) return self:const(ty, Ir.UInt(n)) end
function Builder:int64(ty, high, low) return self:const(ty, Ir.UInt64(high, low)) end
function Builder:bool(b) return self:const(S.bool, Ir.Boolean(b)) end
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

-- The null pointer of a ptr type. Pure, and interned by its type, so every null of one type is one
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
