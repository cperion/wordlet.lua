-- Lexical facts that are purely syntactic, so they are computed once from the AST rather than
-- during evaluation: which names a lambda body captures, and where a definition calls itself in
-- tail position.
--
-- The architecture's module table gives `resolve.lua` bindings as well. This implementation
-- resolves bindings during evaluation instead, because a name can denote a word, a value, a schema
-- or a field depending on values that only exist at evaluation time; a separate static pass would
-- have to duplicate that. The syntactic part lives here.
local Walk = require("wordlet.walk")

local M = {}

-- A set copy, so a nested scope can add bindings without leaking them to its siblings.
local function copy(bound)
    local out = {}
    for key in pairs(bound) do out[key] = true end
    return out
end

-- Free names of a lambda body: referenced but not bound by its parameters or its own `let`s.
-- Structure comes from wordlet.walk, so every expression position -- a record field, an array
-- element, an index -- is covered by construction. Only the scoping cases are written out,
-- because which names bind where is the part structure cannot express.
local function freeNames(node, bound, out)
    if node == nil then return end
    local kind = node.kind
    if kind == "Reference" then
        local name = node.name.text
        if not bound[name] then out[name] = true end
        return
    elseif kind == "Lambda" then
        -- A nested lambda is a separate function, but the names it needs travel through this one:
        -- an environment cannot hold a name its enclosing environment does not have. Its parameter
        -- annotations are read here; its parameters bind in its body.
        for _, param in ipairs(node.params) do
            if param.annotation then freeNames(param.annotation, bound, out) end
        end
        local inner = copy(bound)
        for _, param in ipairs(node.params) do inner[param.name.text] = true end
        return freeNames(node.body, inner, out)
    elseif kind == "SchemaExpr" then
        -- A method body belongs to the schema it is written in, not to the enclosing lambda.
        return
    elseif kind == "Block" then
        local inner = copy(bound)
        for _, stmt in ipairs(node.statements) do freeNames(stmt, inner, out) end
        return
    elseif kind == "ValueStmt" then
        -- Annotations and values see the bindings declared so far; the binders join afterwards.
        for _, binder in ipairs(node.def.binders) do
            if binder.annotation then freeNames(binder.annotation, bound, out) end
        end
        for _, value in ipairs(node.def.values) do freeNames(value, bound, out) end
        for _, binder in ipairs(node.def.binders) do bound[binder.name.text] = true end
        return
    elseif kind == "WordStmt" then
        -- A local named word is called inside its own activation, so it sees that scope directly
        -- and needs no capture; only its name binds, from here on.
        bound[node.def.name.text] = true
        return
    elseif kind == "IfStmt" then
        freeNames(node.test, bound, out)
        -- Each arm is its own scope, so a declaration in one does not bind the other.
        for _, arm in ipairs({ node.yes, node.no }) do
            local inner = copy(bound)
            for _, stmt in ipairs(arm) do freeNames(stmt, inner, out) end
        end
        return
    end
    -- Every other form is walked structurally, so a new expression position is covered without a
    -- table here to keep in step with the schema.
    for _, child in ipairs(Walk.children(node)) do
        if child.list then
            for _, item in ipairs(child.value) do freeNames(item, bound, out) end
        else
            freeNames(child.value, bound, out)
        end
    end
end

-- Syntactic test for a tail self-call. In this language `return` is explicit, so every ReturnStmt
-- value is a tail position, and an expression body's root is one too. Nested words are separate
-- functions and are not entered. A false positive only costs the loop-capable parameter layout.
local function tailValue(node, name, keyed)
    if node == nil then return false end
    local kind = node.kind
    if kind == "Apply" then
        return node.callee.kind == "Reference" and node.callee.name.text == name
    elseif kind == "RecordSupply" then
        -- A keyed self-call that supplies every key is the same back edge as `f(...)`. A partial
        -- supply only returns a specialized word, so it is not a call and not a tail position.
        if keyed == nil or node.schema.kind ~= "Reference" or node.schema.name.text ~= name then
            return false
        end
        local supplied, fields = {}, 0
        for _, field in ipairs(node.fields) do
            if not supplied[field.name.text] then supplied[field.name.text] = true; fields = fields + 1 end
        end
        local wanted = 0
        for key in pairs(keyed) do
            if not supplied[key] then return false end
            wanted = wanted + 1
        end
        return fields == wanted
    elseif kind == "Condition" then
        return tailValue(node.yes, name, keyed) or tailValue(node.no, name, keyed)
    end
    return false
end

local function hasTailCall(node, name, keyed)
    if node == nil then return false end
    local kind = node.kind
    if kind == "ReturnStmt" then
        for _, value in ipairs(node.values) do if tailValue(value, name, keyed) then return true end end
        return false
    elseif kind == "Expression" then
        return tailValue(node.value, name, keyed)
    elseif kind == "Block" then
        for _, stmt in ipairs(node.statements) do if hasTailCall(stmt, name, keyed) then return true end end
        return false
    elseif kind == "IfStmt" then
        for _, arm in ipairs({ node.yes, node.no }) do
            for _, stmt in ipairs(arm) do if hasTailCall(stmt, name, keyed) then return true end end
        end
        return false
    end
    return false   -- Lambda, SchemaExpr, ValueStmt, WordStmt, CallStmt, StoreStmt
end

-- `label` names anonymous words (lambdas); named definitions use their own name.
-- The names a lambda body refers to but does not bind, in a stable order.
function M.captures(node)
    local bound, out = {}, {}
    for _, param in ipairs(node.params) do bound[param.name.text] = true end
    freeNames(node.body, bound, out)
    local order = {}
    for name in pairs(out) do order[#order + 1] = name end
    table.sort(order)
    return order
end

-- Whether a definition body calls `name` in tail position, which is what a self-tail loop needs.
-- `keyed` is the word's own keyed requirement set, or nil for an ordered word.
function M.tailCalls(body, name, keyed)
    return hasTailCall(body, name, keyed)
end

return M
