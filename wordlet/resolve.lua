-- Lexical facts that are purely syntactic, so they are computed once from the AST rather than
-- during evaluation: which names a lambda body captures, and where a definition calls itself in
-- tail position.
--
-- The architecture's module table gives `resolve.lua` bindings as well. This implementation
-- resolves bindings during evaluation instead, because a name can denote a word, a value, a schema
-- or a field depending on values that only exist at evaluation time; a separate static pass would
-- have to duplicate that. The syntactic part lives here.
local M = {}

-- Free names of a lambda body: referenced but not bound by its parameters or its own `let`s.
-- Nested lambdas and method bodies are separate functions and are not entered.
local function freeNames(node, bound, out)
    if node == nil then return end
    local kind = node.kind
    if kind == "Reference" then
        local name = node.name.text
        if not bound[name] then out[name] = true end
        return
    elseif kind == "Lambda" or kind == "SchemaExpr" then
        return
    elseif kind == "Block" then
        local inner = {}
        for key in pairs(bound) do inner[key] = true end
        for _, stmt in ipairs(node.statements) do freeNames(stmt, inner, out) end
        return
    elseif kind == "ValueStmt" then
        -- The value expressions see the bindings declared so far; the binders are added after.
        for _, value in ipairs(node.def.values) do freeNames(value, bound, out) end
        for _, binder in ipairs(node.def.binders) do bound[binder.name.text] = true end
        return
    elseif kind == "WordStmt" then
        bound[node.def.name.text] = true
        return
    elseif kind == "IfStmt" then
        freeNames(node.test, bound, out)
        for _, arm in ipairs({ node.yes, node.no }) do
            for _, stmt in ipairs(arm) do freeNames(stmt, bound, out) end
        end
        return
    elseif kind == "StoreStmt" then
        freeNames(node.target, bound, out); freeNames(node.value, bound, out)
        return
    elseif kind == "ReturnStmt" then
        for _, value in ipairs(node.values) do freeNames(value, bound, out) end
        return
    elseif kind == "Expression" then
        return freeNames(node.value, bound, out)
    end
    -- Remaining expression forms: walk their child expressions.
    local children = {
        Apply = { "callee", "arguments" }, BinaryExpr = { "left", "right" },
        UnaryExpr = { "operand" }, Condition = { "test", "yes", "no" },
        FieldSelect = { "base" }, RecordSupply = { "schema", "fields" },
        SignatureExpr = { "inputs" }, ResultSpec = nil,
    }
    local fields = children[kind]
    if not fields then return end
    for _, field in ipairs(fields) do
        local child = node[field]
        if type(child) == "table" and child.kind == nil and #child > 0 then
            for _, item in ipairs(child) do freeNames(item, bound, out) end
        elseif type(child) == "table" and (child.kind or child.value or child.name) then
            freeNames(child, bound, out)
        end
    end
end

-- Syntactic test for a tail self-call. In this language `return` is explicit, so every ReturnStmt
-- value is a tail position, and an expression body's root is one too. Nested words are separate
-- functions and are not entered. A false positive only costs the loop-capable parameter layout.
local function tailValue(node, name)
    if node == nil then return false end
    local kind = node.kind
    if kind == "Apply" then
        return node.callee.kind == "Reference" and node.callee.name.text == name
    elseif kind == "Condition" then
        return tailValue(node.yes, name) or tailValue(node.no, name)
    end
    return false
end

local function hasTailCall(node, name)
    if node == nil then return false end
    local kind = node.kind
    if kind == "ReturnStmt" then
        for _, value in ipairs(node.values) do if tailValue(value, name) then return true end end
        return false
    elseif kind == "Expression" then
        return tailValue(node.value, name)
    elseif kind == "Block" then
        for _, stmt in ipairs(node.statements) do if hasTailCall(stmt, name) then return true end end
        return false
    elseif kind == "IfStmt" then
        for _, arm in ipairs({ node.yes, node.no }) do
            for _, stmt in ipairs(arm) do if hasTailCall(stmt, name) then return true end end
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
function M.tailCalls(body, name)
    return hasTailCall(body, name)
end

return M
