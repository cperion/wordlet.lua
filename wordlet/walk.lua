-- Schema-driven traversal over the ASDL nodes.
--
-- Structure comes from the generated classes' `__fields` -- the same reflection
-- wordlet/ast.lua's `render` uses -- so a field added to ast.asdl or ir.asdl is
-- traversed without a second table to update. This module answers only the
-- structural questions: what are the node-valued children of a node, and what
-- are the variants of a sum. Every semantic question (binders, scopes, effects,
-- tail position, definite assignment) stays in an explicit visitor, exactly as
-- ASDL.md directs. It depends on nothing, so any pass can use it.
local M = {}

-- ASDL builtin field types are leaves; every other field type names a class. The `span` attribute
-- carries diagnostics rather than structure, so it is not a child.
local SCALARS = { string = true, number = true, boolean = true, any = true }

-- The node-valued fields of `node`, in declaration order. `list` marks a `T*`
-- field, whose value is an A.List. A scalar field is never a child, and a field
-- whose value is nil is skipped.
function M.children(node)
    local class = getmetatable(node)
    local fields = class and class.__fields
    if not fields then return {} end
    local out = {}
    for _, field in ipairs(fields) do
        if not SCALARS[field.type] and field.name ~= "span" then
            local value = node[field.name]
            if value ~= nil then
                out[#out + 1] = { name = field.name, field = field, value = value, list = field.list or false }
            end
        end
    end
    return out
end

-- The node children as one flat list, expanding `T*` fields. A caller that does
-- not care which field a child came from uses this.
function M.nodeChildren(node)
    local out = {}
    for _, child in ipairs(M.children(node)) do
        if child.list then
            for _, item in ipairs(child.value) do out[#out + 1] = item end
        else
            out[#out + 1] = child.value
        end
    end
    return out
end

-- Pre-order traversal. `visitor.enter(node)` may return false to prune the
-- subtree; `visitor.leave(node)` runs after the children.
function M.walk(node, visitor)
    if node == nil then return end
    if visitor.enter and visitor.enter(node) == false then return end
    for _, child in ipairs(M.children(node)) do
        if child.list then
            for _, item in ipairs(child.value) do M.walk(item, visitor) end
        else
            M.walk(child.value, visitor)
        end
    end
    if visitor.leave then visitor.leave(node) end
end

-- The sums a context defines, each with its variant class names. A sum has members and no fields of
-- its own; a product has fields. A fieldless variant (Ir.Add) also has no fields, but its members
-- name only itself, while a sum names itself and at least one variant. This is the schema as data,
-- which is what lets a completeness check enumerate every variant without a hand-kept list.
function M.sums(ctx)
    local qualified = {}
    for name, class in pairs(ctx.definitions) do qualified[class] = name end
    local out = {}
    for name, class in pairs(ctx.definitions) do
        if class.__fields == nil and type(class.members) == "table" then
            local variants = {}
            for member in pairs(class.members) do
                if member ~= class and qualified[member] then variants[#variants + 1] = qualified[member] end
            end
            if #variants > 0 then
                table.sort(variants)
                out[#out + 1] = { name = name, variants = variants }
            end
        end
    end
    table.sort(out, function(a, b) return a.name < b.name end)
    return out
end

return M
