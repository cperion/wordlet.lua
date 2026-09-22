-- AST schema context and reflection helpers. ast.asdl is the source of truth; schema/ast.lua is generated.
local ASDL = require("vendor.asdl")
local M = {}

M.ASDL = ASDL
M.List = ASDL.List
M.ctx = ASDL.NewContext()
M.ctx:Define(require("wordlet.schema.ast"))
M.c = M.ctx.Ast

local source = debug.getinfo(1, "S").source:sub(2)
M.root = (source:match("^(.*[/\\])") or "./") .. "../"

function M.span(tokens, first, last)
    return M.c.Span(first.span.file, first.span.line, first.span.start, (last or first).span.finish)
end

function M.name(token)
    return M.c.Name(token.text, M.c.Span(token.span.file, token.span.line, token.span.start, token.span.finish))
end

-- Structural dump used by tests and diagnostics. Reflection enumerates fields; it is not a
-- semantic visitor, so it is only for readable output. `shape` omits spans so that two parses of
-- the same program can be compared regardless of where they appear in a file.
local function render(value, out, indent, withSpans)
    local pad = string.rep("  ", indent)
    if type(value) ~= "table" or getmetatable(value) == nil then
        out[#out + 1] = tostring(value)
        return
    end
    local mt = getmetatable(value)
    if mt == M.List then
        out[#out + 1] = "["
        for index, item in ipairs(value) do
            if index > 1 then out[#out + 1] = "," end
            render(item, out, indent + 1, withSpans)
        end
        out[#out + 1] = "]"
        return
    end
    local kind = value.kind
    local fields = mt.__fields
    if not fields then
        out[#out + 1] = tostring(value)
        return
    end
    out[#out + 1] = kind and (kind .. "(") or "("
    local first = true
    for _, field in ipairs(fields) do
        local item = value[field.name]
        if item ~= nil and not (field.name == "span" and not withSpans) then
            if not first then out[#out + 1] = ", " end
            first = false
            out[#out + 1] = field.name .. "="
            render(item, out, indent, withSpans)
        end
    end
    out[#out + 1] = ")"
end

function M.dump(value)
    local out = {}
    render(value, out, 0, true)
    return table.concat(out)
end

function M.shape(value)
    local out = {}
    render(value, out, 0, false)
    return table.concat(out)
end

return M
