-- Wordlet diagnostics. Kinds and statuses are fixed by interfaces.md §7.
local M = {}
local KINDS = { reject = 1, bug = 2, todo = 3, resource = 4, internal = 2 }

local Diagnostic = {}
Diagnostic.__index = Diagnostic
function Diagnostic:__tostring() return M.format(self) end

local function make(kind, code, message, span)
    return setmetatable({ kind = kind, status = KINDS[kind], code = code, message = message, span = span }, Diagnostic)
end

-- Construct a diagnostic value without raising it.
function M.make(kind, code, message, span)
    assert(KINDS[kind], "unknown diagnostic kind: " .. tostring(kind))
    return setmetatable({ kind = kind, status = KINDS[kind], code = code, message = message, span = span }, Diagnostic)
end

-- Raise a diagnostic. These are the normal call sites; `make` is for constructing one to return or compare.
function M.reject(code, message, span) error(M.make("reject", code, message, span), 0) end
function M.bug(code, message, span) error(M.make("bug", code, message, span), 0) end
function M.todo(code, message, span) error(M.make("todo", code, message, span), 0) end
function M.resource(code, message, span) error(M.make("resource", code, message, span), 0) end
function M.internal(code, message, span) error(M.make("internal", code, message, span), 0) end

function M.is(value)
    return type(value) == "table" and getmetatable(value) == Diagnostic
end

function M.at(err, span)
    if M.is(err) and span and not err.span then err.span = span end
    return err
end

function M.format(err)
    if not M.is(err) then return tostring(err) end
    local where = ""
    if err.span then
        where = string.format(" at %s:%d", err.span.file or "?", err.span.line or 0)
    end
    return string.format("%s [%s]%s %s", err.kind:upper(), err.code, where, err.message)
end

M.status = function(err) return M.is(err) and err.status or KINDS.internal end

return M
