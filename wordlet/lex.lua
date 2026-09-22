-- Free-form lexer. Newlines and indentation are whitespace; only `--` comments are line-sensitive.
local D = require("wordlet.diag")
local U64 = require("wordletkit.u64")
local M = {}

local KEYWORDS = {}
for word in ("let do end if then else return and or not true false"):gmatch("%S+") do
    KEYWORDS[word] = true
end

-- Longest-token-first. `|` is always a single token, so `||` is simply two pipes.
local OPERATORS = {
    "<<=", ">>=",
    "::", "->", "!=", "==", "<=", ">=", "<<", ">>",
    "+=", "-=", "*=", "/=", "%=", "^=", "&=", "|=", "~=",
    "(", ")", "{", "}", "[", "]", ",", ";", ":", ".", "|", "^", "&", "~",
    "+", "-", "*", "/", "%", "<", ">", "=",
}
table.sort(OPERATORS, function(a, b)
    if #a ~= #b then return #a > #b end
    return a < b
end)

local name_start = "[%a_]"
local name_char = "[%w_]"

local function span(file, line, start, finish) return { file = file, line = line, start = start, finish = finish } end

-- Returns a dense list of tokens: { kind = "name"|"keyword"|"number"|"op"|"eof", text, value, span }.
function M.tokens(source, name)
    name = name or "<source>"
    if type(source) ~= "string" then D.reject("lex-input", "Source must be a string") end
    local tokens, n, i = {}, #source, 1
    local line, line_start = 1, 1
    while i <= n do
        local c = source:sub(i, i)
        if c == "\n" then
            line, line_start = line + 1, i + 1
            i = i + 1
        elseif c == " " or c == "\t" or c == "\r" or c == "\v" or c == "\f" then
            i = i + 1
        elseif source:sub(i, i + 1) == "--" then
            -- Leave the newline to be consumed by the main loop so line counting stays correct.
            local nl = source:find("\n", i + 2, true)
            i = nl or (n + 1)
        elseif c:match(name_start) then
            local start = i
            while i <= n and source:sub(i, i):match(name_char) do i = i + 1 end
            local text = source:sub(start, i - 1)
            tokens[#tokens + 1] = { kind = KEYWORDS[text] and "keyword" or "name", text = text,
                span = span(name, line, start, i) }
        elseif c:match("%d") then
            local start = i
            local value
            if source:sub(i, i + 1):lower() == "0x" then
                i = i + 2
                local digits = i
                while i <= n and source:sub(i, i):match("%x") do i = i + 1 end
                if i == digits then D.reject("lex-number", "Hexadecimal literal has no digits", span(name, line, start, i)) end
            else
                while i <= n and source:sub(i, i):match("%d") do i = i + 1 end
            end
            -- A literal that does not fit a word arrives as its two words, and one that needs more
            -- than 64 bits is refused rather than wrapped.
            local text = source:sub(start, i - 1)
            value = tonumber(text)
            if value == nil or value > 4294967295 then
                local high, low = U64.fromstring(text)
                if not high then
                    D.reject("lex-range", "Integer literal exceeds 64 bits", span(name, line, start, i))
                end
                value = { high = high, low = low }
            end
            tokens[#tokens + 1] = { kind = "number", text = source:sub(start, i - 1), value = value,
                span = span(name, line, start, i) }
        else
            local matched
            for _, op in ipairs(OPERATORS) do
                if source:sub(i, i + #op - 1) == op then matched = op; break end
            end
            if not matched then
                D.reject("lex-char", string.format("Unexpected character %q", c), span(name, line, i, i + 1))
            end
            tokens[#tokens + 1] = { kind = "op", text = matched, span = span(name, line, i, i + #matched) }
            i = i + #matched
        end
    end
    tokens[#tokens + 1] = { kind = "eof", text = "<eof>", span = span(name, line, n, n) }
    return tokens
end

return M
