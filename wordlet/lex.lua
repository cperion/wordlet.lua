-- Free-form lexer. Newlines and indentation are whitespace; only `--` comments are line-sensitive.
local D = require("wordlet.diag")
local U64 = require("wordletkit.u64")
local M = {}

local KEYWORDS = {}
for word in ("let extern do defer end if then else return and or not true false"):gmatch("%S+") do
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

-- Long brackets -----------------------------------------------------------------------------------
-- A long bracket is `[`, some `=`s and `[`, and the same number of `=`s closes it, so a body may
-- contain the closing form of every lower level. There are no escapes: the bytes between the brackets
-- are the bytes of the value. One newline immediately after the opening bracket is dropped, so a body
-- can begin on the line below it.
--
-- A string needs at least one `=`: `[[` is already an array whose first element is an array, and an
-- array literal is ordinary enough that it must not become ambiguous. A comment allows none, so
-- `--[[ ... ]]` spells a block comment; a comment can never be a value, so `[[` has no other reading
-- there, and a line comment that merely begins with a bracket keeps a space after the `--`.
local CLOSES = {}
local function closeOf(level)
    local text = CLOSES[level]
    if not text then
        text = "]" .. string.rep("=", level) .. "]"
        CLOSES[level] = text
    end
    return text
end

-- `at` is the opening `[`. Returns the level and the position after it, or nil when this `[` is the
-- array bracket instead.
local function longOpen(source, n, at, allowZero)
    -- `at` is where the `[` would be. Requiring it is what keeps `-- [[1,2]]` a line comment: the
    -- opening bracket has to follow the `--` immediately, with no space between them.
    if source:sub(at, at) ~= "[" then return nil end
    local level, cursor = 0, at + 1
    while cursor <= n and source:sub(cursor, cursor) == "=" do
        level, cursor = level + 1, cursor + 1
    end
    if source:sub(cursor, cursor) ~= "[" then return nil end
    if level == 0 and not allowZero then return nil end
    return level, cursor + 1
end

-- The body and the position after the closing form, or nil when the bracket is never closed.
local function longBody(source, cursor, level)
    local close = closeOf(level)
    local finish = source:find(close, cursor, true)
    if not finish then return nil end
    local body = source:sub(cursor, finish - 1)
    if body:sub(1, 1) == "\n" then body = body:sub(2) end
    return body, finish + #close
end

local function newlinesIn(text) return select(2, text:gsub("\n", "")) end

-- Quoted literals ---------------------------------------------------------------------------------
-- `"..."` is a string: a byte sequence whose bytes are the bytes of the source, so a multi-byte
-- character needs no escape and no decoding. `'x'` is one byte written readably, which is what a
-- byte-oriented program compares an element against. They share one set of escapes, and neither may
-- contain a raw newline, so a forgotten quote is reported on the line that forgot it.
local ESCAPES = { n = "\n", r = "\r", t = "\t", ["0"] = "\0", ["\\"] = "\\", ["\""] = "\"", ["'"] = "'" }

local function escapeAt(source, i, name, line)
    local escape = source:sub(i + 1, i + 1)
    local simple = ESCAPES[escape]
    if simple then return simple, i + 2 end
    if escape == "x" then
        local digits = source:sub(i + 2, i + 3)
        if not digits:match("^%x%x$") then
            D.reject("lex-string", "\\x needs two hexadecimal digits", span(name, line, i, i + 4))
        end
        return string.char(tonumber(digits, 16)), i + 4
    end
    D.reject("lex-string", "Unknown escape \\" .. escape, span(name, line, i, i + 2))
end

-- Returns the decoded body, the position after the closing quote, and whether it was closed.
local function quoted(source, n, i, quote, name, line)
    local bytes = {}
    i = i + 1
    while i <= n do
        local ch = source:sub(i, i)
        if ch == quote then return table.concat(bytes), i + 1, true end
        if ch == "\n" then break end
        if ch == "\\" then
            local text, after = escapeAt(source, i, name, line)
            bytes[#bytes + 1] = text
            i = after
        else
            bytes[#bytes + 1] = ch
            i = i + 1
        end
    end
    return nil, i, false
end

-- Numbers -----------------------------------------------------------------------------------------
-- A separator is allowed between digits, so `1_000_000` and `0xffff_ffff` read as they look. One that
-- leads, trails or doubles is refused, rather than being ignored into a different value.
local function scanDigits(source, i, n, class, name, line)
    local cursor, any = i, false
    while cursor <= n do
        local ch = source:sub(cursor, cursor)
        if ch:match(class) then
            any, cursor = true, cursor + 1
        elseif ch == "_" then
            if not any or not source:sub(cursor + 1, cursor + 1):match(class) then
                D.reject("lex-number", "A digit separator needs a digit on both sides",
                    span(name, line, cursor, cursor + 1))
            end
            cursor = cursor + 1
        else
            break
        end
    end
    return cursor
end

-- A binary literal is rewritten as hexadecimal so a value too wide for a word takes the same exact
-- 64-bit path a hexadecimal literal takes.
local function binaryToHex(digits)
    local padded = digits
    local remainder = #padded % 4
    if remainder ~= 0 then padded = string.rep("0", 4 - remainder) .. padded end
    return (padded:gsub("%x%x%x%x", function(nibble) return string.format("%x", tonumber(nibble, 2)) end))
end

-- Returns a dense list of tokens: { kind = "name"|"keyword"|"number"|"string"|"byte"|"op"|"eof",
-- text, value, span }.
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
            local level, cursor = longOpen(source, n, i + 2, true)
            if level then
                local body, after = longBody(source, cursor, level)
                if not body then
                    D.reject("lex-comment", "Unterminated long comment", span(name, line, i, n))
                end
                line = line + newlinesIn(source:sub(i, after - 1))
                i = after
            else
                -- Leave the newline to be consumed by the main loop so line counting stays correct.
                local nl = source:find("\n", i + 2, true)
                i = nl or (n + 1)
            end
        elseif c:match(name_start) then
            local start = i
            while i <= n and source:sub(i, i):match(name_char) do i = i + 1 end
            local text = source:sub(start, i - 1)
            tokens[#tokens + 1] = { kind = KEYWORDS[text] and "keyword" or "name", text = text,
                span = span(name, line, start, i) }
        elseif c == "\"" or c == "'" then
            local start, startLine = i, line
            local body, after, closed = quoted(source, n, i, c, name, line)
            if not closed then
                D.reject("lex-string", "Unterminated literal", span(name, startLine, start, after))
            end
            i = after
            if c == "\"" then
                tokens[#tokens + 1] = { kind = "string", text = source:sub(start, after - 1),
                    value = body, span = span(name, startLine, start, after) }
            else
                if #body ~= 1 then
                    D.reject("lex-string",
                        "A byte literal holds exactly one byte; use a string literal for text",
                        span(name, startLine, start, after))
                end
                tokens[#tokens + 1] = { kind = "byte", text = source:sub(start, after - 1),
                    value = body:byte(1), span = span(name, startLine, start, after) }
            end
        elseif c == "[" then
            local level, cursor = longOpen(source, n, i, false)
            if level then
                local start, startLine = i, line
                local body, after = longBody(source, cursor, level)
                if not body then
                    D.reject("lex-string", "Unterminated long string", span(name, startLine, start, n))
                end
                line = line + newlinesIn(source:sub(start, after - 1))
                i = after
                tokens[#tokens + 1] = { kind = "string", text = source:sub(start, after - 1),
                    value = body, span = span(name, startLine, start, after) }
            else
                tokens[#tokens + 1] = { kind = "op", text = "[", span = span(name, line, i, i + 1) }
                i = i + 1
            end
        elseif c:match("%d") then
            local start, startLine = i, line
            local text
            local isFloat = false
            if source:sub(i, i + 1):lower() == "0x" then
                local digits = scanDigits(source, i + 2, n, "%x", name, line)
                if digits == i + 2 then
                    D.reject("lex-number", "Hexadecimal literal has no digits", span(name, line, start, digits))
                end
                text = "0x" .. source:sub(i + 2, digits - 1):gsub("_", "")
                i = digits
            elseif source:sub(i, i + 1):lower() == "0b" then
                local digits = scanDigits(source, i + 2, n, "[01]", name, line)
                if digits == i + 2 then
                    D.reject("lex-number", "Binary literal has no digits", span(name, line, start, digits))
                end
                text = "0x" .. binaryToHex(source:sub(i + 2, digits - 1):gsub("_", ""))
                i = digits
            else
                -- A decimal literal is an integer unless it has a fraction or an exponent. A float needs
                -- a digit on both sides of the point, so `1.` stays the integer 1 followed by a `.`, and
                -- a member selection never has to guess which was meant.
                local digits = scanDigits(source, i, n, "%d", name, line)
                local integerPart = source:sub(start, digits - 1):gsub("_", "")
                i = digits
                local fraction
                if source:sub(i, i) == "." and source:sub(i + 1, i + 1):match("%d") then
                    local fractionDigits = scanDigits(source, i + 1, n, "%d", name, line)
                    fraction = source:sub(i + 1, fractionDigits - 1):gsub("_", "")
                    i = fractionDigits
                end
                local exponent = ""
                local marker = source:sub(i, i)
                if marker == "e" or marker == "E" then
                    local cursor = i + 1
                    local sign = ""
                    local maybeSign = source:sub(cursor, cursor)
                    if maybeSign == "+" or maybeSign == "-" then sign, cursor = maybeSign, cursor + 1 end
                    local exponentDigits = scanDigits(source, cursor, n, "%d", name, line)
                    if exponentDigits == cursor then
                        D.reject("lex-number", "An exponent needs digits", span(name, line, i, cursor))
                    end
                    exponent = marker .. sign .. source:sub(cursor, exponentDigits - 1):gsub("_", "")
                    i = exponentDigits
                end
                if fraction or exponent ~= "" then
                    local value = tonumber(integerPart .. "." .. (fraction or "0") .. exponent)
                    if value == nil then
                        D.reject("lex-number", "Malformed float literal", span(name, startLine, start, i))
                    end
                    tokens[#tokens + 1] = { kind = "float", text = source:sub(start, i - 1),
                        value = value, span = span(name, startLine, start, i) }
                    isFloat = true
                else
                    text = integerPart
                end
            end
            -- A literal that does not fit a word arrives as its two words, and one that needs more
            -- than 64 bits is refused rather than wrapped.
            if not isFloat then
                local value = tonumber(text)
                if value == nil or value > 4294967295 then
                    local high, low = U64.fromstring(text)
                    if not high then
                        D.reject("lex-range", "Integer literal exceeds 64 bits",
                            span(name, startLine, start, i))
                    end
                    value = { high = high, low = low }
                end
                tokens[#tokens + 1] = { kind = "number", text = source:sub(start, i - 1),
                    value = value, span = span(name, startLine, start, i) }
            end
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
