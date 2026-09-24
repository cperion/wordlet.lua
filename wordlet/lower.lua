-- Lowering a closed artifact to C11. Header and source are two views of the same layouts.
local S = require("wordlet.schema")
local D = require("wordlet.diag")
local M = {}

local Ir = S.Ir
local U64Kernel = require("wordletkit.u64")
local Contextual = require("wordlet.contextual")

-- Same injective escape as the ABI layer: every non-alphanumeric byte becomes _XX.
function M.escape(name)
    return (name:gsub("[^%w]", function(c) return string.format("_%02X", c:byte()) end))
end

local function fieldName(name) return "f_" .. M.escape(name) end

local BINARY_OP = {
    Add = "+", Sub = "-", Mul = "*", Div = "/", Rem = "%",
    BitAnd = "&", BitOr = "|", BitXor = "^", Shl = "<<", Shr = ">>",
    Eq = "==", Ne = "!=", Lt = "<", Le = "<=", Gt = ">", Ge = ">=",
}
local UNARY_OP = { Neg = "-", BitNot = "~" }

-- The expression operands of an expression. The traversal itself is `Ir.Expr:each`, so a pass
-- cannot disagree with a node about what it contains.
local function collectExprs(expr, out)
    expr:each(function(operand) out[#out + 1] = operand end)
end

-- A double written so C reads exactly the same value: `%.17g` round-trips, and a decimal point or an
-- exponent keeps it a floating constant rather than an integer one. An infinity or a NaN has no
-- literal spelling, so it is named from <math.h>, which is included only when one appears.
local function doubleText(n)
    if n ~= n then return "NAN" end
    if n == math.huge then return "INFINITY" end
    if n == -math.huge then return "(-INFINITY)" end
    local text = string.format("%.17g", n)
    if not text:find("[.eEnN]") then text = text .. ".0" end
    return text
end

-- A shift amount that is a compile-time constant below the width needs no run-time range guard.
local function shiftInRange(expr, width)
    if expr.kind ~= "Const" then return false end
    local literal = expr.literal
    return literal.kind == "UInt" and literal.value < width
end

local Emitter = {}
Emitter.__index = Emitter
-- One emitter per function, reading the analysis that `wordlet/analysis.lua` computed for it.
local function newEmitter(layouts, signature, analysis)
    return setmetatable({ layouts = layouts, lines = {}, indent = 1,
        placeParams = (signature and signature.placeParams) or {},
        usedStorages = analysis.storageUses,
        usedValues = analysis.valueUses,
        mutatedStorages = analysis.mutatedStorages,
        paramValues = analysis.paramValues,
        storageAlias = {},
        shared = analysis.shared,
        decls = analysis.sharedDecls,
        inline = analysis.inline,
        useCount = analysis.useCount,
        assigned = {}, nextTemp = 0 }, Emitter)
end
function Emitter:line(text) self.lines[#self.lines + 1] = string.rep("    ", self.indent) .. text end
function Emitter:raw(text) self.lines[#self.lines + 1] = text end
function Emitter:name(kind, id) return (self.prefix or "") .. kind .. id end
function Emitter:value(id) return self:name("v", id) end
function Emitter:storage(id) return self:name("s", id) end

-- A shared expression is declared once and referenced by name; every other expression renders inline.
function Emitter:expr(expr)
    local name = self.assigned and self.assigned[expr]
    if name then return name end
    return self:render(expr)
end

-- The compound literal a variant construction prints as. Used both for the definition statement and
-- for a single-use definition lowered at its use.
function Emitter:constructText(stmt)
    local layout = self.layouts.tagLayout(stmt.type)
    local cased = layout.cases[S.tagIndex(stmt.type, stmt.tag) + 1]
    local text = "(" .. layout.name .. "){ .wordlet_tag = " .. cased.tag
    if stmt.payload then
        text = text .. ", .payload." .. cased.name .. " = " .. self:expr(stmt.payload)
    end
    return text .. " }"
end

-- The C expression a single-use definition lowers to.
function Emitter:definitionText(stmt)
    if stmt.kind == "Let" then return self:expr(stmt.expr) end
    if stmt.kind == "ConstructVariant" then return self:constructText(stmt) end
    if stmt.kind == "VariantMatches" then
        -- No outer parentheses: the consumer parenthesises an operand, and an extra pair around a
        -- comparison used as a condition fires clang's -Wparentheses-equality.
        local tag = S.tagIndex(stmt.sum, stmt.tag)
        return self:valueOrInline(stmt.variant.id) .. ".wordlet_tag == " .. tostring(tag)
    end
    if stmt.kind == "VariantPayload" then
        local cased = self.layouts.tagLayout(stmt.sum).cases[S.tagIndex(stmt.sum, stmt.tag) + 1]
        return "(" .. self:valueOrInline(stmt.variant.id) .. ".payload." .. cased.name .. ")"
    end
    D.bug("c-inline", "No inline form for " .. tostring(stmt.kind))
end

-- A value lowered at its use, or its own local when it has more than one use.
function Emitter:valueOrInline(id)
    local inlined = self.inline and self.inline[id]
    if inlined then
        if inlined.place then return self:placeC(inlined.place) end
        return self:definitionText(inlined.stmt)
    end
    return self:value(id)
end

function Emitter:tempName()
    self.nextTemp = self.nextTemp + 1
    return self:name("e", self.nextTemp)
end

-- Emits one local for a shared expression. Shared descendants are declared first so operands are
-- available; `render` prints the node's own body rather than its own name.
function Emitter:declareShared(node)
    if self.assigned[node] then return end
    local function visit(expr)
        local children = {}
        collectExprs(expr, children)
        for _, child in ipairs(children) do
            if self.shared[child] then self:declareShared(child) else visit(child) end
        end
    end
    visit(node)
    local name = self:tempName()
    self.assigned[node] = name
    self:line(self.layouts:cType(node.type) .. " " .. name .. " = " .. self:render(node) .. ";")
end

function Emitter:render(expr)
    local kind = expr.kind
    if kind == "Const" then
        if expr.literal.kind == "UInt64" then
            local text = U64Kernel.tostring(expr.literal.high, expr.literal.low, expr.type:isSigned())
            if expr.type:isSigned() then return "INT64_C(" .. text .. ")" end
            return "UINT64_C(" .. text .. ")"
        end
        if expr.literal.kind == "UInt" then
            if expr.type:isSigned() then return "INT32_C(" .. expr.literal.value .. ")" end
            return "UINT32_C(" .. expr.literal.value .. ")"
        end
        if expr.literal.kind == "Boolean" then return expr.literal.value and "true" or "false" end
        if expr.literal.kind == "Float" then
            local n = expr.literal.value
            if n ~= n or n == math.huge or n == -math.huge then
                self.layouts.usesFloatSpecials = true
            end
            return doubleText(n)
        end
        if expr.literal.kind == "Str" then
            -- A string literal is read-only static storage plus its length. Identical literals share
            -- one buffer, so the emitted object does not depend on how often one is written.
            local key = expr.literal.bytes
            local index = self.layouts.stringIndex[key]
            if not index then
                index = self.layouts.stringCount + 1
                self.layouts.stringCount = index
                self.layouts.stringIndex[key] = index
                self.layouts.strings[index] = key
            end
            local layout = self.layouts.sliceLayout(expr.type)
            return "(" .. layout.name .. "){ .f_data = (uint8_t *)wordlet_str_" .. index
                .. ", .f_length = UINT32_C(" .. #key .. ") }"
        end
        D.bug("c-literal", "Unknown literal")
    elseif kind == "Ref" then
        return self:valueOrInline(expr.value.id)
    elseif kind == "Un" then
        local op = expr.op.kind
        if op == "Not" then return "(!(" .. self:expr(expr.operand) .. "))" end
        local operand = self:expr(expr.operand)
        -- A double negates as itself; the bit-pattern dance below is for integers only.
        if expr.type:isF64() then return "(-(" .. operand .. "))" end
        if expr.type:isSigned() then
            -- Negation and complement of a signed value are done on the bit pattern.
            if op == "Neg" then
                return "wordlet_i32(UINT32_C(0) - wordlet_u32(" .. operand .. "))"
            end
            return "wordlet_i32(~wordlet_u32(" .. operand .. "))"
        end
        return "((uint32_t)(" .. UNARY_OP[op] .. "(" .. operand .. ")))"
    elseif kind == "Bin" then
        local op, left, right = expr.op.kind, self:expr(expr.left), self:expr(expr.right)
        if op == "Pow" then
            self.layouts.usespow32 = true
            local resultType = self.layouts:cType(expr.type)
            if expr.type:isSigned() then
                return "wordlet_i32(wordlet_pow(wordlet_u32(" .. left .. "), " .. right .. "))"
            end
            if resultType == "uint32_t" then return "wordlet_pow(" .. left .. ", " .. right .. ")" end
            return "(" .. resultType .. ")wordlet_pow(" .. left .. ", " .. right .. ")"
        end
        local cOp = BINARY_OP[op]
        if not cOp then D.bug("c-op", "No C operator for " .. tostring(op)) end
        if expr.left.type:isF64() or expr.right.type:isF64() then
            -- IEEE arithmetic and comparison are exactly C's, including a NaN comparing false and a
            -- division by zero producing an infinity rather than trapping.
            return "(" .. self:expr(expr.left) .. ") " .. cOp .. " (" .. self:expr(expr.right) .. ")"
        end
        local resultType = self.layouts:cType(expr.type)
        if expr.type:isWide() then
            -- A signed 64-bit operation reinterprets the bit pattern of its operands.
            if expr.type:isSigned() then
                self.layouts.usesi64 = true
                self.layouts.usesu64 = true
            end
            if op == "Div" then
                if expr.type:isSigned() then self.layouts.usesdiv = true end
                if expr.type:isSigned() then return "wordlet_div_i64(" .. left .. ", " .. right .. ")" end
                return "(" .. left .. " / " .. right .. ")"
            end
            if op == "Rem" then
                if expr.type:isSigned() then
                    self.layouts.usesrem = true
                    return "wordlet_rem_i64(" .. left .. ", " .. right .. ")"
                end
                return "(" .. left .. " % " .. right .. ")"
            end
            if op == "Pow" then
                self.layouts.usespow = true
                if expr.type:isSigned() then
                    return "wordlet_i64(wordlet_pow64(wordlet_u64(" .. left .. "), wordlet_u64("
                        .. right .. ")))"
                end
                return "wordlet_pow64(" .. left .. ", " .. right .. ")"
            end
            if expr.type:isSigned() then
                -- Arithmetic on the bit pattern, so overflow wraps rather than being undefined.
                if op == "Add" or op == "Sub" or op == "Mul" then
                    return "wordlet_i64(wordlet_u64(" .. left .. ") " .. cOp .. " wordlet_u64("
                        .. right .. "))"
                end
                if op == "Shl" then
                    if shiftInRange(expr.right, 64) then
                        return "wordlet_i64(wordlet_u64(" .. left .. ") << (" .. right .. "))"
                    end
                    return "wordlet_i64(wordlet_u64(" .. left .. ") << ((" .. right
                        .. ") >= UINT64_C(64) ? UINT64_C(0) : (" .. right .. ")))"
                end
                if op == "Shr" then
                    self.layouts.usesshr = true
                    return "wordlet_shr_i64(" .. left .. ", wordlet_u64(" .. right .. "))"
                end
                if op == "BitAnd" or op == "BitOr" or op == "BitXor" then
                    return "wordlet_i64(wordlet_u64(" .. left .. ") " .. cOp .. " wordlet_u64("
                        .. right .. "))"
                end
            end
        end
        if op == "Div" and expr.type:isSigned() then
            return "wordlet_div_i32(" .. left .. ", " .. right .. ")"
        end
        if op == "Rem" and expr.type:isSigned() then
            return "wordlet_rem_i32(" .. left .. ", " .. right .. ")"
        end
        if expr.type:isSigned() then
            -- Arithmetic on the bit pattern, then reinterpreted, so overflow wraps.
            if op == "Add" or op == "Sub" or op == "Mul" then
                return "wordlet_i32((uint32_t)((uint64_t)wordlet_u32(" .. left
                    .. ") " .. cOp .. " (uint64_t)wordlet_u32(" .. right .. ")))"
            end
            if op == "Shl" then
                if shiftInRange(expr.right, 32) then
                    return "wordlet_i32(wordlet_u32(" .. left .. ") << (" .. right .. "))"
                end
                return "wordlet_i32(wordlet_u32(" .. left .. ") << ((" .. right
                    .. ") >= UINT32_C(32) ? UINT32_C(0) : (" .. right .. ")))"
            end
            if op == "Shr" then return "wordlet_shr_i32(" .. left .. ", " .. right .. ")" end
            if op == "BitAnd" or op == "BitOr" or op == "BitXor" then
                return "wordlet_i32(wordlet_u32(" .. left .. ") " .. cOp .. " wordlet_u32("
                    .. right .. "))"
            end
        end
        if op == "Add" or op == "Sub" or op == "Mul" then
            -- The intermediate is wide enough for every width here, and the cast is the wrap.
            return "(" .. resultType .. ")((uint64_t)(" .. left .. ") " .. cOp .. " (uint64_t)("
                .. right .. "))"
        end
        if op == "Shl" or op == "Shr" then
            local width = S.widthOf(expr.type) or 32
            if shiftInRange(expr.right, width) then
                return "(" .. resultType .. ")((uint64_t)(" .. left .. ") " .. cOp .. " (" .. right .. "))"
            end
            return "(" .. resultType .. ")((" .. right .. ") >= UINT32_C("
                .. tostring(width) .. ") ? UINT32_C(0) : ((uint64_t)("
                .. left .. ") " .. cOp .. " (" .. right .. ")))"
        end
        if op == "BitAnd" or op == "BitOr" or op == "BitXor" then
            return "(" .. resultType .. ")((" .. left .. ") " .. cOp .. " (" .. right .. "))"
        end
        if (op == "Eq" or op == "Ne") and expr.left.type:isString() then
            -- A byte string compares by content. The helper tests the length first, so unequal
            -- strings never read either buffer.
            self.layouts.usesstreq = true
            local call = "wordlet_streq(" .. left .. ", " .. right .. ")"
            return op == "Eq" and call or ("(!" .. call .. ")")
        end
        -- A comparison keeps its operands parenthesised but not the whole expression: an extra outer
        -- pair makes clang's -Wparentheses-equality fire when the comparison is a condition.
        return "(" .. left .. ") " .. cOp .. " (" .. right .. ")"
    elseif kind == "Make" and expr.type:isSlice() then
        -- A slice is a compound literal: the address of the first element and the length.
        local layout = self.layouts.sliceLayout(expr.type)
        return "(" .. layout.name .. "){ .f_data = " .. self:expr(expr.fields[1])
            .. ", .f_length = " .. self:expr(expr.fields[2]) .. " }"
    elseif kind == "Make" and (S.environmentOf(expr.type)):isArray() then
        -- An array is a struct holding a C array, so its elements initialise that member.
        local layout = self.layouts.arrayLayout(S.environmentOf(expr.type))
        local items = {}
        for index, item in ipairs(expr.fields) do items[index] = self:expr(item) end
        return "(" .. layout.name .. "){ .f_data = { " .. table.concat(items, ", ") .. " } }"
    elseif kind == "Make" then
        -- An Owned callable is represented by its environment record.
        local record = S.environmentOf(expr.type)
        local layout = self.layouts.recordLayout(record)
        local fields = {}
        for index, field in ipairs(record.fields) do
            fields[#fields + 1] = "." .. layout.fields[index].name .. " = " .. self:expr(expr.fields[index])
        end
        return "(" .. layout.name .. "){" .. table.concat(fields, ", ") .. "}"
    elseif kind == "Get" then
        return "(" .. self:expr(expr.aggregate) .. ")." .. fieldName(expr.field.name)
    elseif kind == "Convert" then
        -- A cast makes a width change exact, and a signedness change at one width reinterprets the
        -- bit pattern. The source type is cast first, so a widening sign extends when it should.
        local operand = self:expr(expr.operand)
        local from, to = expr.operand.type, expr.type
        if from:isSigned() ~= to:isSigned() and S.widthOf(from) == S.widthOf(to) then
            if to:isWide() then
                if to:isSigned() then
                    self.layouts.usesi64 = true
                    return "wordlet_i64(" .. operand .. ")"
                end
                self.layouts.usesu64 = true
                return "wordlet_u64(" .. operand .. ")"
            end
            if to:isSigned() then return "wordlet_i32(" .. operand .. ")" end
            return "wordlet_u32(" .. operand .. ")"
        end
        return "(" .. self.layouts:cType(to) .. ")(" .. self.layouts:cType(from) .. ")(" .. operand .. ")"
    elseif kind == "Addr" then
        -- The address of a place: a root plus field names, with no load.
        return "&(" .. self:placeC(expr.place) .. ")"
    elseif kind == "Null" then
        self.layouts.usesNull = true
        return "NULL"
    elseif kind == "SliceLength" then
        return "(" .. self:expr(expr.view) .. ").f_length"
    end
    D.todo("c-expr", "No C lowering for expression " .. tostring(kind))
end

function Emitter:placeC(place)
    if place.kind == "Local" then
        local module = self.layouts.modules and self.layouts.modules.index[place.storage]
        if module then return module.name end
        local alias = self.storageAlias and self.storageAlias[place.storage.id]
        if alias then return alias end
        local name = self:storage(place.storage.id)
        -- A place parameter is already a pointer; a Var is the storage itself.
        return self.placeParams[place.storage.id] and ("(*" .. name .. ")") or name
    end
    if place.kind == "Project" then
        return self:placeC(place.base) .. "." .. fieldName(place.field.name)
    end
    if place.kind == "Deref" then
        return "(*(" .. self:placeC(place.base) .. "))"
    end
    if place.kind == "Index" then
        -- Elements live in the array member, and the index expression is a plain U32 value.
        return self:placeC(place.base) .. ".f_data[" .. self:expr(place.index) .. "]"
    end
    if place.kind == "PtrIndex" then
        -- A pointer carries no length, so the address is the only thing between here and the element.
        return "(" .. self:expr(place.view) .. ")[" .. self:expr(place.index) .. "]"
    end
    if place.kind == "SliceIndex" then
        -- The view is a value, so its element is reached through the view's pointer member.
        return "(" .. self:expr(place.view) .. ").f_data[" .. self:expr(place.index) .. "]"
    end
    D.todo("c-place", "No C lowering for place " .. tostring(place.kind))
end

function Emitter:borrow(place)
    return "&(" .. self:placeC(place) .. ")"
end

function Emitter:declare(ty, name, initial)
    local cType = self.layouts:cType(ty)
    if initial then
        self:line(cType .. " " .. name .. " = " .. initial .. ";")
    else
        -- An uninitialised local is a join slot, and the checker proved every reachable continuation
        -- assigns it before the read. Zeroing it would be storage the program does not need, so the
        -- declaration stands alone.
        self:line(cType .. " " .. name .. ";")
    end
end

function Emitter:statements(list)
    local index = 1
    while index <= #list do
        local stmt = list[index]
        -- Shared expressions are declared at the innermost list that contains all their uses,
        -- immediately before the first statement that needs them.
        local pending = self.decls and self.decls[list] and self.decls[list][index]
        if pending then
            for _, node in ipairs(pending) do self:declareShared(node) end
        end
        local kind = stmt.kind
        local advance = 1
        if kind == "Let" then
            if not (self.inline and self.inline[stmt.value.id]) then
                self:declare(stmt.type, self:value(stmt.value.id), self:expr(stmt.expr))
            end
        elseif kind == "Var" then
            local initial = stmt.initial
            if initial and initial.kind == "Ref" and self.paramValues[initial.value.id]
                and not (self.mutatedStorages and self.mutatedStorages[stmt.storage.id]) then
                -- A read-only by-value parameter already is the C local the place would name, so the
                -- place aliases it instead of paying for a copy of the whole struct.
                self.storageAlias[stmt.storage.id] = self:value(initial.value.id)
            elseif self.usedStorages[stmt.storage.id] then
                -- A loop-carried Var is declared before its Loop, but a specialization's base case
                -- may never read or store it. An initializer is a pure Expr, so dropping an
                -- unreferenced Var is safe and keeps the emitted C free of unused locals.
                self:declare(stmt.type, self:storage(stmt.storage.id), stmt.initial and self:expr(stmt.initial))
            end
        elseif kind == "Read" then
            -- A read is pure, so one whose result no `Ref` ever names is dead, exactly as an
            -- unreferenced `Var` is. A read lowered at its single use needs no local either.
            if self.usedValues[stmt.value.id] and not (self.inline and self.inline[stmt.value.id]) then
                self:declare(stmt.type, self:value(stmt.value.id), self:placeC(stmt.place))
            end
        elseif kind == "Store" then
            self:line(self:placeC(stmt.place) .. " = " .. self:expr(stmt.value) .. ";")
        elseif kind == "If" then
            self:line("if (" .. self:expr(stmt.test) .. ") {")
            self.indent = self.indent + 1
            self:statements(stmt.yes)
            self.indent = self.indent - 1
            if #stmt.no > 0 then
                self:line("} else {")
                self.indent = self.indent + 1
                self:statements(stmt.no)
                self.indent = self.indent - 1
            end
            self:line("}")
        elseif kind == "Switch" then
            self:switch(stmt)
        elseif kind == "Loop" then
            self:line("for (;;) {")
            self.indent = self.indent + 1
            self:statements(stmt.body)
            self.indent = self.indent - 1
            self:line("}")
        elseif kind == "Next" then
            self:line("continue;")
        elseif kind == "Trap" then
            self.layouts.usesAbort = true
            self:line("if (" .. self:expr(stmt.failure) .. ") abort();")
        elseif kind == "ConstructVariant" then
            if not (self.inline and self.inline[stmt.value.id]) then self:construct(stmt) end
        elseif kind == "VariantMatches" then
            if not (self.inline and self.inline[stmt.value.id]) then
                local tag = S.tagIndex(stmt.sum, stmt.tag)
                self:declare(S.Bool, self:value(stmt.value.id),
                    "(" .. self:valueOrInline(stmt.variant.id) .. ".wordlet_tag == " .. tag .. ")")
            end
        elseif kind == "VariantPayload" then
            if not (self.inline and self.inline[stmt.value.id]) then
                local case = S.caseOf(stmt.sum, stmt.tag)
                local cased = self.layouts.tagLayout(stmt.sum).cases[S.tagIndex(stmt.sum, stmt.tag) + 1]
                self:declare(case, self:value(stmt.value.id),
                    "(" .. self:valueOrInline(stmt.variant.id) .. ".payload." .. cased.name .. ")")
            end
        elseif kind == "Call" then
            advance = self:call(stmt, list, index)
        elseif kind == "Indirect" then
            self:indirect(stmt)
        elseif kind == "View" then
            self:makeView(stmt)
        elseif kind == "Return" then
            self:line(self:returnText(stmt.values))
        else
            D.todo("c-stmt", "No C lowering for statement " .. tostring(kind))
        end
        index = index + advance
    end
end

-- A tag switch. The last case carries `fallback` and becomes `default`, so the switch is total and a
-- dense tag range lowers to one jump table instead of a chain of compares. Each case body is braced
-- so a declaration right after the label is valid C and a case cannot fall into the next.
function Emitter:switch(stmt)
    self:line("switch (" .. self:valueOrInline(stmt.variant.id) .. ".wordlet_tag) {")
    for _, case in ipairs(stmt.cases) do
        if case.fallback then
            self:line("default: {")
        else
            self:line("case " .. S.tagIndex(stmt.sum, case.tag) .. ": {")
        end
        self.indent = self.indent + 1
        self:statements(case.body)
        self:line("break;")
        self.indent = self.indent - 1
        self:line("}")
    end
    self:line("}")
end

-- A variant is a compound literal with the tag and the one payload member set by name.
function Emitter:construct(stmt)
    self:declare(stmt.type, self:value(stmt.value.id), self:constructText(stmt))
end

function Emitter:call(stmt, list, index)
    if self.unit then
        local consumed = Contextual.call(self, stmt, list, index)
        if consumed then return consumed end
    end
    local signature = self.layouts.signatures[stmt.target]
    if not signature then D.bug("c-target", "Call to unknown function " .. stmt.target) end
    local args = {}
    for _, arg in ipairs(stmt.arguments) do
        if arg.kind == "ValueArg" then
            args[#args + 1] = self:expr(arg.value)
        elseif arg.kind == "BorrowArg" then
            args[#args + 1] = self:borrow(arg.place)
        else
            D.todo("c-arg", "No C lowering for argument " .. tostring(arg.kind))
        end
    end
    local call = signature.name .. "(" .. table.concat(args, ", ") .. ")"
    -- Call results are Ir.Value ids; their types are the target's declared results, positionally.
    local types = signature.fn.results
    local results = stmt.results
    local function referenced(expr, id)
        return expr and expr.kind == "Ref" and expr.value.id == id
    end
    -- A single-result call whose only use is the very next Store or Return is emitted at that use,
    -- so the result never lands in a temporary of its own.
    if #results == 1 and self.useCount and self.useCount[results[1].id] == 1 and list then
        local nextStatement = list[index + 1]
        local fuse = nextStatement ~= nil
            and ((nextStatement.kind == "Store" and referenced(nextStatement.value, results[1].id))
                or (nextStatement.kind == "Return" and #nextStatement.values == 1
                    and (not self.destination or self.destination.exit)
                    and referenced(nextStatement.values[1], results[1].id)))
        if fuse then
            local pending = self.decls and self.decls[list] and self.decls[list][index + 1]
            if pending then for _, node in ipairs(pending) do self:declareShared(node) end end
            if nextStatement.kind == "Store" then
                self:line(self:placeC(nextStatement.place) .. " = " .. call .. ";")
            else
                self:line("return " .. call .. ";")
            end
            return 2
        end
    end
    if #results == 0 then
        self:line(call .. ";")
    elseif #results == 1 then
        -- A discarded result needs no local: the call statement discards the value, and hiding it
        -- behind an unused local would only need a `(void)` to stay warning-free.
        if self.usedValues and self.usedValues[results[1].id] then
            self:declare(types[1], self:value(results[1].id), call)
        else
            self:line(call .. ";")
        end
    else
        local any = false
        for resultIndex = 1, #results do
            if self.usedValues and self.usedValues[results[resultIndex].id] then any = true end
        end
        if not any then
            self:line(call .. ";")
        else
            local layout = self.layouts.resultLayout(types)
            if not layout.name then D.bug("c-results", "Multiple results need a tuple layout") end
            -- The call produces one aggregate temporary; each used result becomes its own value.
            local packed = self:name("t", results[1].id)
            self:line(layout.name .. " " .. packed .. " = " .. call .. ";")
            for resultIndex = 1, #results do
                if self.usedValues and self.usedValues[results[resultIndex].id] then
                    self:declare(types[resultIndex], self:value(results[resultIndex].id),
                        packed .. ".f_" .. resultIndex)
                end
            end
        end
    end
    return 1
end

-- The adapter that lets a known callable be invoked through a view.
function M.adapterBodies(layouts)
    local lines = {}
    for _, adapter in ipairs(layouts.adapters.order) do
        local signature = layouts.signatures[adapter.entry]
        if not signature then D.bug("c-adapter", "Adapter target " .. adapter.entry .. " has no signature") end
        local returns = signature.results.kind == "void" and "void"
            or (signature.results.kind == "scalar" and layouts:cType(signature.results.type)
                or signature.results.name)
        local visible = {}
        for index = #adapter.bound + 1, #signature.params do
            local param = signature.params[index]
            local name = "a" .. (index - #adapter.bound)
            visible[#visible + 1] = layouts:cType(param.type) .. (param.pointer and " *" or " ") .. name
        end
        -- The bound inputs come first, matching the callee's hidden prefix.
        local ordered = {}
        for _, field in ipairs(adapter.bound) do ordered[#ordered + 1] = "env->" .. field.name end
        for index = #adapter.bound + 1, #signature.params do
            ordered[#ordered + 1] = "a" .. (index - #adapter.bound)
        end
        local body = {}
        -- The environment parameter is always present, so a bound callable with no visible inputs
        -- still has one parameter; `void` here would be the only parameter and is invalid C.
        body[#body + 1] = "static " .. returns .. " " .. adapter.fn .. "(const void *environment"
            .. (#visible > 0 and (", " .. table.concat(visible, ", ")) or "") .. ") {"
        if #adapter.bound == 0 then
            body[#body + 1] = "    (void)environment;"
        else
            body[#body + 1] = "    const " .. adapter.struct .. " *env = (const " .. adapter.struct
                .. " *)environment;"
        end
        local call = signature.name .. "(" .. table.concat(ordered, ", ") .. ")"
        body[#body + 1] = signature.results.kind == "void" and ("    " .. call .. ";") or ("    return " .. call .. ";")
        body[#body + 1] = "}"
        lines[#lines + 1] = table.concat(body, "\n")
    end
    return lines
end

-- An opaque callable is invoked through the pointer its view carries.
function Emitter:indirect(stmt)
    local types = stmt.callable.type
    if not types:isView() then D.bug("c-view", "Indirect needs a view-typed callable") end
    local layout = self.layouts.viewLayout(types)
    local args = {}
    for _, arg in ipairs(stmt.arguments) do
        if arg.kind ~= "ValueArg" then D.todo("c-arg", "Only by-value arguments are lowered yet") end
        args[#args + 1] = self:expr(arg.value)
    end
    local callable = self:expr(stmt.callable)
    local call = callable .. ".invoke(" .. callable .. ".environment"
        .. (#args > 0 and (", " .. table.concat(args, ", ")) or "") .. ")"
    if #stmt.results == 0 then
        self:line(call .. ";")
    elseif #stmt.results == 1 then
        self:declare(layout.results.type, self:value(stmt.results[1].id), call)
    else
        local packed = self:name("t", stmt.results[1].id)
        self:line(layout.results.name .. " " .. packed .. " = " .. call .. ";")
        for index = 1, #stmt.results do
            self:declare(layout.results.fields[index].type, self:value(stmt.results[index].id),
                packed .. ".f_" .. index)
        end
    end
end

-- Binds a callable's hidden inputs in a local adapter and takes its address.
function Emitter:makeView(stmt)
    if self.unit then self.unit.requireRoot(stmt.entry) end
    local types = stmt.type
    -- Either an erased callable view, or pure code: an owned callable with an empty environment.
    if not types:isView() and not (types:isOwned() and S.environmentOf(types) == S.Unit) then
        D.bug("c-view", "View needs a view type or an empty-environment callable type")
    end
    local layout = self.layouts.viewLayout(types)
    -- A borrowed slot is a pointer to the callee's hidden place input, so the target's own parameter
    -- list is what types it.
    local signature = self.layouts.signatures[stmt.entry]
    if not signature then D.bug("c-view", "View binds unknown code " .. tostring(stmt.entry)) end
    local bound, args = {}, {}
    for _, slot in ipairs(stmt.slots) do
        if slot.kind == "BorrowArg" then
            local param = signature.params[#bound + 1]
            if not param then D.bug("c-view", "View binds more places than the callee accepts") end
            bound[#bound + 1] = { type = param.type, pointer = true }
            args[#args + 1] = self:borrow(slot.place)
        else
            bound[#bound + 1] = { type = slot.value.type, pointer = false }
            args[#args + 1] = self:expr(slot.value)
        end
    end
    local adapter = self.layouts:viewAdapter(stmt.entry, bound)
    local value = self:value(stmt.value.id)
    if #args == 0 then
        self.layouts.usesNull = true
        self:line(layout.name .. " " .. value .. " = { .invoke = " .. adapter.fn
            .. ", .environment = NULL };")
        return
    end
    local adapterName = self:name("a", stmt.value.id)
    local fields = {}
    for index, field in ipairs(adapter.bound) do
        fields[#fields + 1] = "." .. field.name .. " = " .. args[index]
    end
    self:line(adapter.name .. " " .. adapterName .. " = {" .. table.concat(fields, ", ") .. "};")
    self:line(layout.name .. " " .. value .. " = { .invoke = " .. adapter.fn
        .. ", .environment = &" .. adapterName .. " };")
end

function Emitter:returnText(values)
    if self.destination then
        local localReturn = Contextual.returnText(self, values)
        if localReturn then return localReturn end
    end
    if #values == 0 then return "return;" end
    if #values == 1 then return "return " .. self:expr(values[1]) .. ";" end
    local types = {}
    for index, value in ipairs(values) do types[index] = value.type end
    local layout = self.layouts.resultLayout(types)
    local fields = {}
    for index, value in ipairs(values) do
        fields[#fields + 1] = ".f_" .. index .. " = " .. self:expr(value)
    end
    return "return (" .. layout.name .. "){" .. table.concat(fields, ", ") .. "};"
end

-- Declarations ---------------------------------------------------------------------------------

function M.typeDeclarations(layouts)
    local lines = {}
    -- Every generated aggregate carries a struct tag with its own name, so a pointer to one needs
    -- only a declaration. Bodies are then emitted in dependency order: a by-value member or a
    -- parameter list mentions a type that must already be complete, and that dependency runs in both
    -- directions (a record may hold a callable view, whose parameter list may mention a record), so
    -- no fixed order is correct. A genuine by-value cycle is reported rather than emitted.
    local definitions, order = {}, {}
    local function forward(name) lines[#lines + 1] = "typedef struct " .. name .. " " .. name .. ";" end
    for _, layout in ipairs(layouts.tuples.order) do forward(layout.name) end
    for _, layout in ipairs(layouts.records.order) do forward(layout.name) end
    for _, layout in ipairs(layouts.arrays.order) do forward(layout.name) end
    for _, layout in ipairs(layouts.slices.order) do forward(layout.name) end
    for _, layout in ipairs(layouts.sums.order) do forward(layout.name) end
    for _, layout in ipairs(layouts.tagged.order) do forward(layout.name) end
    for _, layout in ipairs(layouts.views.order) do forward(layout.name) end
    for _, layout in ipairs(layouts.adapters.order) do forward(layout.name) end

    -- Registering a definition walks its field types, which may register further layouts, so
    -- discovery and emission share one growing list.
    local function define(layout, needs, emit)
        if definitions[layout.name] then return definitions[layout.name] end
        local entry = { name = layout.name, needs = needs, emit = emit }
        definitions[layout.name] = entry
        order[#order + 1] = entry
        return entry
    end
    local function typeName(ty)
        if ty == S.Unit then return "void" end
        return layouts:cType(ty)
    end
    local function defineAggregate(layout, fields, isTag)
        local entry
        entry = define(layout, {}, function()
            local body = {}
            if isTag then body[#body + 1] = "    uint32_t wordlet_tag;" end
            local members, any = {}, false
            for _, field in ipairs(fields) do
                local cType = typeName(field.type)
                if not isTag then
                    if cType ~= "void" then
                        body[#body + 1] = "    " .. cType .. " " .. field.name .. ";"
                        any = true
                    end
                elseif cType == "void" then
                    members[#members + 1] = "        unsigned char " .. field.name .. ";"
                else
                    members[#members + 1] = "        " .. cType .. " " .. field.name .. ";"
                end
            end
            if isTag then
                if #members == 0 then
                    body[#body + 1] = "    unsigned char wordlet_pad;"
                else
                    body[#body + 1] = "    union {"
                    for _, member in ipairs(members) do body[#body + 1] = member end
                    body[#body + 1] = "    } payload;"
                end
            elseif not any then
                body[#body + 1] = "    unsigned char wordlet_pad;"
            end
            -- The forward pass already typedef'd the tag, so the body is a plain definition. Repeating
            -- the typedef here would warn under a C99 compiler even though C11 permits it.
            lines[#lines + 1] = "struct " .. layout.name .. " {\n"
                .. table.concat(body, "\n") .. "\n};"
        end)
        -- Needs are recorded by name and resolved when emitting, because discovery order does not
        -- decide definition order.
        for _, field in ipairs(fields) do
            if field.type ~= S.Unit then entry.needs[#entry.needs + 1] = layouts:cType(field.type) end
        end
        return entry
    end

    for _, layout in ipairs(layouts.tuples.order) do
        defineAggregate(layout, layout.fields, false)
    end
    for _, layout in ipairs(layouts.records.order) do
        defineAggregate(layout, layout.fields, false)
    end
    for _, layout in ipairs(layouts.arrays.order) do
        -- An array is a struct holding one C array, because a bare C array cannot be assigned or
        -- returned by value while a struct that contains one can. The element is embedded, so its
        -- layout is a completeness need.
        define(layout, { layouts:cType(layout.element) }, function()
            lines[#lines + 1] = "struct " .. layout.name .. " {\n    "
                .. layouts:cType(layout.element) .. " f_data[" .. tostring(layout.length)
                .. "];\n};"
        end)
    end
    for _, layout in ipairs(layouts.slices.order) do
        -- A slice is a pointer and a length. The element is named but not embedded, so the element
        -- type need not be complete yet, which is what keeps a recursive slice a finite layout.
        define(layout, {}, function()
            lines[#lines + 1] = "struct " .. layout.name .. " {\n    "
                .. layouts:cType(layout.element) .. " *f_data;\n    uint32_t f_length;\n};"
        end)
    end
    for _, layout in ipairs(layouts.sums.order) do
        defineAggregate(layout, layout.cases, true)
    end
    for _, layout in ipairs(layouts.tagged.order) do
        defineAggregate(layout, layout.cases, true)
    end
    -- A view mentions its visible parameter and result types in its function pointer, so those must
    -- be complete first. An adapter holds its by-value slots by value; a borrowed slot is a pointer.
    local function defineView(layout)
        local entry
        entry = define(layout, {}, function()
            lines[#lines + 1] = "struct " .. layout.name .. " {\n    "
                .. layout.returns .. " (*invoke)" .. layout.invoke .. ";"
                .. "\n    const void *environment;\n};"
        end)
        -- The recorded types are named so their layouts exist. A function-pointer declaration is
        -- allowed to mention an incomplete parameter type, so a parameter is not a completeness
        -- need; that is what lets a record hold a view that takes the record. A result type must be
        -- complete, so it is still a need and a view that returns the record stays a cycle.
        local types = {}
        if layout.results.kind == "scalar" then types[#types + 1] = layout.results.type end
        for _, param in ipairs(layout.parameters or {}) do
            if param.type then typeName(param.type) end
        end
        for _, ty in ipairs(types) do
            if ty ~= S.Unit then entry.needs[#entry.needs + 1] = typeName(ty) end
        end
        return entry
    end
    for _, layout in ipairs(layouts.views.order) do defineView(layout) end
    for _, adapter in ipairs(layouts.adapters.order) do
        local entry
        entry = define(adapter, {}, function()
            local fields = {}
            if #adapter.bound == 0 then
                fields[1] = "    unsigned char wordlet_pad;"
            else
                for _, field in ipairs(adapter.bound) do
                    fields[#fields + 1] = "    " .. layouts:cType(field.type)
                        .. (field.pointer and " *" or " ") .. field.name .. ";"
                end
            end
            lines[#lines + 1] = "struct " .. adapter.name .. " {\n"
                .. table.concat(fields, "\n") .. "\n};"
        end)
        for _, field in ipairs(adapter.bound) do
            if not field.pointer and field.type ~= S.Unit then
                entry.needs[#entry.needs + 1] = layouts:cType(field.type)
            end
        end
        -- The adapter body calls the target by value, so those types must be complete by then.
        local signature = layouts.signatures[adapter.entry]
        if signature then
            for _, param in ipairs(signature.params) do
                if S.runtime(param.type) then entry.needs[#entry.needs + 1] = layouts:cType(param.type) end
            end
            if signature.results.kind == "scalar" and S.runtime(signature.results.type) then
                entry.needs[#entry.needs + 1] = layouts:cType(signature.results.type)
            end
        end
    end

    -- Emitting a definition needs the definitions it embeds by value to be complete first, and the
    -- discovery order above is not a dependency order: a record is registered before the field types
    -- it names. A depth-first walk from each definition emits it after the ones it needs, so one pass
    -- over the graph replaces the readiness fixpoint, and a back edge names the cycle rather than
    -- leaving the caller to find it.
    local emitted, active, stack = {}, {}, {}
    local function emit(entry)
        if emitted[entry.name] then return end
        if active[entry.name] then
            local first = 1
            for index, name in ipairs(stack) do
                if name == entry.name then first = index; break end
            end
            local cycle = {}
            for index = first, #stack do cycle[#cycle + 1] = stack[index] end
            cycle[#cycle + 1] = entry.name
            D.todo("c-order", "These types contain each other by value: " .. table.concat(cycle, ", "))
        end
        active[entry.name] = true
        stack[#stack + 1] = entry.name
        for _, need in ipairs(entry.needs) do
            -- A name that defines no aggregate is a scalar type spelled directly in C.
            local dependency = definitions[need]
            if dependency then emit(dependency) end
        end
        stack[#stack] = nil
        active[entry.name] = nil
        entry.emit()
        emitted[entry.name] = true
    end
    for _, entry in ipairs(order) do emit(entry) end
    for _, exported in ipairs(layouts.typeExports) do
        lines[#lines + 1] = "typedef " .. exported.layout.name .. " " .. exported.name .. ";"
    end
    return lines
end

function M.signatureText(layouts, signature)
    local parameters = {}
    if #signature.params == 0 then parameters[1] = "void" end
    for _, param in ipairs(signature.params) do
        local pointer = param.pointer and " *" or " "
        parameters[#parameters + 1] = layouts:cType(param.type) .. pointer .. param.name
    end
    local returns = "void"
    if signature.results.kind == "scalar" then returns = layouts:cType(signature.results.type) end
    if signature.results.kind == "tuple" then returns = signature.results.name end
    -- A private residual function has internal linkage. `WORDLET_PRIVATE` asks GCC and clang to inline
    -- it and falls back to plain `static` on a compiler without the attribute; a non-tail self-recursive
    -- function uses plain `static` too, because GCC refuses to force-inline a recursive function. An
    -- export keeps external linkage for the host.
    local linkage = ""
    -- A foreign prototype is a plain declaration: external linkage, and no body to emit.
    if not signature.exported and not signature.foreign then
        if layouts.privateInline == false or (layouts.recursiveRoots and layouts.recursiveRoots[signature.fn.id]) then
            linkage = "static "
        else
            linkage = "WORDLET_PRIVATE "
        end
    end
    return linkage .. returns .. " " .. signature.name .. "(" .. table.concat(parameters, ", ") .. ")"
end

local function aliasOf(signature, name)
    local copy = {}
    for key, value in pairs(signature) do copy[key] = value end
    copy.name = name
    return copy
end

function M.prototypes(layouts)
    local lines = M.moduleDeclarations(layouts)
    -- A foreign word is declared, never defined: the host has the body.
    for _, signature in ipairs(layouts.foreignOrder) do
        lines[#lines + 1] = M.signatureText(layouts, signature) .. ";"
    end
    for _, instance in ipairs(layouts.order) do
        local signature = layouts.signatures[instance.target]
        lines[#lines + 1] = M.signatureText(layouts, signature) .. ";"
        for _, alias in ipairs(signature.aliases) do
            lines[#lines + 1] = M.signatureText(layouts, aliasOf(signature, alias)) .. ";"
        end
    end
    return lines
end

function M.prelude(layouts)
    local lines = {}
    -- The 32-bit power helper is only emitted when a body actually uses `^`.
    if layouts.usespow32 then
        lines[#lines + 1] = "uint32_t wordlet_pow(uint32_t base, uint32_t exponent) {"
        lines[#lines + 1] = "    uint32_t result = UINT32_C(1);"
        lines[#lines + 1] = "    while (exponent > UINT32_C(0)) {"
        lines[#lines + 1] = "        if ((exponent & UINT32_C(1)) != UINT32_C(0)) {"
        lines[#lines + 1] = "            result = (uint32_t)((uint64_t)result * (uint64_t)base);"
        lines[#lines + 1] = "        }"
        lines[#lines + 1] = "        exponent = exponent >> 1;"
        lines[#lines + 1] = "        if (exponent > UINT32_C(0)) {"
        lines[#lines + 1] = "            base = (uint32_t)((uint64_t)base * (uint64_t)base);"
        lines[#lines + 1] = "        }"
        lines[#lines + 1] = "    }"
        lines[#lines + 1] = "    return result;"
        lines[#lines + 1] = "}"
    end
    if layouts.usesstreq then
        -- Two byte strings are equal when their lengths match and their bytes match. Testing the
        -- length first means an unequal pair never reads either buffer.
        local layout = layouts.sliceLayout(S.String)
        lines[#lines + 1] = "static bool wordlet_streq(" .. layout.name .. " a, " .. layout.name .. " b) {"
        lines[#lines + 1] = "    if (a.f_length != b.f_length) return false;"
        lines[#lines + 1] = "    return a.f_length == UINT32_C(0) || memcmp(a.f_data, b.f_data, a.f_length) == 0;"
        lines[#lines + 1] = "}"
    end
    return lines
end

-- Read-only byte buffers for string literals, emitted once per distinct literal in first-use order
-- so the object is deterministic. A zero-length string still occupies one byte, because C has no
-- array of length zero.
function M.stringDeclarations(layouts)
    local lines = {}
    for index = 1, layouts.stringCount do
        local bytes = layouts.strings[index]
        local items = {}
        for position = 1, #bytes do items[#items + 1] = tostring(bytes:byte(position)) end
        if #items == 0 then items[1] = "0" end
        lines[#lines + 1] = "static const uint8_t wordlet_str_" .. index .. "[" .. #items .. "] = { "
            .. table.concat(items, ", ") .. " };"
    end
    return lines
end


function M.bodies(layouts)
    local lines = {}
    -- Discover actual roots/call cycles before rendering linkage. A logical function copied into
    -- a tail component is not necessarily a remaining C function.
    for _, body in ipairs(Contextual.bodies(layouts, newEmitter)) do
        local signature = body.signature
        lines[#lines + 1] = M.signatureText(layouts, signature) .. " {\n"
            .. table.concat(body.lines, "\n") .. "\n}"
        for _, alias in ipairs(signature.aliases) do
            local args = {}
            for index, param in ipairs(signature.params) do args[index] = param.name end
            local call = signature.name .. "(" .. table.concat(args, ", ") .. ")"
            local body = signature.results.kind == "void" and (call .. ";") or ("return " .. call .. ";")
            lines[#lines + 1] = M.signatureText(layouts, aliasOf(signature, alias)) .. " {\n    " .. body .. "\n}"
        end
    end
    return lines
end

-- Only the headers the emitted program actually uses. The bodies and declarations are built first,
-- which is what sets these flags, so the list is decided once every type and helper is known.
local function includes(layouts)
    local lines = { "#include <stdint.h>" }
    if layouts.usesBool then lines[#lines + 1] = "#include <stdbool.h>" end
    if layouts.usesNull then lines[#lines + 1] = "#include <stddef.h>" end
    if layouts.usesAbort then lines[#lines + 1] = "#include <stdlib.h>" end
    if layouts.usesSigned or layouts.usesWide or layouts.usesi64 or layouts.usesu64
        or layouts.usesdiv or layouts.usesrem or layouts.usesshr or layouts.usespow
        or layouts.usesstreq then
        lines[#lines + 1] = "#include <string.h>"
    end
    return lines
end


-- A 64-bit value is a C integer of its own width, but the signed operations still go through helpers
-- so that the cases C leaves undefined or implementation-defined - an overflowing signed operation,
-- the most negative value divided by -1, and a shift of a negative value - behave as two's complement.
-- Each wide helper is emitted only when a body needs it, because an unused static function is a
-- diagnostic under `-Werror`. The flags are set while bodies are emitted, which is why the helper text
-- is assembled after them.
local WIDE_HELPERS = {
    i64 = {
        "static int64_t wordlet_i64(uint64_t bits) { int64_t value; memcpy(&value, &bits, sizeof value); return value; }",
    },
    u64 = {
        "static uint64_t wordlet_u64(int64_t value) { uint64_t bits; memcpy(&bits, &value, sizeof bits); return bits; }",
    },
    div = {
        "static int64_t wordlet_div_i64(int64_t a, int64_t b) {",
        "    if (b == -1) return wordlet_i64(UINT64_C(0) - wordlet_u64(a));",
        "    return a / b;",
        "}",
    },
    rem = {
        "static int64_t wordlet_rem_i64(int64_t a, int64_t b) {",
        "    if (b == -1) return 0;",
        "    return a % b;",
        "}",
    },
    shr = {
        "static int64_t wordlet_shr_i64(int64_t value, uint64_t amount) {",
        "    if (amount == 0) return value;",
        "    if (amount >= 64) return value < 0 ? -1 : 0;",
        "    uint64_t filled = value < 0 ? (~UINT64_C(0) << (64 - amount)) : UINT64_C(0);",
        "    return wordlet_i64((wordlet_u64(value) >> amount) | filled);",
        "}",
    },
    -- An unsigned 64-bit power, which the 32-bit helper cannot express.
    pow = {
        "static uint64_t wordlet_pow64(uint64_t base, uint64_t exponent) {",
        "    uint64_t result = UINT64_C(1);",
        "    while (exponent > UINT64_C(0)) {",
        "        if ((exponent & UINT64_C(1)) != UINT64_C(0)) result = result * base;",
        "        exponent = exponent >> 1;",
        "        if (exponent > UINT64_C(0)) base = base * base;",
        "    }",
        "    return result;",
        "}",
    },
}

-- The wide helpers a layout needs, in dependency order. A helper that reinterprets the bit pattern
-- implies the two reinterpretation functions, because it is written in terms of them.
local WIDE_ORDER = { "i64", "u64", "div", "rem", "shr", "pow" }
local WIDE_DEPENDS = { div = { "i64", "u64" }, shr = { "i64", "u64" } }

function M.wideHelpers(layouts)
    local needed = {}
    for _, name in ipairs(WIDE_ORDER) do
        if layouts["uses" .. name] then
            needed[name] = true
            for _, dependency in ipairs(WIDE_DEPENDS[name] or {}) do needed[dependency] = true end
        end
    end
    if next(needed) == nil then return {} end
    local lines = {}
    for _, name in ipairs(WIDE_ORDER) do
        if needed[name] then
            for _, line in ipairs(WIDE_HELPERS[name]) do lines[#lines + 1] = line end
        end
    end
    return lines
end

-- Signed 32-bit values are held as their unsigned bit pattern and reinterpreted, because converting
-- an out-of-range unsigned value to a signed type is implementation-defined. Division and the right
-- shift are written out so that the two cases C leaves undefined or implementation-defined - the most
-- negative value divided by -1, and a shift of a negative value - behave as two's complement.
local SIGNED_HELPERS = {
    "static int32_t wordlet_i32(uint32_t bits) { int32_t value; memcpy(&value, &bits, sizeof value); return value; }",
    "static uint32_t wordlet_u32(int32_t value) { uint32_t bits; memcpy(&bits, &value, sizeof bits); return bits; }",
    "static int32_t wordlet_div_i32(int32_t a, int32_t b) {",
    "    if (b == -1) return wordlet_i32(UINT32_C(0) - wordlet_u32(a));",
    "    return a / b;",
    "}",
    "static int32_t wordlet_rem_i32(int32_t a, int32_t b) {",
    "    if (b == -1) return 0;",
    "    return a % b;",
    "}",
    "static int32_t wordlet_shr_i32(int32_t value, uint32_t amount) {",
    "    if (amount == 0) return value;",
    "    if (amount >= 32) return value < 0 ? -1 : 0;",
    "    uint32_t filled = value < 0 ? (~UINT32_C(0) << (32 - amount)) : UINT32_C(0);",
    "    return wordlet_i32((wordlet_u32(value) >> amount) | filled);",
    "}",
}

-- File-scope objects for module-level mutable state, plus the entry point that initialises them.
function M.moduleDeclarations(layouts)
    local lines = {}
    for _, module in ipairs(layouts.modules.order) do
        lines[#lines + 1] = "static " .. layouts:cType(module.type) .. " " .. module.name .. ";"
    end
    return lines
end

-- Bodies are emitted first: doing so is what registers the views, adapters and nested record
-- layouts that the declarations have to name.
-- A private residual function has internal linkage. GCC and clang are asked to inline it, because a
-- specialization usually has one caller; another C11 compiler, or a host that defines
-- WORDLET_NO_FORCED_INLINE, gets plain `static`.
function M.privateLinkage(layouts)
    if layouts.privateInline == false then return {} end
    return {
        "#if defined(__GNUC__) && !defined(WORDLET_NO_FORCED_INLINE)",
        "#define WORDLET_PRIVATE static inline __attribute__((always_inline))",
        "#else",
        "#define WORDLET_PRIVATE static",
        "#endif",
    }
end

-- A view of a closed artifact. `close` computed the emission, so every function below only reads:
-- a view called before that would walk a half-named layout set and could print different C twice.
local function closed(layouts)
    if not layouts.closed then
        D.bug("c-closed", "The layouts are not closed: call lower.close after cabi.close")
    end
    return layouts
end

-- Close the artifact: emit the bodies, the adapters and the declarations once, in dependency
-- order, and freeze them on the layouts. Naming a type is what decides which helpers the unit
-- needs, so this is the step that finishes the layout set; after it, `unit`, `source`, `header`
-- and `cdef` are consistent views of one artifact, and calling them in any order gives one answer.
function M.close(layouts)
    if layouts.closed then return layouts end
    layouts.bodies = M.bodies(layouts)
    layouts.adapterBodies = M.adapterBodies(layouts)
    layouts.declarations = M.typeDeclarations(layouts)
    layouts.closed = true
    return layouts
end

-- A `cdef` view: every type declaration and the exported prototypes, with no bodies and no private
-- symbols. A host feeds this to `ffi.cdef` and then `ffi.load`s the shared object it builds. Because
-- `ffi.cdef` is process-global, an optional namespace prefixes every generated type name so several
-- artifacts can be loaded side by side; the C names in the object are unaffected, since C struct
-- identity is layout, not spelling.
function M.cdef(layouts, namespace)
    closed(layouts)
    local lines = {}
    for _, line in ipairs(layouts.declarations) do lines[#lines + 1] = line end
    lines[#lines + 1] = ""
    for _, instance in ipairs(layouts.order) do
        local signature = layouts.signatures[instance.target]
        if signature.exported then
            lines[#lines + 1] = M.signatureText(layouts, signature) .. ";"
        end
    end
    local text = table.concat(lines, "\n")
    if namespace and namespace ~= "" then
        local names = {}
        for _, group in ipairs({ layouts.tuples.order, layouts.records.order, layouts.arrays.order,
            layouts.sums.order, layouts.tagged.order, layouts.views.order, layouts.adapters.order,
            layouts.slices.order }) do
            for _, layout in ipairs(group) do names[#names + 1] = layout.name end
        end
        for _, exported in ipairs(layouts.typeExports) do names[#names + 1] = exported.name end
        for _, name in ipairs(names) do
            text = text:gsub("%f[%w_]" .. name .. "%f[^%w_]", namespace .. name)
        end
    end
    return text
end

-- The whole translation unit: one file, so it is `source` with no header to include.
function M.unit(layouts)
    return M.source(layouts, nil)
end

function M.source(layouts, headerName)
    closed(layouts)
    local lines = {}
    if headerName then lines[#lines + 1] = '#include "' .. headerName .. '"' end
    for _, line in ipairs(includes(layouts)) do lines[#lines + 1] = line end
    if layouts.usesFloatSpecials then lines[#lines + 1] = "#include <math.h>" end
    for _, line in ipairs(M.privateLinkage(layouts)) do lines[#lines + 1] = line end
    lines[#lines + 1] = ""
    if layouts.usesSigned then
        for _, line in ipairs(SIGNED_HELPERS) do lines[#lines + 1] = line end
        lines[#lines + 1] = ""
    end
    local wide = M.wideHelpers(layouts)
    if #wide > 0 then
        for _, line in ipairs(wide) do lines[#lines + 1] = line end
        lines[#lines + 1] = ""
    end
    for _, line in ipairs(layouts.declarations) do lines[#lines + 1] = line end
    for _, line in ipairs(M.stringDeclarations(layouts)) do lines[#lines + 1] = line end
    lines[#lines + 1] = ""
    for _, line in ipairs(M.prototypes(layouts)) do lines[#lines + 1] = line end
    lines[#lines + 1] = ""
    for _, line in ipairs(M.prelude(layouts)) do lines[#lines + 1] = line end
    lines[#lines + 1] = ""
    for _, line in ipairs(layouts.adapterBodies) do
        lines[#lines + 1] = line
        lines[#lines + 1] = ""
    end
    for _, body in ipairs(layouts.bodies) do
        lines[#lines + 1] = body
        lines[#lines + 1] = ""
    end
    return table.concat(lines, "\n")
end

function M.header(layouts, name)
    closed(layouts)
    local guard = "WORDLET_" .. M.escape(name or "unit"):upper() .. "_H"
    local lines = { "#ifndef " .. guard, "#define " .. guard, "", "#include <stdint.h>", "#include <stdbool.h>", "" }
    for _, line in ipairs(layouts.declarations) do lines[#lines + 1] = line end
    lines[#lines + 1] = ""
    lines[#lines + 1] = "#ifdef __cplusplus"
    lines[#lines + 1] = 'extern "C" {'
    lines[#lines + 1] = "#endif"
    lines[#lines + 1] = ""
    local any = false
    for _, instance in ipairs(layouts.order) do
        local signature = layouts.signatures[instance.target]
        if signature.exported then
            any = true
            lines[#lines + 1] = M.signatureText(layouts, signature) .. ";"
            for _, alias in ipairs(signature.aliases) do
                lines[#lines + 1] = M.signatureText(layouts, aliasOf(signature, alias)) .. ";"
            end
        end
    end
    if not any then lines[#lines + 1] = "/* no exported functions */" end
    lines[#lines + 1] = ""
    lines[#lines + 1] = "#ifdef __cplusplus"
    lines[#lines + 1] = "}"
    lines[#lines + 1] = "#endif"
    lines[#lines + 1] = ""
    lines[#lines + 1] = "#endif"
    return table.concat(lines, "\n")
end

return M
