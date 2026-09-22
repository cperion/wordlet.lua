-- Lowering a closed artifact to C11. Header and source are two views of the same layouts.
local S = require("wordlet.schema")
local D = require("wordlet.diag")
local M = {}

local Ir = S.Ir
local U64Kernel = require("wordletkit.u64")

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

local collectExprs, collectPlaceExprs

-- The `Expr` operands of an expression. A place can carry an index expression, so `Addr` and a
-- place's `Index` are followed here too.
function collectPlaceExprs(place, out)
    if not place then return end
    local kind = place.kind
    if kind == "Project" or kind == "Deref" then collectPlaceExprs(place.base, out)
    elseif kind == "Index" then collectPlaceExprs(place.base, out); out[#out + 1] = place.index end
end

function collectExprs(expr, out)
    local kind = expr.kind
    if kind == "Un" then out[#out + 1] = expr.operand
    elseif kind == "Bin" then out[#out + 1] = expr.left; out[#out + 1] = expr.right
    elseif kind == "Get" then out[#out + 1] = expr.aggregate
    elseif kind == "Make" then for _, field in ipairs(expr.fields) do out[#out + 1] = field end
    elseif kind == "Owned" then out[#out + 1] = expr.environment
    elseif kind == "Convert" then out[#out + 1] = expr.operand
    elseif kind == "Addr" then collectPlaceExprs(expr.place, out)
    end
end

-- A shift amount that is a compile-time constant below the width needs no run-time range guard.
local function shiftInRange(expr, width)
    if expr.kind ~= "Const" then return false end
    local literal = expr.literal
    return literal.kind == "UInt" and literal.value < width
end

local Emitter = {}
Emitter.__index = Emitter
local function newEmitter(layouts, signature, usedStorages, plan)
    return setmetatable({ layouts = layouts, lines = {}, indent = 1,
        placeParams = (signature and signature.placeParams) or {},
        usedStorages = usedStorages or {},
        shared = plan and plan.shared or nil,
        decls = plan and plan.decls or nil,
        assigned = {}, nextTemp = 0 }, Emitter)
end
function Emitter:line(text) self.lines[#self.lines + 1] = string.rep("    ", self.indent) .. text end
function Emitter:raw(text) self.lines[#self.lines + 1] = text end
function Emitter:value(id) return "v" .. id end
function Emitter:storage(id) return "s" .. id end

-- A shared expression is declared once and referenced by name; every other expression renders inline.
function Emitter:expr(expr)
    local name = self.assigned and self.assigned[expr]
    if name then return name end
    return self:render(expr)
end

function Emitter:tempName()
    self.nextTemp = self.nextTemp + 1
    return "e" .. self.nextTemp
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
            local text = U64Kernel.tostring(expr.literal.high, expr.literal.low, S.isSigned(expr.type))
            if S.isSigned(expr.type) then return "INT64_C(" .. text .. ")" end
            return "UINT64_C(" .. text .. ")"
        end
        if expr.literal.kind == "UInt" then
            if S.isSigned(expr.type) then return "INT32_C(" .. expr.literal.value .. ")" end
            return "UINT32_C(" .. expr.literal.value .. ")"
        end
        if expr.literal.kind == "Boolean" then return expr.literal.value and "true" or "false" end
        D.bug("c-literal", "Unknown literal")
    elseif kind == "Ref" then
        return self:value(expr.value.id)
    elseif kind == "Un" then
        local op = expr.op.kind
        if op == "Not" then return "(!(" .. self:expr(expr.operand) .. "))" end
        local operand = self:expr(expr.operand)
        if S.isSigned(expr.type) then
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
            if S.isSigned(expr.type) then
                return "wordlet_i32(wordlet_pow(wordlet_u32(" .. left .. "), " .. right .. "))"
            end
            if resultType == "uint32_t" then return "wordlet_pow(" .. left .. ", " .. right .. ")" end
            return "(" .. resultType .. ")wordlet_pow(" .. left .. ", " .. right .. ")"
        end
        local cOp = BINARY_OP[op]
        if not cOp then D.bug("c-op", "No C operator for " .. tostring(op)) end
        local resultType = self.layouts:cType(expr.type)
        if S.isWide(expr.type) then
            -- A signed 64-bit operation reinterprets the bit pattern of its operands.
            if S.isSigned(expr.type) then
                self.layouts.usesi64 = true
                self.layouts.usesu64 = true
            end
            if op == "Div" then
                if S.isSigned(expr.type) then self.layouts.usesdiv = true end
                if S.isSigned(expr.type) then return "wordlet_div_i64(" .. left .. ", " .. right .. ")" end
                return "(" .. left .. " / " .. right .. ")"
            end
            if op == "Rem" then
                if S.isSigned(expr.type) then
                    self.layouts.usesrem = true
                    return "wordlet_rem_i64(" .. left .. ", " .. right .. ")"
                end
                return "(" .. left .. " % " .. right .. ")"
            end
            if op == "Pow" then
                self.layouts.usespow = true
                if S.isSigned(expr.type) then
                    return "wordlet_i64(wordlet_pow64(wordlet_u64(" .. left .. "), wordlet_u64("
                        .. right .. ")))"
                end
                return "wordlet_pow64(" .. left .. ", " .. right .. ")"
            end
            if S.isSigned(expr.type) then
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
        if op == "Div" and S.isSigned(expr.type) then
            return "wordlet_div_i32(" .. left .. ", " .. right .. ")"
        end
        if op == "Rem" and S.isSigned(expr.type) then
            return "wordlet_rem_i32(" .. left .. ", " .. right .. ")"
        end
        if S.isSigned(expr.type) then
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
        return "((" .. left .. ") " .. cOp .. " (" .. right .. "))"
    elseif kind == "Make" and S.isArray(S.environmentOf(expr.type)) then
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
        if S.isSigned(from) ~= S.isSigned(to) and S.widthOf(from) == S.widthOf(to) then
            if S.isWide(to) then
                if S.isSigned(to) then
                    self.layouts.usesi64 = true
                    return "wordlet_i64(" .. operand .. ")"
                end
                self.layouts.usesu64 = true
                return "wordlet_u64(" .. operand .. ")"
            end
            if S.isSigned(to) then return "wordlet_i32(" .. operand .. ")" end
            return "wordlet_u32(" .. operand .. ")"
        end
        return "(" .. self.layouts:cType(to) .. ")(" .. self.layouts:cType(from) .. ")(" .. operand .. ")"
    elseif kind == "Addr" then
        -- The address of a place: a root plus field names, with no load.
        return "&(" .. self:placeC(expr.place) .. ")"
    end
    D.todo("c-expr", "No C lowering for expression " .. tostring(kind))
end

function Emitter:placeC(place)
    if place.kind == "Local" then
        local module = self.layouts.modules and self.layouts.modules[place.storage]
        if module then return module.name end
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
        -- An aggregate without an initialiser still needs valid storage, because a branch that
        -- assigns it is not guaranteed to run. A scalar takes a zero initialiser; an aggregate
        -- is zeroed with an explicit memset rather than `= {0}`, which GCC's
        -- -Wmaybe-uninitialized misreads when a union-bearing aggregate is later assigned from
        -- a temporary.
        if S.isInteger(ty) or ty == S.Bool then
            self:line(cType .. " " .. name .. " = " .. (S.isInteger(ty) and "0" or "false") .. ";")
        else
            self:line(cType .. " " .. name .. ";")
            self:line("memset(&" .. name .. ", 0, sizeof " .. name .. ");")
        end
    end
end

function Emitter:statements(list)
    for index, stmt in ipairs(list) do
        -- Shared expressions are declared at the innermost list that contains all their uses,
        -- immediately before the first statement that needs them.
        local pending = self.decls and self.decls[list] and self.decls[list][index]
        if pending then
            for _, node in ipairs(pending) do self:declareShared(node) end
        end
        local kind = stmt.kind
        if kind == "Let" then
            self:declare(stmt.type, self:value(stmt.value.id), self:expr(stmt.expr))
        elseif kind == "Var" then
            -- A loop-carried Var is declared before its Loop, but a specialization's base case may
            -- never read or store it. An initializer is a pure Expr, so dropping an unreferenced
            -- Var is safe and keeps the emitted C free of unused locals.
            if self.usedStorages[stmt.storage.id] then
                self:declare(stmt.type, self:storage(stmt.storage.id), stmt.initial and self:expr(stmt.initial))
            end
        elseif kind == "Read" then
            self:declare(stmt.type, self:value(stmt.value.id), self:placeC(stmt.place))
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
        elseif kind == "Loop" then
            self:line("for (;;) {")
            self.indent = self.indent + 1
            self:statements(stmt.body)
            self.indent = self.indent - 1
            self:line("}")
        elseif kind == "Next" then
            self:line("continue;")
        elseif kind == "Trap" then
            self:line("if (" .. self:expr(stmt.failure) .. ") abort();")
        elseif kind == "ConstructVariant" then
            self:construct(stmt)
        elseif kind == "VariantMatches" then
            local tag = S.tagIndex(stmt.sum, stmt.tag)
            self:declare(S.Bool, self:value(stmt.value.id),
                "(" .. self:value(stmt.variant.id) .. ".wordlet_tag == " .. tag .. ")")
        elseif kind == "VariantPayload" then
            local case = S.caseOf(stmt.sum, stmt.tag)
            local cased = self.layouts.tagLayout(stmt.sum).cases[S.tagIndex(stmt.sum, stmt.tag) + 1]
            self:declare(case, self:value(stmt.value.id),
                "(" .. self:value(stmt.variant.id) .. ".payload." .. cased.name .. ")")
        elseif kind == "Call" then
            self:call(stmt)
        elseif kind == "Indirect" then
            self:indirect(stmt)
        elseif kind == "View" then
            self:makeView(stmt)
        elseif kind == "Return" then
            self:line(self:returnText(stmt.values))
        else
            D.todo("c-stmt", "No C lowering for statement " .. tostring(kind))
        end
    end
end

-- A variant is a compound literal with the tag and the one payload member set by name.
function Emitter:construct(stmt)
    local layout = self.layouts.tagLayout(stmt.type)
    local cased = layout.cases[S.tagIndex(stmt.type, stmt.tag) + 1]
    local text = "(" .. layout.name .. "){ .wordlet_tag = " .. cased.tag
    if stmt.payload then
        text = text .. ", .payload." .. cased.name .. " = " .. self:expr(stmt.payload)
    end
    self:declare(stmt.type, self:value(stmt.value.id), text .. " }")
end

function Emitter:call(stmt)
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
    if #stmt.results == 0 then
        self:line(call .. ";")
    elseif #stmt.results == 1 then
        self:declare(types[1], self:value(stmt.results[1].id), call)
        self:line("(void)" .. self:value(stmt.results[1].id) .. ";")
    else
        local layout = self.layouts.resultLayout(types)
        if not layout.name then D.bug("c-results", "Multiple results need a tuple layout") end
        -- The call produces one aggregate temporary; each logical result becomes its own value.
        local packed = "t" .. stmt.results[1].id
        self:line(layout.name .. " " .. packed .. " = " .. call .. ";")
        for index = 1, #stmt.results do
            self:declare(types[index], self:value(stmt.results[index].id), packed .. ".f_" .. index)
        end
        -- A discarded call still must not leave an unused local behind under -Werror.
        self:line("(void)" .. packed .. ";")
        for index = 1, #stmt.results do self:line("(void)" .. self:value(stmt.results[index].id) .. ";") end
    end
end

-- The adapter that lets a known callable be invoked through a view.
function M.adapterBodies(layouts)
    local lines = {}
    for _, adapter in ipairs(layouts.adapterOrder or {}) do
        local signature = layouts.signatures[adapter.entry]
        if not signature then D.bug("c-adapter", "Adapter target " .. adapter.entry .. " has no signature") end
        local returns = signature.results.kind == "void" and "void"
            or (signature.results.kind == "scalar" and layouts:cType(signature.results.type)
                or signature.results.name)
        local visible, calls = {}, {}
        for index = #adapter.bound + 1, #signature.params do
            local param = signature.params[index]
            local name = "a" .. (index - #adapter.bound)
            visible[#visible + 1] = layouts:cType(param.type) .. (param.pointer and " *" or " ") .. name
            calls[#calls + 1] = name
        end
        for _, field in ipairs(adapter.bound) do calls[#calls + 1] = "env->" .. field.name end
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
    if not S.isView(types) then D.bug("c-view", "Indirect needs a view-typed callable") end
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
        self:line(layout.results.name .. " t" .. stmt.results[1].id .. " = " .. call .. ";")
        for index = 1, #stmt.results do
            self:declare(layout.results.fields[index].type, self:value(stmt.results[index].id),
                "t" .. stmt.results[1].id .. ".f_" .. index)
        end
    end
end

-- Binds a callable's hidden inputs in a local adapter and takes its address.
function Emitter:makeView(stmt)
    local types = stmt.type
    -- Either an erased callable view, or pure code: an owned callable with an empty environment.
    if not S.isView(types) and not (S.isOwned(types) and S.environmentOf(types) == S.Unit) then
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
        self:line(layout.name .. " " .. value .. " = { .invoke = " .. adapter.fn
            .. ", .environment = NULL };")
        return
    end
    local adapterName = "a" .. stmt.value.id
    local fields = {}
    for index, field in ipairs(adapter.bound) do
        fields[#fields + 1] = "." .. field.name .. " = " .. args[index]
    end
    self:line(adapter.name .. " " .. adapterName .. " = {" .. table.concat(fields, ", ") .. "};")
    self:line(layout.name .. " " .. value .. " = { .invoke = " .. adapter.fn
        .. ", .environment = &" .. adapterName .. " };")
end

function Emitter:returnText(values)
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
    for _, layout in ipairs(layouts.tupleOrder) do forward(layout.name) end
    for _, layout in ipairs(layouts.recordOrder) do forward(layout.name) end
    for _, layout in ipairs(layouts.arrayOrder) do forward(layout.name) end
    for _, layout in ipairs(layouts.sumOrder) do forward(layout.name) end
    for _, layout in ipairs(layouts.taggedOrder) do forward(layout.name) end
    for _, layout in ipairs(layouts.viewOrder) do forward(layout.name) end
    for _, layout in ipairs(layouts.adapterOrder or {}) do forward(layout.name) end

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
            lines[#lines + 1] = "typedef struct " .. layout.name .. " {\n"
                .. table.concat(body, "\n") .. "\n} " .. layout.name .. ";"
        end)
        -- Needs are recorded by name and resolved when emitting, because discovery order does not
        -- decide definition order.
        for _, field in ipairs(fields) do
            if field.type ~= S.Unit then entry.needs[#entry.needs + 1] = layouts:cType(field.type) end
        end
        return entry
    end

    for _, layout in ipairs(layouts.tupleOrder) do
        defineAggregate(layout, layout.fields, false)
    end
    for _, layout in ipairs(layouts.recordOrder) do
        defineAggregate(layout, layout.fields, false)
    end
    for _, layout in ipairs(layouts.arrayOrder) do
        -- An array is a struct holding one C array, because a bare C array cannot be assigned or
        -- returned by value while a struct that contains one can. The element is embedded, so its
        -- layout is a completeness need.
        define(layout, { layouts:cType(layout.element) }, function()
            lines[#lines + 1] = "typedef struct " .. layout.name .. " {\n    "
                .. layouts:cType(layout.element) .. " f_data[" .. tostring(layout.length)
                .. "];\n} " .. layout.name .. ";"
        end)
    end
    for _, layout in ipairs(layouts.sumOrder) do
        defineAggregate(layout, layout.cases, true)
    end
    for _, layout in ipairs(layouts.taggedOrder) do
        defineAggregate(layout, layout.cases, true)
    end
    -- A view mentions its visible parameter and result types in its function pointer, so those must
    -- be complete first. An adapter holds its by-value slots by value; a borrowed slot is a pointer.
    local function defineView(layout)
        local entry
        entry = define(layout, {}, function()
            lines[#lines + 1] = "typedef struct " .. layout.name .. " {\n    "
                .. layout.returns .. " (*invoke)" .. layout.invoke .. ";"
                .. "\n    const void *environment;\n} " .. layout.name .. ";"
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
    for _, layout in ipairs(layouts.viewOrder) do defineView(layout) end
    for _, adapter in ipairs(layouts.adapterOrder or {}) do
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
            lines[#lines + 1] = "typedef struct " .. adapter.name .. " {\n"
                .. table.concat(fields, "\n") .. "\n} " .. adapter.name .. ";"
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

    local emitted = {}
    local remaining = #order
    while remaining > 0 do
        local progressed = false
        for _, entry in ipairs(order) do
            if not emitted[entry.name] then
                local ready = true
                for _, need in ipairs(entry.needs) do
                    -- A name that defines no aggregate is a scalar type spelled directly in C.
                    if definitions[need] and not emitted[need] then ready = false break end
                end
                if ready then
                    entry.emit()
                    emitted[entry.name] = true
                    remaining = remaining - 1
                    progressed = true
                end
            end
        end
        if not progressed then
            local stuck = {}
            for _, entry in ipairs(order) do
                if not emitted[entry.name] then stuck[#stuck + 1] = entry.name end
            end
            D.todo("c-order", "These types contain each other by value: " .. table.concat(stuck, ", "))
        end
    end
    for _, exported in ipairs(layouts.typeExports or {}) do
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
    return returns .. " " .. signature.name .. "(" .. table.concat(parameters, ", ") .. ")"
end

local function aliasOf(signature, name)
    local copy = {}
    for key, value in pairs(signature) do copy[key] = value end
    copy.name = name
    return copy
end

function M.prototypes(layouts)
    local lines = M.moduleDeclarations(layouts)
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
    -- The 32-bit power helper is only emitted when a body actually uses `^`.
    if not layouts.usespow32 then return {} end
    return {
        "uint32_t wordlet_pow(uint32_t base, uint32_t exponent) {",
        "    uint32_t result = UINT32_C(1);",
        "    while (exponent > UINT32_C(0)) {",
        "        if ((exponent & UINT32_C(1)) != UINT32_C(0)) {",
        "            result = (uint32_t)((uint64_t)result * (uint64_t)base);",
        "        }",
        "        exponent = exponent >> 1;",
        "        if (exponent > UINT32_C(0)) {",
        "            base = (uint32_t)((uint64_t)base * (uint64_t)base);",
        "        }",
        "    }",
        "    return result;",
        "}",
    }
end

-- The storage IDs a function actually references through a place. A loop-carried `Var` is declared
-- before its `Loop`, but a specialization whose base case returns immediately may never read or
-- store it; since an initializer is a pure `Expr`, such a `Var` is dead.
local function usedStorages(fn)
    local used = {}
    local place, expr
    local function arg(value)
        if value.kind == "ValueArg" then expr(value.value)
        elseif value.kind == "BorrowArg" then place(value.place) end
    end
    local function arguments(list)
        for _, value in ipairs(list) do arg(value) end
    end
    local function statements(list)
        for _, stmt in ipairs(list) do
            local kind = stmt.kind
            if kind == "Let" then expr(stmt.expr)
            elseif kind == "Var" then expr(stmt.initial)
            elseif kind == "Read" then place(stmt.place)
            elseif kind == "Store" then place(stmt.place) expr(stmt.value)
            elseif kind == "BundleDef" or kind == "View" then arguments(stmt.slots)
            elseif kind == "Call" then arguments(stmt.arguments)
            elseif kind == "Indirect" then expr(stmt.callable) arguments(stmt.arguments)
            elseif kind == "If" then expr(stmt.test) statements(stmt.yes) statements(stmt.no)
            elseif kind == "Loop" then statements(stmt.body)
            elseif kind == "Trap" then expr(stmt.failure)
            elseif kind == "ConstructVariant" then expr(stmt.payload)
            elseif kind == "Return" then for _, value in ipairs(stmt.values) do expr(value) end
            end
        end
    end
    function place(value)
        if not value then return end
        if value.kind == "Local" then used[value.storage.id] = true
        elseif value.kind == "Project" or value.kind == "Deref" then place(value.base)
        elseif value.kind == "Index" then place(value.base) expr(value.index) end
    end
    function expr(value)
        if not value then return end
        local kind = value.kind
        if kind == "Un" then expr(value.operand)
        elseif kind == "Bin" then expr(value.left) expr(value.right)
        elseif kind == "Get" then expr(value.aggregate)
        elseif kind == "Make" then for _, field in ipairs(value.fields) do expr(field) end
        elseif kind == "Owned" then expr(value.environment)
        elseif kind == "Convert" then expr(value.operand)
        elseif kind == "Addr" then place(value.place)
        end
    end
    statements(fn.body)
    return used
end

-- The IR is a DAG: `Builder:intern` unifies structurally equal expressions, so one node can be
-- referenced many times, and `Emitter:render` is a tree walk that would print every reference. This
-- finds the nodes used more than once and the innermost statement list containing all of their
-- uses, so the emitter can bind each to one local and print names instead.
local function analyzeSharing(fn)
    local seen, nodes, edges, roots = {}, {}, {}, {}
    local paths, pathList, chains = {}, {}, {}

    local function chainOf(path)
        local chain = chains[path]
        if chain then return chain end
        local reversed = {}
        local current = path
        while current do reversed[#reversed + 1] = current; current = current.parent end
        chain = {}
        for index = #reversed, 1, -1 do chain[#chain + 1] = reversed[index] end
        chains[path] = chain
        return chain
    end

    local function collect(expr)
        if not expr or seen[expr] then return end
        seen[expr] = true
        nodes[#nodes + 1] = expr
        local children = {}
        collectExprs(expr, children)
        local list, position = {}, {}
        for _, child in ipairs(children) do
            if not position[child] then
                position[child] = #list + 1
                list[#list + 1] = { node = child, count = 0 }
            end
            list[position[child]].count = list[position[child]].count + 1
        end
        edges[expr] = list
        for _, edge in ipairs(list) do collect(edge.node) end
    end

    local function statementExprs(stmt, out)
        local kind = stmt.kind
        local function arg(value)
            if value.kind == "ValueArg" then out[#out + 1] = value.value
            elseif value.kind == "BorrowArg" then collectPlaceExprs(value.place, out) end
        end
        if kind == "Let" then out[#out + 1] = stmt.expr
        elseif kind == "Var" then out[#out + 1] = stmt.initial
        elseif kind == "Read" then collectPlaceExprs(stmt.place, out)
        elseif kind == "Store" then collectPlaceExprs(stmt.place, out); out[#out + 1] = stmt.value
        elseif kind == "BundleDef" or kind == "View" then for _, value in ipairs(stmt.slots) do arg(value) end
        elseif kind == "Call" then for _, value in ipairs(stmt.arguments) do arg(value) end
        elseif kind == "Indirect" then
            out[#out + 1] = stmt.callable
            for _, value in ipairs(stmt.arguments) do arg(value) end
        elseif kind == "If" then out[#out + 1] = stmt.test
        elseif kind == "Trap" then out[#out + 1] = stmt.failure
        elseif kind == "ConstructVariant" then out[#out + 1] = stmt.payload
        elseif kind == "Return" then for _, value in ipairs(stmt.values) do out[#out + 1] = value end
        end
    end

    local stack = {}
    local function walkList(list)
        for index, stmt in ipairs(list) do
            local path = { list = list, index = index, parent = stack[#stack] }
            stack[#stack + 1] = path
            local exprs = {}
            statementExprs(stmt, exprs)
            for _, expr in ipairs(exprs) do
                if expr then
                    collect(expr)
                    roots[#roots + 1] = { node = expr, path = path }
                end
            end
            if stmt.kind == "If" then walkList(stmt.yes); walkList(stmt.no)
            elseif stmt.kind == "Loop" then walkList(stmt.body) end
            stack[#stack] = nil
        end
    end
    walkList(fn.body)

    -- Reference counts and use positions propagate from the statement roots through the DAG, so the
    -- walk is linear in the DAG and never expands the shared tree.
    local order, marked = {}, {}
    local function orderVisit(node)
        if marked[node] then return end
        marked[node] = true
        for _, edge in ipairs(edges[node]) do orderVisit(edge.node) end
        order[#order + 1] = node
    end
    for _, root in ipairs(roots) do orderVisit(root.node) end

    local uses = {}
    for _, root in ipairs(roots) do
        uses[root.node] = math.min(2, (uses[root.node] or 0) + 1)
        if not paths[root.node] then paths[root.node] = {}; pathList[root.node] = {} end
        if not paths[root.node][root.path] then
            paths[root.node][root.path] = true
            pathList[root.node][#pathList[root.node] + 1] = root.path
        end
    end
    for index = #order, 1, -1 do
        local node = order[index]
        local count = uses[node] or 0
        if count > 0 then
            for _, edge in ipairs(edges[node]) do
                local child = edge.node
                uses[child] = math.min(2, (uses[child] or 0) + count * edge.count)
                if pathList[node] then
                    if not paths[child] then paths[child] = {}; pathList[child] = {} end
                    for _, path in ipairs(pathList[node]) do
                        if not paths[child][path] then
                            paths[child][path] = true
                            pathList[child][#pathList[child] + 1] = path
                        end
                    end
                end
            end
        end
    end

    -- A node used twice or more is shared; its declaration goes in the innermost list that contains
    -- every use, before the earliest statement in that list that uses it.
    local shared, decls = {}, {}
    for _, node in ipairs(nodes) do
        if uses[node] and uses[node] >= 2 and node.kind ~= "Const" and node.kind ~= "Ref" then
            shared[node] = true
            local list = pathList[node]
            local first = chainOf(list[1])
            local depth = #first
            for _, path in ipairs(list) do
                local chain = chainOf(path)
                local matched = 0
                while matched < depth and matched < #chain
                    and chain[matched + 1].list == first[matched + 1].list do
                    matched = matched + 1
                end
                if matched < depth then depth = matched end
            end
            local target = first[depth].list
            local earliest = first[depth].index
            for _, path in ipairs(list) do
                local index = chainOf(path)[depth].index
                if index < earliest then earliest = index end
            end
            decls[target] = decls[target] or {}
            decls[target][earliest] = decls[target][earliest] or {}
            local pending = decls[target][earliest]
            pending[#pending + 1] = node
        end
    end
    return { shared = shared, decls = decls }
end

function M.bodies(layouts)
    local lines = {}
    for _, instance in ipairs(layouts.order) do
        local signature = layouts.signatures[instance.target]
        local emitter = newEmitter(layouts, signature, usedStorages(instance.fn),
            analyzeSharing(instance.fn))
        emitter:raw(M.signatureText(layouts, signature) .. " {")
        emitter:statements(instance.fn.body)
        -- A residual base case keeps the full ABI, so a parameter it never reads still appears in
        -- the signature. Mark such a parameter used for `-Wunused-parameter`.
        local referenced = {}
        for index = 2, #emitter.lines do
            for name in emitter.lines[index]:gmatch("[%a_][%w_]*") do referenced[name] = true end
        end
        for _, param in ipairs(signature.params) do
            if param.name and not referenced[param.name] then emitter:line("(void)" .. param.name .. ";") end
        end
        emitter:raw("}")
        lines[#lines + 1] = table.concat(emitter.lines, "\n")
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

local INCLUDES = { "#include <stdint.h>", "#include <stdbool.h>", "#include <stdlib.h>", "#include <string.h>" }

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
    for _, module in ipairs(layouts.moduleOrder or {}) do
        lines[#lines + 1] = "static " .. layouts:cType(module.type) .. " " .. module.name .. ";"
    end
    return lines
end

-- Bodies are emitted first: doing so is what registers the views, adapters and nested record
-- layouts that the declarations have to name.
function M.unit(layouts)
    -- Bodies and declarations are built first: naming a type is what decides whether the signed
    -- helpers are needed, and they have to be printed before anything that uses them.
    local bodies = M.bodies(layouts)
    local adapters = M.adapterBodies(layouts)
    local declarations = M.typeDeclarations(layouts)
    local lines = {}
    for _, line in ipairs(INCLUDES) do lines[#lines + 1] = line end
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
    for _, line in ipairs(declarations) do lines[#lines + 1] = line end
    lines[#lines + 1] = ""
    for _, line in ipairs(M.prototypes(layouts)) do lines[#lines + 1] = line end
    lines[#lines + 1] = ""
    for _, line in ipairs(M.prelude(layouts)) do lines[#lines + 1] = line end
    lines[#lines + 1] = ""
    for _, line in ipairs(adapters) do
        lines[#lines + 1] = line
        lines[#lines + 1] = ""
    end
    for _, body in ipairs(bodies) do
        lines[#lines + 1] = body
        lines[#lines + 1] = ""
    end
    return table.concat(lines, "\n")
end

function M.source(layouts, headerName)
    -- The signed helpers are decided by naming types, so build the bodies and declarations first.
    local bodies = M.bodies(layouts)
    local adapters = M.adapterBodies(layouts)
    local declarations = M.typeDeclarations(layouts)
    local lines = {}
    if headerName then lines[#lines + 1] = '#include "' .. headerName .. '"' end
    for _, line in ipairs(INCLUDES) do lines[#lines + 1] = line end
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
    for _, line in ipairs(declarations) do lines[#lines + 1] = line end
    lines[#lines + 1] = ""
    for _, line in ipairs(M.prototypes(layouts)) do lines[#lines + 1] = line end
    lines[#lines + 1] = ""
    for _, line in ipairs(M.prelude(layouts)) do lines[#lines + 1] = line end
    lines[#lines + 1] = ""
    for _, line in ipairs(adapters) do
        lines[#lines + 1] = line
        lines[#lines + 1] = ""
    end
    for _, body in ipairs(bodies) do
        lines[#lines + 1] = body
        lines[#lines + 1] = ""
    end
    return table.concat(lines, "\n")
end

function M.header(layouts, name)
    -- The header is a view of the same closed artifact, so bodies must have been emitted for the
    -- type closure to be complete.
    M.bodies(layouts)
    local guard = "WORDLET_" .. M.escape(name or "unit"):upper() .. "_H"
    local lines = { "#ifndef " .. guard, "#define " .. guard, "", "#include <stdint.h>", "#include <stdbool.h>", "" }
    for _, line in ipairs(M.typeDeclarations(layouts)) do lines[#lines + 1] = line end
    lines[#lines + 1] = ""
    lines[#lines + 1] = "#ifdef __cplusplus"
    lines[#lines + 1] = 'extern "C" {'
    lines[#lines + 1] = "#endif"
    lines[#lines + 1] = ""
    local any = false
    for _, instance in ipairs(layouts.order) do
        local signature = layouts.signatures[instance.target]
        if signature.name:sub(1, 8) == "wordlet_" then
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
