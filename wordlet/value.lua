-- Values: concrete (u32/bool/unit/type/record), structural (schema/method) or residual (Ir.Expr,
-- a storage-backed object).
local S = require("wordlet.schema")
local D = require("wordlet.diag")
local M = {}

local V = {}
M.mt = V
V.__index = V

local function make(t) return setmetatable(t, V) end

-- An integer value of a given width. Its type says which width, so the arithmetic and the
-- conversions are decided by the type rather than by a separate kind.
function M.int(ty, n) return make{ tag = "int", ty = ty, n = n } end

-- A 64-bit integer, held as the two words of its value because a Lua number cannot hold it.
function M.int64(ty, high, low) return make{ tag = "int", ty = ty, high = high, low = low } end
function M.isWide(v) return v.tag == "int" and v.high ~= nil end
function M.u32(n) return M.int(S.U32, n) end
function M.u8(n) return M.int(S.U8, n) end
function M.u16(n) return M.int(S.U16, n) end
function M.isInteger(v) return v.tag == "int" end
function M.bool(b) return make{ tag = "bool", ty = S.Bool, b = b } end
-- An IEEE-754 double, held as a Lua number, which is one. Its type says which rules apply to it.
function M.float(ty, n) return make{ tag = "float", ty = ty, n = n } end
function M.f64(n) return M.float(S.F64, n) end
function M.unit() return make{ tag = "unit", ty = S.Unit } end
function M.type(ty) return make{ tag = "type", ty = S.Type, value = ty } end
-- `place` is the place the value was read from, when there is one: a reference read from storage
-- needs it to reach its target.
function M.ir(expr, ty, borrowed, place)
    return make{ tag = "ir", ty = ty, expr = expr, borrowed = borrowed, place = place }
end
function M.results(values) return make{ tag = "results", values = values } end
function M.word(def, args, span) return make{ tag = "word", def = def, args = args or {}, span = span } end

-- A concrete, immutable record: every field is a Value.
function M.record(ty, fields, schema) return make{ tag = "record", ty = ty, fields = fields, schema = schema } end

-- A schema: data fields, methods and any statically bound fields.
function M.schema(def) return make{ tag = "schema", def = def, ty = S.Type } end

-- A record instance in residual code. A record is mutable, so a place is what makes a store to a
-- field observable; but storage is only demanded when something actually needs an address. Until
-- then `expr` is the immutable `Make` the constructor built, and every read is a pure projection of
-- it, which is what keeps a constructor out of a storage round trip. Materialising clears `expr`,
-- because from then on the place is authoritative and a mutation must be visible to every read.
-- `enclosing` marks storage that belongs to an enclosing activation (a borrowed capture or a place
-- parameter) rather than to this one, which is what makes it a legal reference target.
function M.object(ty, place, schema, borrowed, enclosing, expr, body)
    return make{ tag = "object", ty = ty, place = place, schema = schema, borrowed = borrowed or false,
        enclosing = enclosing or false, expr = expr, body = body }
end

-- A reference: a checked borrow of the place it names. `tied` records that the target belongs to an
-- enclosing activation, so the reference cannot escape; a reference to module storage is untied.
-- `record`, when present, is the frontend record a module reference also names: normalize code reads
-- and writes that record directly, and residual code uses `place`.
function M.ref(ty, place, schema, tied, record)
    return make{ tag = "ref", ty = ty, place = place, schema = schema, tied = tied or false,
        record = record }
end

-- An array: a fixed-length sequence whose elements are values, with an optional place when it is
-- backed by storage. Like a record, a residual literal keeps its construction `Make` as `expr` and
-- spills to a place only when an element is addressed; `body` is the statement list that spill must
-- go into so it dominates every use.
function M.array(ty, items, place, borrowed, expr, body)
    return make{ tag = "array", ty = ty, items = items, place = place, borrowed = borrowed or false,
        expr = expr, body = body }
end

-- A string literal is a compile-time constant byte sequence. Its bytes are the bytes of the source
-- literal, and generated code keeps them in read-only static storage.
function M.string(ty, bytes) return make{ tag = "string", ty = ty, bytes = bytes } end

-- A slice: a runtime-length view of storage someone else owns. `source` is the container it views,
-- `start`/`count` the range, and `tied` records that the source belongs to an enclosing activation
-- rather than to module storage, so the view cannot escape that activation.
function M.slice(ty, source, start, count, tied)
    return make{ tag = "slice", ty = ty, source = source, start = start or 0, count = count,
        tied = tied or false }
end

-- A module namespace: the exported functions and types of a `use`d module, reached by member
-- selection. Its members are ordinary values, so no new call or supply rules are needed.
function M.namespace(module, members)
    return make{ tag = "namespace", ty = S.Type, module = module, members = members }
end

-- A constructor for one alternative of a sum type, named by member selection on the type.
function M.ctor(sum, case, caseType)
    return make{ tag = "ctor", ty = S.Type, sum = sum, case = case, caseType = caseType }
end

-- A sum value: which alternative it holds, and that alternative's payload.
function M.variant(ty, tag, payload, expr)
    return make{ tag = "variant", ty = ty, case = tag, payload = payload, expr = expr }
end

-- A method selected on an actual receiver.
function M.method(method, receiver) return make{ tag = "method", def = method, receiver = receiver } end

-- A concrete executable value: a lambda definition plus its captured bindings and any statically
-- supplied arguments.
function M.closure(plan, bound)
    return make{ tag = "closure", plan = plan, ty = plan.ty, bound = bound or {} }
end

function M.callable(t, code) return make{ tag = "callable", ty = t, code = code } end

function M.is(v) return getmetatable(v) == V end
function M.tag(v) return M.is(v) and v.tag or nil end
function M.isIr(v) return M.is(v) and v.tag == "ir" end

-- Fully concrete: every component is known, so a static invocation can be evaluated now.
function M.isKnown(v)
    if not M.is(v) then return false end
    local tag = v.tag
    if tag == "ir" or tag == "object" or tag == "schema" or tag == "callable"
        or tag == "namespace" then
        return false
    end
    -- A bound method is as known as the receiver it borrows.
    if tag == "method" then return M.isKnown(v.receiver) end
    if tag == "closure" then
        if #v.plan.runtimeOrder > 0 then return false end
        for _, capture in ipairs(v.plan.order) do
            local value = v.plan.static[capture]
            if value and not M.isKnown(value) then return false end
        end
        -- A borrowed capture is known when it names a record that is itself known: the code, the
        -- capture route and the receiver are then all facts of this compilation.
        for _, name in ipairs(v.plan.borrowedOrder or {}) do
            local borrowed = v.plan.borrowed[name]
            if not (borrowed and borrowed.record and M.isKnown(borrowed.record)) then return false end
        end
    end
    if tag == "record" then
        for _, field in pairs(v.fields) do if not M.isKnown(field) then return false end end
    end
    if tag == "string" then return true end
    if tag == "slice" then return M.isKnown(v.source) end
    if tag == "array" then
        if not v.items then return false end
        for _, item in ipairs(v.items) do if not M.isKnown(item) then return false end end
    end
    if tag == "variant" then return M.isKnown(v.payload) end
    return true
end

-- Usable as part of a specialization key. Mutable storage never qualifies: a record argument is
-- passed by value as a runtime input instead of becoming a compile-time constant.
function M.isStatic(v)
    if not M.is(v) then return false end
    local tag = v.tag
    -- A schema and a type are compile-time descriptions: capturing one is a static fact, not a
    -- runtime environment entry.
    if tag == "int" or tag == "float" or tag == "bool" or tag == "unit" or tag == "type" or tag == "schema"
        or tag == "namespace" then
        return true
    end
    if tag == "word" then
        for _, arg in ipairs(v.args) do if not M.isStatic(arg) then return false end end
        return true
    end
    -- A string is immutable bytes, so it is a static fact and a specialization key. A slice is a view
    -- of storage, so its identity is a borrow rather than a compile-time constant.
    if tag == "string" then return true end
    if tag == "slice" then return false end
    if tag == "array" then
        if not v.items then return false end
        for _, item in ipairs(v.items) do if not M.isStatic(item) then return false end end
        return true
    end
    if tag == "closure" then
        -- A closure with no runtime environment is pure code identity plus static facts.
        if #v.plan.runtimeOrder > 0 then return false end
        for _, capture in ipairs(v.plan.order) do
            if not M.isStatic(v.plan.static[capture]) then return false end
        end
        for _, arg in ipairs(v.bound) do if not M.isStatic(arg) then return false end end
        return true
    end
    return false
end

-- Canonical encoding for specialization keys. Returns nil when the value is not static.
function M.encode(v)
    if not M.is(v) then return S.encode(v) end
    local tag = v.tag
    if tag == "int" then
        if v.high then return S.encode(v.ty) .. ":" .. tostring(v.high) .. ":" .. tostring(v.low) end
        return S.encode(v.ty) .. ":" .. tostring(v.n)
    end
    if tag == "bool" then return "bool:" .. tostring(v.b) end
    -- Enough digits to round-trip, so two equal floats encode equally and unequal ones do not.
    if tag == "float" then return S.encode(v.ty) .. ":" .. string.format("%.17g", v.n) end
    if tag == "unit" then return "unit" end
    if tag == "type" then return "type:" .. S.encode(v.value) end
    if tag == "namespace" then return "namespace:" .. tostring(v.module) end
    if tag == "word" then
        local parts = { "word:" .. tostring(v.def.id) }
        for _, arg in ipairs(v.args) do
            local encoded = M.encode(arg)
            if not encoded then return nil end
            parts[#parts + 1] = encoded
        end
        return table.concat(parts, ",")
    end
    if tag == "string" then return "str:" .. tostring(#v.bytes) .. ":" .. v.bytes end
    if tag == "slice" then return nil end
    if tag == "array" then
        if not v.items then return nil end
        local parts = {}
        for index, item in ipairs(v.items) do
            local encoded = M.encode(item)
            if not encoded then return nil end
            parts[#parts + 1] = encoded
        end
        return "array:" .. S.encode(v.ty) .. "[" .. table.concat(parts, ",") .. "]"
    end
    if tag == "results" then
        local parts = {}
        for index, item in ipairs(v.values) do
            local encoded = M.encode(item)
            if not encoded then return nil end
            parts[index] = encoded
        end
        return "results:" .. table.concat(parts, ",")
    end
    if tag == "closure" then
        local parts = { "closure:" .. tostring(v.plan.def.id) }
        for _, arg in ipairs(v.bound) do
            local encoded = M.encode(arg)
            if not encoded then return nil end
            parts[#parts + 1] = "arg=" .. encoded
        end
        for _, name in ipairs(v.plan.order) do
            local static = v.plan.static[name]
            if static then
                local encoded = M.encode(static)
                if not encoded then return nil end
                parts[#parts + 1] = name .. "=" .. encoded
            else
                parts[#parts + 1] = name .. "=#"
            end
        end
        return table.concat(parts, ",")
    end
    return nil
end

function M.describe(v)
    if M.is(v) and v.tag == "float" then return string.format("%.17g", v.n) end
    if not M.is(v) then return tostring(v) end
    if v.tag == "type" then return "Type(" .. S.encode(v.value) .. ")" end
    if v.tag == "ir" then return "residual<" .. S.encode(v.ty) .. ">#" .. tostring(v.expr.kind) end
    if v.tag == "object" then return "object<" .. S.encode(v.ty) .. ">" end
    if v.tag == "record" then return "record<" .. S.encode(v.ty) .. ">" end
    if v.tag == "string" then return string.format("string<%d bytes>", #v.bytes) end
    if v.tag == "slice" then return "slice<" .. S.encode(v.ty) .. ">" end
    if v.tag == "array" then return "array<" .. S.encode(v.ty) .. ">" end
    if v.tag == "namespace" then return "namespace<" .. tostring(v.module) .. ">" end
    if v.tag == "schema" then return "schema<" .. tostring(v.def.name or v.def.id) .. ">" end
    if v.tag == "method" then return "method<" .. tostring(v.def.name) .. ">" end
    if v.tag == "closure" then return "closure<" .. tostring(v.plan.def.name) .. ">" end
    if v.tag == "results" then
        local parts = {}
        for index, item in ipairs(v.values) do parts[index] = M.describe(item) end
        return "(" .. table.concat(parts, ", ") .. ")"
    end
    return tostring(v.n ~= nil and v.n or v.b)
end

return M
