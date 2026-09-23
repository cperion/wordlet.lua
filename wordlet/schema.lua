-- Runtime type descriptors (Ty) over ir.asdl. Structural interning is the ASDL context's job;
-- canonical ordering and validation are ours.
local ASDL = require("vendor.asdl")
local D = require("wordlet.diag")
local M = {}

M.ASDL = ASDL
M.List = ASDL.List
M.ctx = ASDL.NewContext()
M.ctx:Define(require("wordlet.schema.ir"))
M.Ty = M.ctx.Ty
M.Ir = M.ctx.Ir

local Ty = M.Ty
M.U32, M.U8, M.U16, M.I32 = Ty.U32, Ty.U8, Ty.U16, Ty.I32
M.U64, M.I64 = Ty.U64, Ty.I64
-- IEEE-754 double. It is a scalar like the integers, but it follows IEEE 754 rather than the
-- integer rules, so it is never an integer width and never wraps.
M.F64 = Ty.F64
M.Bool, M.Unit, M.Type = Ty.Bool, Ty.Unit, Ty.Type

function M.list(items) return ASDL.List(items) end

function M.isU32(t) return t == Ty.U32 end
function M.isU8(t) return t == Ty.U8 end
function M.isU16(t) return t == Ty.U16 end

-- The integer widths this version has. An integer wraps at its own width, and a conversion that
-- changes width is checked. A signed integer is two's complement, so its range is the same width
-- shifted by half.
local WIDTHS = { [Ty.U8] = 8, [Ty.U16] = 16, [Ty.U32] = 32, [Ty.I32] = 32,
    [Ty.U64] = 64, [Ty.I64] = 64 }
-- A 64-bit bound is not a Lua number, so the bounds of every width are held as two words and the
-- exact kernel compares them. MAXIMA and MINIMA therefore only describe the widths that fit one.
local MAXIMA = { [Ty.U8] = 255, [Ty.U16] = 65535, [Ty.U32] = 4294967295, [Ty.I32] = 2147483647 }
local MINIMA = { [Ty.I32] = -2147483648 }
local SIGNED = { [Ty.I32] = true, [Ty.I64] = true }
function M.isInteger(t) return WIDTHS[t] ~= nil end
function M.isF64(t) return t == Ty.F64 end
-- What the arithmetic and comparison operators accept. A float and an integer are both numbers, but
-- an operation still needs one type on both sides; only a literal adopts the other side's type.
function M.isNumeric(t) return WIDTHS[t] ~= nil or t == Ty.F64 end
function M.widthOf(t) return WIDTHS[t] end
function M.isWide(t) return WIDTHS[t] == 64 end
function M.maxOf(t) return MAXIMA[t] end
function M.minOf(t) return MINIMA[t] or 0 end
function M.isSigned(t) return SIGNED[t] == true end
function M.modulusOf(t) return 2 ^ WIDTHS[t] end

-- The largest and smallest value of an integer type as a pair of words, so that "does this value
-- fit" is one comparison in the exact kernel for every width. A signed type sign extends its bounds.
function M.maxWordsOf(t)
    if M.isWide(t) then
        if M.isSigned(t) then return 2147483647, 4294967295 end
        return 4294967295, 4294967295
    end
    return 0, M.maxOf(t)
end

function M.minWordsOf(t)
    if M.isWide(t) then
        if M.isSigned(t) then return 2147483648, 0 end
        return 0, 0
    end
    local minimum = M.minOf(t)
    if minimum < 0 then return 4294967295, minimum + 4294967296 end
    return 0, 0
end

-- A wider integer of the same signedness holds every value of a narrower one. Changing signedness
-- reinterprets the bits at one width and is checked when the width changes, so it is never implicit.
function M.widerThan(a, b)
    local wa, wb = WIDTHS[a], WIDTHS[b]
    if not wa or not wb then return nil end
    if M.isSigned(a) ~= M.isSigned(b) then return nil end
    if wa == wb then return a end
    return wa > wb and a or b
end
function M.isBool(t) return t == Ty.Bool end
function M.isUnit(t) return t == Ty.Unit end
function M.isType(t) return t == Ty.Type end
function M.isRecord(t) return type(t) == "table" and t.kind == "Record" end
function M.isSig(t) return type(t) == "table" and t.kind == "Sig" end

-- A record type is the runtime data layout: methods and static supplies live in the source
-- definition, never in Ty. Fields are canonicalised by name.
function M.record(fields)
    local names = {}
    for name in pairs(fields) do names[#names + 1] = name end
    table.sort(names)
    local list = {}
    for _, name in ipairs(names) do list[#list + 1] = Ty.Field(name, fields[name]) end
    local meaning = M.encodeFields(list)
    return Ty.Record(meaning, ASDL.List(list))
end

function M.encodeFields(fields)
    local parts = {}
    for _, field in ipairs(fields) do
        parts[#parts + 1] = field.name .. ":" .. M.encode(field.type)
    end
    return table.concat(parts, ",")
end

function M.fieldsOf(t)
    local map = {}
    for _, field in ipairs(t.fields) do map[field.name] = field.type end
    return map
end

function M.field(t, name)
    if not M.isRecord(t) then return nil end
    for _, field in ipairs(t.fields) do if field.name == name then return field.type end end
end

function M.fieldNames(t)
    local names = {}
    for _, field in ipairs(t.fields) do names[#names + 1] = field.name end
    return names
end

function M.sig(inputs, results)
    return Ty.Sig(ASDL.List(inputs), ASDL.List(results))
end

-- A concrete executable value: `key` names the compiled lambda instance whose environment this
-- value carries. The code identity lives in the type, so an IR value of this type is callable.
function M.owned(key, visible, environment)
    return Ty.Owned(key, visible, environment or Ty.Unit)
end
function M.view(sig) return Ty.View(sig) end

-- A sum type: an unordered set of named alternatives, exactly like a record's fields but read as
-- a tag plus a payload.
function M.sum(cases)
    local names = {}
    for name in pairs(cases) do names[#names + 1] = name end
    table.sort(names)
    local list = {}
    for _, name in ipairs(names) do list[#list + 1] = Ty.Field(name, cases[name]) end
    return Ty.Sum(M.encodeFields(list), ASDL.List(list))
end

function M.isSum(t) return type(t) == "table" and t.kind == "Sum" end

-- A tagged callable is a closed set of code identities that share one visible signature. Each arm
-- names an entry and holds that entry's environment type; the tag selects which code a call runs.
function M.tagged(visible, arms)
    local names = {}
    for name in pairs(arms) do names[#names + 1] = name end
    table.sort(names)
    local list = {}
    for _, name in ipairs(names) do list[#list + 1] = Ty.Field(name, arms[name]) end
    return Ty.Tagged(visible, ASDL.List(list))
end

function M.isTagged(t) return type(t) == "table" and t.kind == "Tagged" end

-- A sum and a tagged callable are both a tag plus one of several payloads, so the tag operations
-- and the three IR statements that manipulate them are shared.
function M.isTaggedType(t) return M.isSum(t) or M.isTagged(t) end

function M.alternatives(t)
    if M.isTagged(t) then return t.arms end
    if M.isSum(t) then return t.cases end
    return nil
end

-- The alternative names, in the canonical order that fixes the tag numbering.
function M.casesOf(t)
    local names = {}
    for _, field in ipairs(M.alternatives(t) or {}) do names[#names + 1] = field.name end
    return names
end

function M.caseOf(t, name)
    for _, field in ipairs(M.alternatives(t) or {}) do
        if field.name == name then return field.type end
    end
end

function M.tagIndex(t, name)
    for index, field in ipairs(M.alternatives(t) or {}) do
        if field.name == name then return index - 1 end
    end
end
-- A reference is a checked borrow of a place: its representation is a pointer, its meaning is the
-- lifetime rule in section 8.2 of the syntax contract.
function M.ref(target) return Ty.Ref(target) end
function M.isRef(t) return type(t) == "table" and t.kind == "Ref" end

-- A raw pointer is an address with no lifetime attached. It has the same C representation as a
-- reference and none of the same guarantee, which is why it is a separate kind rather than a flag on
-- one: a signature that asks for `Ptr(T)` is asking for an unchecked address.
function M.ptr(target) return Ty.Ptr(target) end
function M.isPtr(t) return type(t) == "table" and t.kind == "Ptr" end

-- An array is a fixed-length sequence of one element type. Its length is part of the type, so a
-- static index is checked while compiling and only a run-time index needs a bounds guard.
function M.array(element, length) return Ty.Array(element, length) end
function M.isArray(t) return type(t) == "table" and t.kind == "Array" end

-- A slice is a runtime-length view of storage someone else owns: a pointer and a length. Its
-- length is not part of its type, which is what lets one word accept arrays of any extent. A
-- `String` is the byte slice, so text and bytes are one mechanism rather than two.
function M.slice(element) return Ty.Slice(element) end
function M.isSlice(t) return type(t) == "table" and t.kind == "Slice" end
M.String = Ty.Slice(Ty.U8)
function M.isString(t) return t == M.String end

-- A named cell is the identity a recursive type definition reserves for itself while its own layout
-- is still being computed. It may only appear as a reference target, so it is deliberately not a
-- record, a sum or anything else a value could be built from.
function M.named(cell) return Ty.Named(cell) end
function M.isNamed(t) return type(t) == "table" and t.kind == "Named" end

-- Whether a type still mentions a named cell anywhere inside it. A cell is what an open definition
-- hands back while its own layout is computed, so a type that mentions one is not finished yet: it
-- cannot be judged as a value type until the definition is sealed, and the cycle checker is what
-- judges it then. A record that holds one by value is a by-value cycle in progress.
function M.hasNamed(t, seen)
    if M.isNamed(t) then return true end
    seen = seen or {}
    if seen[t] then return false end
    seen[t] = true
    if M.isRef(t) or M.isPtr(t) then return M.hasNamed(t.target, seen) end
    if M.isSlice(t) then return M.hasNamed(t.element, seen) end
    if M.isArray(t) then return M.hasNamed(t.element, seen) end
    if M.isRecord(t) then
        for _, field in ipairs(t.fields) do
            if M.hasNamed(field.type, seen) then return true end
        end
        return false
    end
    if M.isTaggedType(t) then
        for _, field in ipairs(M.alternatives(t)) do
            if M.hasNamed(field.type, seen) then return true end
        end
        return false
    end
    if M.isOwned(t) then return M.hasNamed(t.environment, seen) end
    return false
end

function M.isOwned(t) return type(t) == "table" and t.kind == "Owned" end
-- The runtime representation of a type: an Owned callable is represented by its environment.
function M.environmentOf(t) return M.isOwned(t) and t.environment or t end
function M.isView(t) return type(t) == "table" and t.kind == "View" end
function M.inValue(t) return Ty.InValue(t) end
function M.inPlace(t) return Ty.InPlace(t) end

-- Canonical textual encoding of a Ty/Ir descriptor; used for instance keys and caches.
function M.encode(value, seen)
    local tv = type(value)
    if tv == "number" then return "n" .. string.format("%.17g", value) end
    if tv == "string" then return "s" .. #value .. ":" .. value end
    if tv == "boolean" then return value and "T" or "F" end
    if tv ~= "table" then return tv end
    if getmetatable(value) == ASDL.List then
        local parts = {}
        for _, item in ipairs(value) do parts[#parts + 1] = M.encode(item) end
        return "[" .. table.concat(parts, ",") .. "]"
    end
    local mt = getmetatable(value)
    local name = value.kind or (mt and mt.__tostring and mt.__tostring(value)) or "?"
    local fields = mt and mt.__fields
    -- Fieldless variants (U32, Unit, Ir.Add, ...) carry only their constructor name.
    if not fields then return name end
    local parts = {}
    for _, field in ipairs(fields) do
        local item = value[field.name]
        parts[#parts + 1] = field.name .. "=" .. M.encode(item)
    end
    return name .. "(" .. table.concat(parts, ",") .. ")"
end

-- Validate that a type can appear as a runtime value type.
function M.runtime(t, visiting)
    if M.isInteger(t) or t == Ty.F64 or t == Ty.Bool or t == Ty.Unit then return true end
    if t == Ty.Type then return false end
    if M.isRef(t) then
        -- A pointer is a runtime value whatever it points at; a named cell is always a data type
        -- that was sealed, so the target's own runtime-ness was checked when it was defined.
        return M.isNamed(t.target) or M.runtime(t.target, visiting)
    end
    if M.isPtr(t) then
        -- A pointer is a word of address whatever it points at, exactly as a reference is.
        return M.isNamed(t.target) or M.runtime(t.target, visiting)
    end
    if M.isArray(t) then
        if t.length < 1 then return false end
        return M.isNamed(t.element) or M.runtime(t.element, visiting)
    end
    if M.isSlice(t) then
        -- The element is reached through a pointer, so it needs a representation of its own. A
        -- slice of Unit reaches no bytes at all, so it is not a value.
        if t.element == Ty.Unit then return false end
        -- The element is reached through the pointer, so it needs a representation of its own.
        return M.isNamed(t.element) or M.runtime(t.element, visiting)
    end
    if M.isNamed(t) then
        -- A bare named cell must never reach a value position: it stands for a definition still
        -- being computed, and the definition decides. Rejecting it here keeps that invariant loud.
        return false
    end
    if M.isOwned(t) then return M.runtime(t.environment, visiting) end
    if M.isTaggedType(t) then
        -- A tag plus a payload whose size is the largest alternative.
        for _, field in ipairs(M.alternatives(t)) do
            if not M.runtime(field.type, visiting) then return false end
        end
        return true
    end
    if M.isView(t) then
        -- The runtime representation is an invocation pointer plus an environment pointer.
        for _, input in ipairs(t.visible.inputs) do
            if input.kind == "InValue" and not M.runtime(input.type, visiting) then return false end
        end
        for _, result in ipairs(t.visible.results) do
            if not M.runtime(result, visiting) then return false end
        end
        return true
    end
    if M.isSig(t) then
        -- A signature is a calling requirement, not a value; it only survives as a specialized
        -- Owned type once an argument fixes the code.
        return false
    end
    if M.isRecord(t) then
        visiting = visiting or {}
        if visiting[t] then return false end
        visiting[t] = true
        for _, field in ipairs(t.fields) do
            if not M.runtime(field.type, visiting) then visiting[t] = nil; return false end
        end
        visiting[t] = nil
        return true
    end
    return false
end

-- A value that can actually appear in generated code. An owned callable with an empty environment is
-- pure code, and pure code already has a representation: the invocation pointer plus a null
-- environment that a view is, so it is representable as well.
function M.representable(t)
    if M.isArray(t) then return M.runtime(t) end
    if M.isSlice(t) then return M.runtime(t) end
    if M.isRef(t) then return M.runtime(t) end
    if M.isPtr(t) then return M.runtime(t) end
    if M.isNamed(t) then return false end
    if M.isView(t) then return M.runtime(t) end
    if M.isTaggedType(t) then return M.runtime(t) end
    if M.isOwned(t) then
        if t.environment == Ty.Unit then return M.runtime(M.view(t.visible)) end
        return M.runtime(t.environment)
    end
    return M.runtime(t)
end

-- A type as a diagnostic should show it. A record or a sum names its fields, which is what a source
-- signature names; everything else is already its own encoding.
function M.display(t)
    if M.isRecord(t) then return "{" .. M.encodeFields(t.fields) .. "}" end
    if M.isSum(t) then return "OneOf({" .. M.encodeFields(t.cases) .. "})" end
    if M.isPtr(t) then return "Ptr(" .. M.display(t.target) .. ")" end
    if M.isRef(t) then return "Ref(" .. M.display(t.target) .. ")" end
    return M.encode(t)
end

function M.checkRuntime(t, span)
    if not M.runtime(t) then
        D.reject("runtime-type", "A runtime value cannot have type " .. M.encode(t), span)
    end
    return t
end

return M
