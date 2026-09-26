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
M.Surface = M.ctx.Surface

local Ty = M.Ty
M.u32, M.u8, M.u16, M.i32 = Ty.u32, Ty.u8, Ty.u16, Ty.i32
M.u64, M.i64 = Ty.u64, Ty.i64
-- IEEE-754 double. It is a scalar like the integers, but it follows IEEE 754 rather than the
-- integer rules, so it is never an integer width and never wraps.
M.f64 = Ty.f64
M.bool, M.unit, M.type = Ty.bool, Ty.unit, Ty.type

function M.list(items) return ASDL.List(items) end


-- The integer widths this version has. An integer wraps at its own width, and a conversion that
-- changes width is checked. A signed integer is two's complement, so its range is the same width
-- shifted by half.
local WIDTHS = { [Ty.u8] = 8, [Ty.u16] = 16, [Ty.u32] = 32, [Ty.i32] = 32,
    [Ty.u64] = 64, [Ty.i64] = 64 }
-- A 64-bit bound is not a Lua number, so the bounds of every width are held as two words and the
-- exact kernel compares them. MAXIMA and MINIMA therefore only describe the widths that fit one.
local MAXIMA = { [Ty.u8] = 255, [Ty.u16] = 65535, [Ty.u32] = 4294967295, [Ty.i32] = 2147483647 }
local MINIMA = { [Ty.i32] = -2147483648 }
local SIGNED = { [Ty.i32] = true, [Ty.i64] = true }
-- The arithmetic and comparison operators accept an integer or a float, but one operation still
-- needs one type on both sides; only a literal adopts the other side's type.

-- Intrinsic predicates on the interned type (structure.md §2.4). Each reads only `self`, so each is
-- safe on a shared node, and each call site reads as the question it asks. A fold that carries a
-- `seen`/`visiting` set is contextual state, not an intrinsic question, so `runtime`,
-- `representable`, `hasNamed`, `embedsCell` and `reachesCell` stay free functions below.
--
-- `Ty.V` is a sum, so one implementation on the parent answers for every variant: the ten scalars
-- are one value each, and every other variant carries the constructor name it was built with. The
-- first write of a key to the parent is raw-set onto every member (ASDL.md), which is why nothing
-- here has a per-variant arm.
function Ty.V:isInteger() return WIDTHS[self] ~= nil end
function Ty.V:isWide() return WIDTHS[self] == 64 end
function Ty.V:isSigned() return SIGNED[self] == true end
function Ty.V:isF64() return self == Ty.f64 end
function Ty.V:isBool() return self == Ty.bool end
function Ty.V:isUnit() return self == Ty.unit end

-- The schema is the discriminant: `self.kind` is the constructor name the sum assigned, so one kind
-- test answers for every variant that has no field to inspect (structure.md §0.1).
function Ty.V:isRecord() return self.kind == "Record" end
function Ty.V:isSig() return self.kind == "Sig" end
function Ty.V:isSum() return self.kind == "Sum" end
function Ty.V:isTagged() return self.kind == "Tagged" end
function Ty.V:isTaggedType() return self.kind == "Sum" or self.kind == "Tagged" end
function Ty.V:isRef() return self.kind == "ref" end
function Ty.V:isPtr() return self.kind == "ptr" end
function Ty.V:isArray() return self.kind == "array" end
function Ty.V:isSlice() return self.kind == "slice" end
function Ty.V:isNamed() return self.kind == "Named" end
function Ty.V:isOwned() return self.kind == "Owned" end
function Ty.V:isView() return self.kind == "View" end
-- ref | ptr | slice: a representation that stops, so what it reaches through is not embedded. A
-- predicate over three variants, not a fourth variant (structure.md §0.1).
function Ty.V:isIndirection()
    return self.kind == "ref" or self.kind == "ptr" or self.kind == "slice"
end

-- The byte slice: text and bytes are one mechanism rather than two, so they are one type.
function Ty.V:isString() return self == M.string end

-- The width facts the predicates and the fences ask about, by identity.
function M.widthOf(t) return WIDTHS[t] end
function M.maxOf(t) return MAXIMA[t] end
function M.minOf(t) return MINIMA[t] or 0 end
function M.modulusOf(t) return 2 ^ WIDTHS[t] end

-- The largest and smallest value of an integer type as a pair of words, so that "does this value
-- fit" is one comparison in the exact kernel for every width. A signed type sign extends its bounds.
function M.maxWordsOf(t)
    if t:isWide() then
        if t:isSigned() then return 2147483647, 4294967295 end
        return 4294967295, 4294967295
    end
    return 0, M.maxOf(t)
end

function M.minWordsOf(t)
    if t:isWide() then
        if t:isSigned() then return 2147483648, 0 end
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
    if a:isSigned() ~= b:isSigned() then return nil end
    if wa == wb then return a end
    return wa > wb and a or b
end

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
    if type(t) ~= "table" or not t:isRecord() then return nil end
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
    return Ty.Owned(key, visible, environment or Ty.unit)
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


-- A sum and a tagged callable are both a tag plus one of several payloads, so the tag operations
-- and the three IR statements that manipulate them are shared.

function M.alternatives(t)
    if type(t) ~= "table" then return nil end
    if t:isTagged() then return t.arms end
    if t:isSum() then return t.cases end
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
function M.ref(target) return Ty.ref(target) end

-- A raw pointer is an address with no lifetime attached. It has the same C representation as a
-- reference and none of the same guarantee, which is why it is a separate kind rather than a flag on
-- one: a signature that asks for `ptr(T)` is asking for an unchecked address.
function M.ptr(target) return Ty.ptr(target) end

-- An array is a fixed-length sequence of one element type. Its length is part of the type, so a
-- static index is checked while compiling and only a run-time index needs a bounds guard.
function M.array(element, length) return Ty.array(element, length) end

-- A slice is a runtime-length view of storage someone else owns: a pointer and a length. Its
-- length is not part of its type, which is what lets one word accept arrays of any extent. A
-- `string` is the byte slice, so text and bytes are one mechanism rather than two.
function M.slice(element) return Ty.slice(element) end
M.string = Ty.slice(Ty.u8)

-- A named cell is the identity a recursive type definition reserves for itself while its own layout
-- is still being computed. It may only appear as a reference target, so it is deliberately not a
-- record, a sum or anything else a value could be built from.
function M.named(cell) return Ty.Named(cell) end

-- Whether a named cell is reachable from `t`. `through` says whether the walk follows an
-- indirection: a reference, a pointer and a slice all point at storage that may be defined later,
-- so a layout that embeds one is finite, while a definition that is still open mentions one
-- wherever it appears. A signature and a view hold no storage of their own either way.
--
-- The visited set lives here rather than in the caller, which is why this is a free function and
-- not a method: `ASDL.md` keeps contextual state off an interned node.
local function mentionsCell(t, seen, through)
    -- A result slot that a signature requirement has yet to fix is `false`, which is not a type.
    if type(t) ~= "table" then return false end
    if t:isNamed() then return true end
    seen = seen or {}
    if seen[t] then return false end
    seen[t] = true
    if t:isIndirection() then
        if not through then return false end
        if t:isSlice() then return mentionsCell(t.element, seen, through) end
        return mentionsCell(t.target, seen, through)
    end
    if t:isSig() or t:isView() then return false end
    if t:isArray() then return mentionsCell(t.element, seen, through) end
    if t:isRecord() then
        for _, field in ipairs(t.fields) do
            if mentionsCell(field.type, seen, through) then return true end
        end
        return false
    end
    if t:isTaggedType() then
        for _, field in ipairs(M.alternatives(t)) do
            if mentionsCell(field.type, seen, through) then return true end
        end
        return false
    end
    if t:isOwned() then return mentionsCell(t.environment, seen, through) end
    return false
end

-- Whether a definition that mentions `t` is still open. A cell is what an open definition hands
-- back while its own layout is computed, so a type that mentions one cannot be judged as a value
-- type until the definition is sealed. A cell behind an indirection still counts: the definition
-- is not finished, whatever the storage does with it later.
function M.hasNamed(t)
    return mentionsCell(t, nil, true)
end

-- Whether a layout embeds a named cell by value, which no finite layout can: the walk stops at
-- every indirection, because what an address points at is not part of the layout holding it.
function M.embedsCell(t)
    return mentionsCell(t, nil, false)
end

-- Whether resolving named cells from `t` leads back to `cell`. A record, an array or a sum is a
-- layout, and a layout anchors the cycle, so only a nominal chain continues here: a name, or a
-- reference or pointer to one. A slice stops it for the same reason the walk above does.
function M.reachesCell(t, cell, cells)
    local seen = {}
    local current = t
    while true do
        if type(current) ~= "table" then return false end
        if current:isNamed() then
            if current.cell == cell then return true end
            if seen[current.cell] then return false end
            seen[current.cell] = true
            current = cells[current.cell]
        elseif current:isIndirection() and not current:isSlice() then
            current = current.target
        else
            return false
        end
    end
end

-- The runtime representation of a type: an Owned callable is represented by its environment. Any
-- value that is not a type is its own representation.
function M.environmentOf(t) return type(t) == "table" and t:isOwned() and t.environment or t end
function M.inValue(t) return Ty.InValue(t) end
function M.inPlace(t) return Ty.InPlace(t) end

-- Canonical textual encoding of a Ty/Ir descriptor; used for instance keys and caches.
function M.encode(value)
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
    -- Fieldless variants (u32, unit, Ir.Add, ...) carry only their constructor name.
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
    -- Only a type can have a runtime representation; a result slot a signature requirement has yet to
    -- fix is `false`.
    if type(t) ~= "table" then return false end
    if t:isInteger() or t == Ty.f64 or t == Ty.bool or t == Ty.unit then return true end
    if t == Ty.type then return false end
    if t:isRef() then
        -- A pointer is a runtime value whatever it points at; a named cell is always a data type
        -- that was sealed, so the target's own runtime-ness was checked when it was defined.
        return t.target:isNamed() or M.runtime(t.target, visiting)
    end
    if t:isPtr() then
        -- A pointer is a word of address whatever it points at, exactly as a reference is.
        return t.target:isNamed() or M.runtime(t.target, visiting)
    end
    if t:isArray() then
        if t.length < 1 then return false end
        return t.element:isNamed() or M.runtime(t.element, visiting)
    end
    if t:isSlice() then
        -- The element is reached through a pointer, so it needs a representation of its own. A
        -- slice of unit reaches no bytes at all, so it is not a value.
        if t.element == Ty.unit then return false end
        -- The element is reached through the pointer, so it needs a representation of its own.
        return t.element:isNamed() or M.runtime(t.element, visiting)
    end
    if t:isNamed() then
        -- A bare named cell must never reach a value position: it stands for a definition still
        -- being computed, and the definition decides. Rejecting it here keeps that invariant loud.
        return false
    end
    if t:isOwned() then return M.runtime(t.environment, visiting) end
    if t:isTaggedType() then
        -- A tag plus a payload whose size is the largest alternative.
        for _, field in ipairs(M.alternatives(t)) do
            if not M.runtime(field.type, visiting) then return false end
        end
        return true
    end
    if t:isView() then
        -- The runtime representation is an invocation pointer plus an environment pointer.
        for _, input in ipairs(t.visible.inputs) do
            if input.kind == "InValue" and not M.runtime(input.type, visiting) then return false end
        end
        for _, result in ipairs(t.visible.results) do
            if not M.runtime(result, visiting) then return false end
        end
        return true
    end
    if t:isSig() then
        -- A signature is a calling requirement, not a value; it only survives as a specialized
        -- Owned type once an argument fixes the code.
        return false
    end
    if t:isRecord() then
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
    if type(t) ~= "table" then return false end
    if t:isArray() then return M.runtime(t) end
    if t:isSlice() then return M.runtime(t) end
    if t:isRef() then return M.runtime(t) end
    if t:isPtr() then return M.runtime(t) end
    if t:isNamed() then return false end
    if t:isView() then return M.runtime(t) end
    if t:isTaggedType() then return M.runtime(t) end
    if t:isOwned() then
        if t.environment == Ty.unit then return M.runtime(M.view(t.visible)) end
        return M.runtime(t.environment)
    end
    return M.runtime(t)
end

-- A type as a diagnostic should show it. A record or a sum names its fields, which is what a source
-- signature names; everything else is already its own encoding.
function M.display(t)
    if type(t) ~= "table" then return M.encode(t) end
    if t:isRecord() then return "{" .. M.encodeFields(t.fields) .. "}" end
    if t:isSum() then return "oneof {" .. M.encodeFields(t.cases) .. "}" end
    if t:isPtr() then return "ptr(" .. M.display(t.target) .. ")" end
    if t:isRef() then return "ref(" .. M.display(t.target) .. ")" end
    return M.encode(t)
end

function M.checkRuntime(t, span)
    if not M.runtime(t) then
        D.reject("runtime-type", "A runtime value cannot have type " .. M.encode(t), span)
    end
    return t
end

return M
