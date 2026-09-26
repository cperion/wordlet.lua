-- Schema checks for ast.asdl / ir.asdl. Loaded by tests/run.lua from the project root.
local A = require("vendor.asdl")
local L = A.List
local root = (debug.getinfo(1, "S").source:sub(2):match("^(.*[/\\])") or "./") .. "../"

local function context(file)
    local c = A.NewContext()
    local f = assert(io.open(root .. file, "rb"))
    c:Define(assert(f:read("*a")))
    assert(f:close())
    return c
end

-- ast.asdl parses and constructs, and every variant carries its span as an attribute.
local a = context("ast.asdl")
local span = a.Ast.Span("app.let", 1, 0, 5)
local literal = a.Ast.U32Literal(7, span)
assert(a.Ast.Expr:isclassof(literal) and literal.kind == "U32Literal")
assert(literal.span.start == 0 and literal.span.line == 1 and literal.span.file == "app.let")
local program = a.Ast.Program(L{}, a.Ast.Export(L{}, L{}, L{}))
assert(program.export.results ~= nil and #program.declarations == 0)

-- ir.asdl parses and constructs. Structural types intern; occurrences do not.
local i = context("ir.asdl")
local record = i.Ty.Record("Counter", L{i.Ty.Field("value", i.Ty.u32)})
assert(record == i.Ty.Record("Counter", L{i.Ty.Field("value", i.Ty.u32)}))
assert(record ~= i.Ty.Record("Other", L{i.Ty.Field("value", i.Ty.u32)}))
-- Source interfaces are separate from the interned data layout. Two schemas with that same
-- record type can carry distinct method sets, and indirections retain only a face descriptor.
local one, two = i.Surface.Schema(1), i.Surface.Schema(2)
assert(one == i.Surface.Schema(1) and one ~= two)
assert(i.Surface.Element(one) == i.Surface.Element(i.Surface.Schema(1)))
assert(i.Surface.Element(one) ~= i.Surface.Element(two))
assert(i.Surface.Knot("cell") == i.Surface.Knot("cell"))
assert(i.Ir.Value(1) ~= i.Ir.Value(1) and i.Ir.Storage(1) ~= i.Ir.Storage(1))
assert(i.Ir.Const(i.Ty.u32, i.Ir.UInt(3)) ~= i.Ir.Const(i.Ty.u32, i.Ir.UInt(3)))

-- A place parameter and a value parameter both build an Ir.Fn; Input distinguishes value from place.
local place_param = i.Ir.PlaceParam(0, i.Ir.Storage(1), record)
local fn = i.Ir.Fn("wordletfn_1", i.Ir.Body, 1,
    L{i.Ty.InPlace(record), i.Ty.InValue(i.Ty.u32)}, L{i.Ty.u32},
    L{place_param, i.Ir.ValueParam(1, i.Ir.Value(1), i.Ty.u32)},
    L{i.Ir.Return(L{i.Ir.Ref(i.Ir.Value(1), i.Ty.u32)})})
assert(fn.role.kind == "Body" and fn.hidden == 1 and fn.params[1].input == 0)
assert(i.Ir.Fn.kind == nil and i.Ir.ValueParam.kind == "ValueParam")
assert(not pcall(i.Ir.Fn, "bad", i.Ir.Body, 0, L{i.Ty.u32}, L{}, L{}, L{}))

print("PASS: ast.asdl/ir.asdl parse and construct; spans, interning and occurrences behave")
