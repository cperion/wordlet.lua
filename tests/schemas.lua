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

local a = context("ast.asdl")
local span = a.Ast.Span("app.let", 1, 0, 5)
local literal = a.Ast.U32Literal(7, span)
assert(a.Ast.Expr:isclassof(literal) and literal.kind == "U32Literal")
assert(literal.span.start == 0 and literal.span.line == 1 and literal.span.file == "app.let") -- ASDL attributes carry spans
assert(a.Ast.Stmt.kind == nil) -- sums have .kind; this asserts the product/Sum distinction below
local program = a.Ast.Program(L{}, a.Ast.Export(L{}, L{}, L{}))
assert(program.export.results ~= nil and #program.declarations == 0)
-- Spans make singleton constructors into classes; they are no longer bare values.
assert(type(a.Ast.UnitLiteral) == "table" and a.Ast.UnitLiteral.kind == "UnitLiteral")

local i = context("ir.asdl")

-- Structural types intern; distinct meanings do not collide.
assert(i.Ty.Record("m", L{}) == i.Ty.Record("m", L{}))
assert(i.Ty.Record("m", L{}) ~= i.Ty.Record("n", L{}))
assert(i.Ty.Tuple(L{i.Ty.U32}) ~= i.Ty.Tuple(L{i.Ty.Bool}))
local sig = i.Ty.Sig(L{i.Ty.InValue(i.Ty.U32)}, L{i.Ty.U32})
assert(sig == i.Ty.Sig(L{i.Ty.InValue(i.Ty.U32)}, L{i.Ty.U32}))
assert(sig ~= i.Ty.Sig(L{i.Ty.InValue(i.Ty.Bool)}, L{i.Ty.U32}))
assert(i.Ty.Env(L{i.Ty.Saved(i.Ty.U32)}) ~= i.Ty.Env(L{i.Ty.Reference(i.Ty.U32)}))
assert(i.Ty.U32 == i.Ty.U32 and i.Ty.V:isclassof(i.Ty.U32) and i.Ty.V:isclassof(i.Ty.Unit))

-- A sum interns by its canonical alternative list, so two spellings of one sum are one type.
local sum = i.Ty.Sum("m", L{i.Ty.Field("circle", i.Ty.U32), i.Ty.Field("rect", i.Ty.Bool)})
assert(sum == i.Ty.Sum("m", L{i.Ty.Field("circle", i.Ty.U32), i.Ty.Field("rect", i.Ty.Bool)}))
assert(sum ~= i.Ty.Sum("m", L{i.Ty.Field("circle", i.Ty.U32)}))
assert(i.Ty.Sum:isclassof(sum) and i.Ty.V:isclassof(sum))

-- A tagged callable interns by its canonical arms too, and shares the tag operations with a sum.
local tagged = i.Ty.Tagged(sig, L{i.Ty.Field("closure:1", i.Ty.Unit),
    i.Ty.Field("closure:2", record or i.Ty.U32)})
assert(tagged == i.Ty.Tagged(sig, L{i.Ty.Field("closure:1", i.Ty.Unit),
    i.Ty.Field("closure:2", record or i.Ty.U32)}))
assert(tagged ~= i.Ty.Tagged(sig, L{i.Ty.Field("closure:1", i.Ty.Unit)}))
assert(i.Ty.Tagged:isclassof(tagged) and i.Ty.V:isclassof(tagged))

-- A reference interns by its target and a named cell by its identity, and neither subsumes the
-- other: a recursive definition is one knot, not two spellings of it.
local named = i.Ty.Named("Node#1")
assert(i.Ty.Ref(named) == i.Ty.Ref(i.Ty.Named("Node#1")))
assert(i.Ty.Ref(named) ~= i.Ty.Ref(i.Ty.U32))
assert(i.Ty.Named("Node#1") ~= i.Ty.Named("Node#2"))
assert(i.Ty.Ref:isclassof(i.Ty.Ref(named)) and i.Ty.V:isclassof(i.Ty.Ref(named)))
assert(i.Ty.Named:isclassof(named) and i.Ty.V:isclassof(named))

-- An address is a pure expression over a place, and a dereference is a place.
local refPlace = i.Ir.Local(i.Ir.Storage(1))
assert(i.Ir.Expr:isclassof(i.Ir.Addr(refPlace, i.Ty.Ref(named))))
assert(i.Ir.Place:isclassof(i.Ir.Deref(refPlace, named)))
assert(i.Ir.Addr(refPlace, i.Ty.Ref(named)) ~= i.Ir.Addr(refPlace, i.Ty.Ref(i.Ty.U32)))

-- An array interns by its element type and length, and its length is part of its identity.
local array = i.Ty.Array(i.Ty.U32, 3)
assert(array == i.Ty.Array(i.Ty.U32, 3) and array ~= i.Ty.Array(i.Ty.U32, 4))
assert(array ~= i.Ty.Array(i.Ty.Bool, 3) and i.Ty.Array:isclassof(array))
assert(i.Ir.Place:isclassof(i.Ir.Deref(i.Ir.Local(i.Ir.Storage(1)), named)))
assert(i.Ir.Place:isclassof(i.Ir.Index(i.Ir.Local(i.Ir.Storage(1)),
    i.Ir.Const(i.Ty.U32, i.Ir.UInt(0)), i.Ty.U32)))

-- Function-local ID descriptors are interned so equality is cheap.
assert(i.Ir.Value(1) == i.Ir.Value(1) and i.Ir.Storage(1) == i.Ir.Storage(1))
assert(i.Ir.Bundle(1) == i.Ir.Bundle(1) and i.Ir.Field("x") == i.Ir.Field("x"))
assert(i.Ir.Value(1) ~= i.Ir.Storage(1))

-- Ir.Expr is deliberately NOT interned by ASDL: Value IDs are function-local, so a global cache
-- would merge Ref(Value(1)) across functions. The builder interns per function instead.
local three = i.Ir.Const(i.Ty.U32, i.Ir.UInt(3))
assert(three ~= i.Ir.Const(i.Ty.U32, i.Ir.UInt(3)))
assert(i.Ir.Literal:isclassof(three.literal) and three.literal.kind == "UInt")

-- The three sum statements are occurrences too, and a Unit alternative has no payload expression.
local construct = i.Ir.ConstructVariant(i.Ir.Value(1), sum, "circle", three)
local unit_case = i.Ir.ConstructVariant(i.Ir.Value(2), sum, "none", nil)
assert(construct ~= i.Ir.ConstructVariant(i.Ir.Value(1), sum, "circle", three))
assert(unit_case.payload == nil)
assert(i.Ir.Stmt:isclassof(construct))
assert(i.Ir.Stmt:isclassof(i.Ir.VariantMatches(i.Ir.Value(3), i.Ir.Value(1), sum, "circle")))
assert(i.Ir.Stmt:isclassof(i.Ir.VariantPayload(i.Ir.Value(4), i.Ir.Value(1), sum, "circle")))

-- Statements are occurrences, never interned.
local call1 = i.Ir.Call(L{i.Ir.Value(1)}, "inc", L{i.Ir.ValueArg(three)})
local call2 = i.Ir.Call(L{i.Ir.Value(1)}, "inc", L{i.Ir.ValueArg(three)})
assert(call1 ~= call2 and i.Ir.Stmt:isclassof(call1) and i.Ir.Stmt:isclassof(i.Ir.Next))
assert(i.Ir.Binary:isclassof(i.Ir.Add) and i.Ir.Unary:isclassof(i.Ir.Neg))

-- Places unify value parameters and receiver roots through place params (no Receiver variant).
local record = i.Ty.Record("Counter", L{i.Ty.Field("value", i.Ty.U32)})
local place_param = i.Ir.PlaceParam(0, i.Ir.Storage(1), record)
local place = i.Ir.Project(i.Ir.Local(place_param.binding), i.Ir.Field("value"))
assert(i.Ir.Place:isclassof(place) and place.base.kind == "Local")
local env = i.Ty.Env(L{i.Ty.Saved(i.Ty.U32), i.Ty.Reference(record)})
local bundle = i.Ir.BundleDef(i.Ir.Bundle(1), env, L{i.Ir.ValueArg(three), i.Ir.BorrowArg(place)})
assert(bundle.env == env)
assert(i.Ir.Arg:isclassof(bundle.slots[1]) and i.Ir.Arg:isclassof(bundle.slots[2]))

-- Fn.inputs is Ty.Input* (value/place/bundle), not Ty.V*: the ASDL field check enforces this.
local fn = i.Ir.Fn("wordletfn_1", i.Ir.Body, 1,
    L{i.Ty.InPlace(record), i.Ty.InValue(i.Ty.U32)}, L{i.Ty.U32},
    L{place_param, i.Ir.ValueParam(1, i.Ir.Value(1), i.Ty.U32)},
    L{i.Ir.Return(L{i.Ir.Ref(i.Ir.Value(1), i.Ty.U32)})})
assert(fn.role.kind == "Body" and fn.hidden == 1 and fn.params[1].input == 0)
assert(i.Ir.Fn.kind == nil and i.Ir.ValueParam.kind == "ValueParam")
assert(not pcall(i.Ir.Fn, "bad", i.Ir.Body, 0, L{i.Ty.U32}, L{}, L{}, L{}))
assert(not pcall(i.Ty.Sig, L{i.Ty.U32}, L{}))

local out = i.Ir.Program(L{fn}, L{i.Ir.FunctionExport("inc", "wordlet_inc")}, L{i.Ir.TypeExport("Counter", record)})
assert(#out.functions == 1 and out.exports[1].target == "wordlet_inc" and out.types[1].name == "Counter")

print("PASS: ast.asdl/ir.asdl parse and construct; interning, spans, occurrences and cross-module refs behave")
