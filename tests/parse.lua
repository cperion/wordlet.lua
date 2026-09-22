-- Parser and lexer conformance: constructs from syntax.md, plus the rejection cases it specifies.
local source = debug.getinfo(1, "S").source:sub(2)
package.path = (source:match("^(.*[/\\])") or "./") .. "../?.lua;"
    .. (source:match("^(.*[/\\])") or "./") .. "../?/init.lua;" .. package.path

local P = require("wordlet.parse")
local A = require("wordlet.ast")
local D = require("wordlet.diag")
local checks = 0

local function check(ok, message)
    assert(ok, message)
    checks = checks + 1
end

local function parses(text)
    return P.source(text, "t.let")
end

local function rejects(code, text)
    local ok, err = pcall(P.source, text, "t.let")
    check(not ok, "expected rejection: " .. text)
    check(D.is(err), "expected a diagnostic for: " .. text)
    check(err.code == code, ("expected code %s but got %s for: %s"):format(code, err.code, text))
    check(err.span ~= nil and err.span.line ~= nil, "rejection needs a spanned location")
    return err
end

local function dump(text)
    return A.shape(parses(text))
end

-- definitions, application, blocks -------------------------------------------
local program = parses("let affine(a, b, x: U32) : U32 = a * x + b\nreturn { functions = { affine } }")
check(#program.declarations == 1, "one declaration")
local word = program.declarations[1]
check(word.kind == "WordDecl" and word.def.name.text == "affine", "named definition")
check(#word.def.params == 3, "three parameters")
check(word.def.params[2].annotation.kind == "Reference", "shared annotation is applied to each name")
check(word.def.result.kind == "Single", "single result annotation")
check(word.def.body.kind == "Expression", "expression body")
check(#program.export.functions == 1 and program.export.functions[1].kind == "ExportName", "export name")

check(parses("let f(x: U32) = do return x end\nreturn { functions = {} }").declarations[1].def.body.kind == "Block",
    "block body")
check(#parses("let a = 1\nlet b = 2\nreturn { functions = {} }").declarations == 2, "multiple declarations")

-- partial application and calls ----------------------------------------------
local partial = parses("let affine(a, b, x: U32) = a * x + b\nlet t = affine(4, 3)\nreturn { functions = {} }")
check(partial.declarations[2].def.values[1].kind == "Apply", "partial application is an Apply")

-- multiple results ------------------------------------------------------------
local multi = parses("let divmod(a, b: U32) : (U32, U32) = do return a / b, a % b end\nreturn { functions = {} }")
check(multi.declarations[1].def.result.kind == "Many", "multiple result annotation")
check(multi.declarations[1].def.result.types and #multi.declarations[1].def.result.types == 2, "two result slots")
local ret = multi.declarations[1].def.body.statements[1]
check(ret.kind == "ReturnStmt" and #ret.values == 2, "two returned values")
check(#parses("let a, b = f(1)\nreturn { functions = {} }").declarations[1].def.binders == 2, "result-list binding")

-- lambdas and signatures ------------------------------------------------------
check(parses("let g = |x| -> x + 1\nreturn { functions = {} }").declarations[1].def.values[1].kind == "Lambda",
    "untyped lambda")
check(parses("let g = |a, b: U32| -> a + b\nreturn { functions = {} }").declarations[1].def.values[1].kind == "Lambda",
    "grouped lambda parameters")
check(parses("let g = || -> Unit()\nreturn { functions = {} }").declarations[1].def.values[1].kind == "Lambda",
    "empty lambda parameters")
local inner = parses("let g = |f: (U32): U32| -> f\nreturn { functions = {} }").declarations[1].def.values[1]
check(inner.kind == "Lambda" and inner.params[1].annotation.kind == "SignatureExpr",
    "a signature annotation inside pipes is not read as bitwise-or")
check(parses("let E = (U32): U32\nreturn { functions = {} }").declarations[1].def.values[1].kind == "SignatureExpr",
    "a parenthesized input list with a result makes a signature")
check(parses("let E = (U32, U32) : U32\nreturn { functions = {} }").declarations[1].def.values[1].kind == "SignatureExpr",
    "parenthesized signature inputs")
check(parses("let E = () : U32\nreturn { functions = {} }").declarations[1].def.values[1].kind == "SignatureExpr",
    "empty signature inputs")
check(parses("let E = (U32) : U32\nreturn { functions = {} }").declarations[1].def.values[1].kind == "SignatureExpr",
    "one-element parenthesized input list")
check(parses("let E = (U32): ((U32): U32)\nreturn { functions = {} }").declarations[1].def.values[1].kind
    == "SignatureExpr", "a parenthesized input list nests as a callable result")
-- `->` introduces a lambda body only; `::` is gone; signature inputs must be parenthesized.
rejects("parse", "let f(x: U32) -> U32 = x\nreturn { functions = { f } }")
rejects("parse", "let C = { v: U32, get() -> U32 = v }\nreturn { types = { C } }")
rejects("parse", "let f(x: U32) :: U32 = x\nreturn { functions = { f } }")
rejects("parse", "let E = U32 :: U32\nreturn { functions = {} }")
rejects("parse", "let E = U32: U32\nreturn { functions = {} }")
-- A `:` after a name is an annotation, so a signature needs its inputs parenthesized.
check(parses("let g: (U32): U32 = |x| -> x + 1\nreturn { functions = {} }")
    .declarations[1].def.binders[1].annotation.kind == "SignatureExpr",
    "a binding annotation may be a signature")
check(parses("let f(x: U32): (U32): U32 = |y: U32| -> y\nreturn { functions = { f } }")
    .declarations[1].def.result.kind == "Single", "a result may itself be a signature")
local grouped = parses("let x = (1 + 2) * 3\nreturn { functions = {} }").declarations[1].def.values[1]
check(grouped.kind == "BinaryExpr" and grouped.left.kind == "BinaryExpr", "parenthesized expression groups")

-- records, schemas, methods ---------------------------------------------------
local schema = parses("let Counter = { value: U32, inc() : U32 = do value += 1 return value end, }\nreturn { types = { Counter } }")
local members = schema.declarations[1].def.values[1].members
check(#members == 2 and members[1].kind == "FieldMember" and members[2].kind == "MethodMember",
    "schema members; trailing comma accepted")
check(parses("let r = Counter { value = 3 }\nreturn { functions = {} }").declarations[1].def.values[1].kind == "RecordSupply",
    "keyed supply")
check(parses("let r = Counter { }\nreturn { functions = {} }").declarations[1].def.values[1].kind == "RecordSupply",
    "empty keyed supply")
check(parses("let E = {}\nreturn { types = { E } }").declarations[1].def.values[1].kind == "SchemaExpr", "empty schema")
check(parses("let y = r.value\nreturn { functions = {} }").declarations[1].def.values[1].kind == "FieldSelect",
    "field selection")

-- statements ------------------------------------------------------------------
local stmts = parses([[
let f(x: U32) : U32 = do
  let a = x + 1
  let b = a
  counter.total += b
  g(a)
  if a == 0 then return 0 end
  if b != 0 then return b else return a end
  return a
end
return { functions = { f } }
]]).declarations[1].def.body.statements
check(stmts[1].kind == "ValueStmt" and stmts[3].kind == "StoreStmt" and stmts[3].operator == "+=", "value and compound store")
check(stmts[4].kind == "CallStmt", "call statement")
check(stmts[5].kind == "IfStmt" and #stmts[5].no == 0, "statement if without else")
check(stmts[6].kind == "IfStmt" and #stmts[6].no == 1, "statement if with else")
check(stmts[6].yes[1].kind == "ReturnStmt" and stmts[6].yes[1].values[1].kind == "Reference", "return in an arm")

-- local word definitions in a block -------------------------------------------
local localWord = parses([[
let outer(x: U32) : U32 = do
  let inner(y: U32) : U32 = y + 1
  return inner(x)
end
return { functions = { outer } }
]]).declarations[1].def.body.statements[1]
check(localWord.kind == "WordStmt", "a local named word is a WordStmt")

-- operators and precedence ----------------------------------------------------
local expr = function(text) return parses("let v = " .. text .. "\nreturn { functions = {} }").declarations[1].def.values[1] end
check(expr("-x ^ 2").kind == "UnaryExpr" and expr("-x ^ 2").operand.kind == "BinaryExpr", "-x ^ 2 is -(x ^ 2)")
check(expr("x ^ -1").kind == "BinaryExpr" and expr("x ^ -1").right.kind == "UnaryExpr", "x ^ -1 allows unary on the right")
check(expr("a + b * c").right.kind == "BinaryExpr", "* binds tighter than +")
check(expr("a << b + c").kind == "BinaryExpr" and expr("a << b + c").left.kind == "Reference", "shift is looser than +")
check(expr("a & b | c").kind == "BinaryExpr" and expr("a & b | c").left.kind == "BinaryExpr", "| is looser than &")
check(expr("a == b").kind == "BinaryExpr" and expr("a or b and c").left.kind == "Reference", "and binds tighter than or")
check(expr("x ~ (x << 13)").right.kind == "BinaryExpr", "xor with shift")
check(expr("a != b").operator == "!=", "!= is inequality")

-- exports ---------------------------------------------------------------------
local export = parses("let f(x: U32) = x\nreturn { functions = { f, g = f }, types = { T = f }, results = { [f] = U32 } }").export
check(#export.functions == 2 and export.functions[2].kind == "ExportAlias", "export alias")
check(#export.types == 1 and #export.results == 1, "type and result sections")
check(parses("let f(x: U32) = x\nreturn { functions = { f }, }").export ~= nil, "trailing comma between sections")

-- comments, whitespace, one-line equivalence ----------------------------------
check(#parses("-- only a comment\nlet f(x: U32) = x -- trailing\nreturn { functions = { f } }").declarations == 1,
    "comments are ignored")
local oneLine = "let f(x: U32) : U32 = do let y = x + 1 return y end return { functions = { f } }"
check(dump(oneLine) == dump([[
let f(x: U32) : U32 = do
  let y = x + 1
  return y
end
return { functions = { f } }
]]), "one-line and multi-line forms parse identically")

-- rejections per syntax.md ----------------------------------------------------
rejects("parse", "let f(x: U32) = x")
rejects("parse", "let f(x: U32) = 1 < x < 2\nreturn { functions = {} }")
rejects("parse", "let f(x: U32) = do x + 1 return x end\nreturn { functions = {} }")
rejects("parse", "return { widgets = {} }")
rejects("parse", "let f(x: U32, y) = x\nreturn { functions = {} }")
-- A literal above 64 bits is refused, while one that only exceeds a word is a 64-bit literal.
rejects("lex-range", "let x = 18446744073709551616\nreturn { functions = {} }")
check(#P.source("let x = 4294967296\nreturn { functions = {} }", "t.let").declarations == 1,
    "a literal above a word is a 64-bit literal")
rejects("lex-char", "let x = $\nreturn { functions = {} }")
rejects("parse", "let f(x: U32) = x\nreturn { functions = { f }\n")

-- examples parse -----------------------------------------------------------------
for _, example in ipairs({ "arithmetic", "receivers", "captures", "sums", "tagged", "references", "arrays", "modules", "modules_util" }) do
    local path = (source:match("^(.*[/\\])") or "./") .. "../examples/" .. example .. ".let"
    local file = assert(io.open(path, "rb"))
    local text = assert(file:read("*a"))
    assert(file:close())
    local parsed, err = pcall(P.source, text, example .. ".let")
    check(parsed, "example must parse: " .. example .. " (" .. tostring(err) .. ")")
    local tokenStream = require("wordlet.lex").tokens(text, example .. ".let")
    check(tokenStream[#tokenStream].kind == "eof", "token stream is terminated")
end

print(("PASS: lexer/parser (%d checks)"):format(checks))
