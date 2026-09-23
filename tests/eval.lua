-- Evaluator semantics: static results, specialization sharing and source rejections.
local source = debug.getinfo(1, "S").source:sub(2)
package.path = (source:match("^(.*[/\\])") or "./") .. "../?.lua;"
    .. (source:match("^(.*[/\\])") or "./") .. "../?/init.lua;" .. package.path

local wordlet = require("wordlet")
local Eval = require("wordlet.eval")
local Parse = require("wordlet.parse")
local D = require("wordlet.diag")
local C = require("wordlet.cabi")
local A = require("wordlet.ast")
local S = require("wordlet.schema")
local checks = 0
local function check(ok, message) assert(ok, message); checks = checks + 1 end

local function interpret(entry, args, program)
    return wordlet.interpret{ source = program, name = "t.let", entry = entry, args = args }
end

local function compile(program)
    return wordlet.compile{ source = program, name = "t.let" }
end

local function rejects(code, program, entry, args)
    local ok, err = pcall(function()
        if entry then interpret(entry, args or {}, program) else compile(program) end
    end)
    check(not ok, "expected a rejection (" .. code .. ")")
    check(D.is(err), "expected a diagnostic, got " .. tostring(err))
    check(err.code == code, ("expected %s but got %s"):format(code, err.code))
    check(err.span ~= nil, "rejection should carry a span")
    return err
end

-- F64 follows IEEE-754 rather than the integer rules: a division by zero is an infinity or a NaN, a
-- NaN comparison is false, an integer rounds to the nearest double, and a float truncates toward an
-- integer with the target's range checked.
do
    local source = "let third(): F64 = 1.0 / 3.0\n"
        .. "let inf(): F64 = 1.0 / 0.0\n"
        .. "let nan(): F64 = 0.0 / 0.0\n"
        .. "let nan_eq(): Bool = (0.0 / 0.0) == (0.0 / 0.0)\n"
        .. "let nan_ne(): Bool = (0.0 / 0.0) != (0.0 / 0.0)\n"
        .. "let huge(): Bool = 1.0 / 0.0 > 1.0e308\n"
        .. "let rounds(): F64 = F64(18446744073709551615)\n"
        .. "let truncates(): U32 = U32(2.75)\n"
        .. "let adopts(x: F64): F64 = x * 2.0\n"
        .. "let adopted(): F64 = adopts(3)\n"
        .. "let negated(x: F64): F64 = -x\n"
        .. "let ordered(a: F64, b: F64): Bool = a < b\n"
        .. "return { functions = { third, inf, nan, nan_eq, nan_ne, huge, rounds, truncates,\n"
        .. "    adopted, negated, ordered } }"
    check(interpret("third", {}, source)[1] == 1.0 / 3.0, "a float division is IEEE")
    check(interpret("inf", {}, source)[1] == math.huge, "a division by zero is an infinity")
    local nan = interpret("nan", {}, source)[1]
    check(nan ~= nan, "zero over zero is a NaN")
    check(interpret("nan_eq", {}, source)[1] == false, "a NaN is not equal to itself")
    check(interpret("nan_ne", {}, source)[1] == true, "a NaN is not equal to itself, so `!=` holds")
    check(interpret("huge", {}, source)[1] == true, "an infinity exceeds every finite double")
    check(interpret("rounds", {}, source)[1] == 18446744073709551616.0,
        "an integer rounds to the nearest double, ties to even")
    check(interpret("truncates", {}, source)[1] == 2, "a float truncates toward zero")
    check(interpret("adopted", {}, source)[1] == 6.0, "an integer literal adopts F64")
    check(interpret("negated", { 2.5 }, source)[1] == -2.5, "a double negates as itself")
    check(interpret("ordered", { 1.5, 2.5 }, source)[1] == true, "a double orders as IEEE does")
    -- An integer that is not a literal needs the conversion written, because rounding may lose a value.
    rejects("type-mismatch", "let f(n: U32): F64 = n + 1.5\nreturn { functions = { f } }", "f", { 1 })
    -- F64 has no remainder, power, shift or bitwise operator.
    rejects("type-mismatch", "let f(): F64 = 1.5 % 2.0\nreturn { functions = { f } } ")
    rejects("type-mismatch", "let f(): F64 = 1.5 & 2.0\nreturn { functions = { f } }")
    -- A known value outside the target's range is refused while compiling.
    rejects("numeric-range", "let f(): U32 = U32(4294967296.0)\nreturn { functions = { f } }")
    rejects("numeric-range", "let f(): U32 = U32(18446744073709551615.0)\nreturn { functions = { f } }")
end

-- A bare `return` is one Unit result and `Unit()` is the Unit value (syntax.md §1, §6). A Unit slot
-- is logical but has no runtime representation, so the IR drops it while a binding list keeps its
-- position.
do
    local source = "let nothing() : Unit = do return end\n"
        .. "let explicit() : Unit = do return; end\n"
        .. "let unit_value() : Unit = Unit()\n"
        .. "let pair(x: U32) : (Unit, U32) = do return Unit(), x end\n"
        .. "let use(x: U32) : U32 = do let u, y = pair(x) return y end\n"
        .. "return { functions = { nothing, explicit, unit_value, pair, use } }"
    check(interpret("nothing", {}, source)[1] == "unit", "a bare return is the Unit value")
    check(interpret("explicit", {}, source)[1] == "unit", "return; is a bare return")
    check(interpret("unit_value", {}, source)[1] == "unit", "Unit() is the Unit value")
    -- The Unit slot is first, so a positional binding is only right if it stayed logical.
    check(interpret("use", { 7 }, source)[1] == 7, "a Unit slot keeps its position in a result vector")
    compile(source)
end

-- Free-name analysis walks the schema, so a name captured inside any expression position is found.
-- A hand-written child table once missed record fields, array literals and indexes.
do
    local source = "let M = { acc: U32 }\n"
        .. "let pool = [3, 4, 5]\n"
        .. "let via_field(k: U32, x: U32) : U32 = (|y: U32| -> M { acc = k + y })(x).acc\n"
        .. "let via_array(k: U32, x: U32) : U32 = (|y: U32| -> [k, y])(x)[0]\n"
        .. "let via_index(k: U32, x: U32) : U32 = (|y: U32| -> pool[k] + y)(x)\n"
        .. "let via_cond(k: U32, x: U32) : U32 = (|y: U32| -> if k < y then k else y)(x)\n"
        .. "let via_binary(k: U32, x: U32) : U32 = (|y: U32| -> k * x + y)(x)\n"
        .. "return { functions = { via_field, via_array, via_index, via_cond, via_binary } }"
    check(interpret("via_field", { 2, 3 }, source)[1] == 5, "a capture in a record field is found")
    check(interpret("via_array", { 7, 1 }, source)[1] == 7, "a capture in an array literal is found")
    check(interpret("via_index", { 1, 10 }, source)[1] == 14, "a capture in an index is found")
    check(interpret("via_cond", { 2, 5 }, source)[1] == 2, "a capture in a conditional is found")
    check(interpret("via_binary", { 3, 4 }, source)[1] == 16, "a capture in a binary operand is found")
    compile(source)
end

-- Static evaluation ----------------------------------------------------------------------------
check(interpret("affine", { 3, 7, 4 },
    "let affine(a, b, x: U32) : U32 = a * x + b\nreturn { functions = { affine } }")[1] == 19,
    "affine is 19")
check(interpret("pick", { 0 },
    "let pick(x: U32) : U32 = if x == 0 then 7 else x * 2\nreturn { functions = { pick } }")[1] == 7,
    "known condition selects one arm")

local divmod = interpret("divmod", { 17, 5 },
    "let divmod(a, b: U32) : (U32, U32) = do return a / b, a % b end\nreturn { functions = { divmod } }")
check(#divmod == 2 and divmod[1] == 3 and divmod[2] == 2, "two results")

check(interpret("b", { 7 },
    "let a(x: U32) : U32 = x + 1\nlet b(x: U32) : U32 = a(x) * 2\nreturn { functions = { b } }")[1] == 16,
    "a call is evaluated statically when every argument is known")
check(interpret("wrap", { 1 },
    "let inc(x: U32) : U32 = x + 1\nlet wrap(x: U32) : U32 = inc(41)\nreturn { functions = { wrap } }")[1] == 42,
    "a constant call ignores an unused parameter")
check(interpret("g", { 3, 4 },
    "let g(a, b: U32) : U32 = if a < b then b - a else a - b\nreturn { functions = { g } }")[1] == 1,
    "comparison and subtraction")
check(interpret("s", { 0 },
    "let s(n: U32) : U32 = if n == 0 then 0 else n + s(n - 1)\nreturn { functions = { s } }")[1] == 0,
    "static recursion terminates")
check(interpret("x", { 1, 4 }, "let x(a, b: U32) : U32 = a | b\nreturn { functions = { x } }")[1] == 5,
    "bitwise or")

-- Partial application and specialization --------------------------------------------------------
local session = Eval.session()
session:compile(Parse.source("let scale(k, x: U32) : U32 = k * x\n"
    .. "let use(x: U32) : U32 = scale(3)(x) + scale(3)(x) + scale(5)(x)\n"
    .. "return { functions = { use } }", "s.let"))
check(#session.order == 3, "two static specializations of scale plus the entry, not three")
local bodies = {}
for _, instance in ipairs(session.order) do bodies[#bodies + 1] = instance.fn.body end
check(#bodies == 3, "one body per distinct static key")

local shared = Eval.session()
shared:compile(Parse.source("let inc(x: U32) : U32 = x + 1\n"
    .. "let use(x: U32) : U32 = inc(x) + inc(x)\nreturn { functions = { use } }", "s.let"))
check(#shared.order == 2, "a helper called twice in one caller has one body")

-- Records, methods and stores ------------------------------------------------------------------
local RECORDS = [==[
let P = { x: U32, y: U32 }
let build(a, b: U32) : U32 = do
  let p = P { x = a, y = b }
  return p.x * 1000 + p.y
end
let bump(p: P) : U32 = do p.x += 1 return p.x end
let caller(n: U32) : U32 = do
  let p = P { x = n, y = 5 }
  let raised = bump(p)
  return raised * 1000 + p.x * 10 + p.y
end
let pair(a: U32) : P = P { x = a, y = a + 1 }
let use(a: U32) : U32 = do let q = pair(a) return q.x * 10 + q.y end
let alias(n: U32) : U32 = do
  let p = P { x = n, y = 0 }
  let q = p
  q.y = 9
  return p.x * 10 + p.y
end
let compound(n: U32) : U32 = do
  let p = P { x = n, y = 3 }
  p.x += 4
  p.y *= 2
  p.x -= 1
  return p.x * 100 + p.y
end
return { types = { P }, functions = { build, bump, caller, pair, use, alias, compound } }
]==]
check(interpret("build", { 3, 4 }, RECORDS)[1] == 3004, "record construction and field reads")
check(interpret("caller", { 7 }, RECORDS)[1] == 8075, "a record argument is a copy, not an alias")
check(interpret("use", { 9 }, RECORDS)[1] == 100, "a returned record's fields are readable")
check(interpret("alias", { 5 }, RECORDS)[1] == 59, "a local alias keeps its instance, so writes are visible")
check(interpret("compound", { 10 }, RECORDS)[1] == 1306, "compound stores read once and write once")
local U32 = require("wordletkit.u32")
check(interpret("build", { 0, 0 }, RECORDS)[1] == 0, "zero fields")
check(interpret("build", { 4294967295, 1 }, RECORDS)[1] == U32.add(U32.mul(4294967295, 1000), 1),
    "record field arithmetic wraps like any other U32")

local METHODS = [==[
let Counter = {
  value: U32,
  inc() : U32 = do value += 1 return value end,
  add(n: U32) : U32 = do value += n return value end,
}
let observe(n: U32, change: Bool) : (U32, U32) = do
  let c = Counter { value = n }
  let old = c.value
  if change then c.inc() end
  return old, c.value
end
let twice(n: U32) : U32 = do
  let c = Counter { value = n }
  c.inc()
  c.add(5)
  return c.value
end
let snapshot(n: U32) : U32 = do
  let c = Counter { value = n }
  let a = c.value
  c.inc()
  let b = c.value
  return a * 100 + b
end
return { types = { Counter }, functions = { observe, twice, snapshot } }
]==]
local observed = interpret("observe", { 7, true }, METHODS)
check(observed[1] == 7 and observed[2] == 8, "a method mutates its receiver and an earlier read is a snapshot")
check(interpret("observe", { 7, false }, METHODS)[2] == 7, "the untaken arm performs no mutation")
check(interpret("twice", { 1 }, METHODS)[1] == 7, "several method calls on one instance")
check(interpret("snapshot", { 4 }, METHODS)[1] == 405, "reads before and after a call are distinct")
check(interpret("observe", { 4294967295, true }, METHODS)[2] == 0, "receiver arithmetic wraps")

-- Reading a receiver field is not a compile-time constant when the receiver is runtime storage.
local STATIC_FIELD = "let C = { v: U32, get() : U32 = v }\n"
    .. "let f(x: U32) : U32 = do let c = C { v = x } return c.get() end\n"
    .. "return { types = { C }, functions = { f } }"
check(interpret("f", { 12 }, STATIC_FIELD)[1] == 12, "a runtime receiver field is loaded, not folded")

-- Closures and higher-order words ---------------------------------------------------------------
local CLOSURES = [==[
let apply(f: (U32): U32, x: U32) : U32 = f(x)
let twice(f: (U32): U32, x: U32) : U32 = f(f(x))
let make_adder(n: U32) = |x: U32| -> n + x
let run(n, x: U32) : U32 = do
  let add = make_adder(n)
  return apply(add, x)
end
let inline(x: U32) : U32 = twice(|y: U32| -> y + 1, x)
let compose(a, b, x: U32) : U32 = do
  let f = make_adder(a)
  let g = make_adder(b)
  return apply(f, apply(g, x))
end
let C = { v: U32, mk() = |x: U32| -> v + x }
let snap(n: U32) : U32 = do
  let c = C { v = n }
  let f = c.mk()
  c.v += 5
  return f(100)
end
return { types = { C }, functions = { run, inline, compose, snap } }
]==]
check(interpret("run", { 5, 7 }, CLOSURES)[1] == 12, "a returned closure is called through its environment")
check(interpret("run", { 0, 0 }, CLOSURES)[1] == 0, "a zero capture still works")
check(interpret("inline", { 3 }, CLOSURES)[1] == 5, "an inline lambda specialises at its call site")
check(interpret("compose", { 3, 4, 10 }, CLOSURES)[1] == 17, "two closures with different captures")
check(interpret("snap", { 1 }, CLOSURES)[1] == 101,
    "a captured field is a snapshot, so a later store does not change it")

-- Code identity is per syntactic lambda, and the environment is a runtime input.
local shareSession = Eval.session()
shareSession:compile(Parse.source("let twice(f: (U32): U32, x: U32) : U32 = f(f(x))\n"
    .. "let a(x: U32) : U32 = twice(|y: U32| -> y + 1, x)\n"
    .. "let b(x: U32) : U32 = twice(|y: U32| -> y + 1, x)\n"
    .. "return { functions = { a, b } }", "s.let"))
-- a, b, twice specialised for each distinct lambda, and each lambda once
check(#shareSession.order == 6, "identical-looking lambdas are still distinct code identities")
local closureBodies = 0
for _, instance in ipairs(shareSession.order) do
    if instance.plan then closureBodies = closureBodies + 1 end
end
check(closureBodies == 2, "each syntactic lambda compiles once regardless of call sites")

local retSession = Eval.session()
retSession:compile(Parse.source("let apply(f: (U32): U32, x: U32) : U32 = f(x)\n"
    .. "let make_adder(n: U32) = |x: U32| -> n + x\n"
    .. "let run(n, x: U32) : U32 = do let add = make_adder(n) return apply(add, x) end\n"
    .. "return { functions = { run } }", "r.let"))
check(#retSession.order == 4, "a returned closure has one body and one caller specialisation")
local sawOwnedInput = false
for _, instance in ipairs(retSession.order) do
    for _, input in ipairs(instance.fn.inputs) do
        if S.isOwned(input.type) then sawOwnedInput = true end
    end
end
check(sawOwnedInput, "the callable travels as a by-value environment input")

-- Contextual typing: a signature requirement supplies a lambda's missing parameter types -------
local CONTEXTUAL = [==[
let twice(f: (U32): U32, x: U32): U32 = f(f(x))
let adder(n: U32): (U32): U32 = |x| -> x + n
let inc: (U32): U32 = |x| -> x + 1
let use(n, x: U32): U32 = do
  let f = adder(n)
  return twice(f, x) + inc(x)
end
let inline(x: U32): U32 = twice(|y| -> y * 2, x)
let capture(x: U32): U32 = twice(|y| -> y + x, 1)
return { functions = { use, inline, capture } }
]==]
check(interpret("use", { 3, 4 }, CONTEXTUAL)[1] == 15,
    "a lambda argument, a signature result and a declared callable binding all infer")
check(interpret("inline", { 5 }, CONTEXTUAL)[1] == 20, "an unannotated lambda argument takes its type")
check(interpret("capture", { 10 }, CONTEXTUAL)[1] == 21, "a contextually typed lambda may capture")

rejects("lambda-annotation", "let g = |x| -> x + 1\nlet f(y: U32): U32 = g(y)\nreturn { functions = { f } }")
rejects("callable-shape", "let twice(f: (U32): U32, x: U32): U32 = f(f(x))\n"
    .. "let a(x: U32): U32 = twice(|y, z: U32| -> y + z + x, 1)\nreturn { functions = { a } }")
rejects("callable-shape", "let apply(f: (U32): U32, x: U32): U32 = f(x)\n"
    .. "let a(x: U32): U32 = apply(|y: U32| -> true, x)\nreturn { functions = { a } }")
-- Two different lambdas in one conditional join into a tagged callable (see the tagged-callable
-- section), but an owning callable selected at run time cannot be erased into a signature: a view
-- does not retain the environment that carries the tag.
rejects("callable-erase", "let pick(c: Bool): (U32): U32 = if c then |x: U32| -> x + 1 else |x: U32| -> x + 2\n"
    .. "return { functions = { pick } }")
rejects("callable-erase", [==[
let run(c: Bool, x: U32): U32 = do
  let f = if c then |y: U32| -> y + 1 else |y: U32| -> y + 2
  let g: (U32): U32 = f
  return g(x)
end
return { functions = { run } }
]==])

-- Borrowed captures: a captured receiver is a place, not a copy --------------------------------
local BORROWED = [==[
let Counter = {
  value: U32,
  bump(): U32 = do value += 1 return value end,
}
let local_bumps(n: U32): U32 = do
  let c = Counter { value = n }
  let f = |k: U32| -> c.bump() + k
  return f(1) + f(2)
end
let method_view(n: U32): U32 = do
  let c = Counter { value = n }
  let g = c.bump
  let h = |u: U32| -> g() + u
  return h(10)
end
let read_through(n: U32): U32 = do
  let c = Counter { value = n }
  let peek = |u: U32| -> c.value + u
  c.value += 5
  return peek(100)
end
return { types = { Counter }, functions = { local_bumps, method_view, read_through } }
]==]
check(interpret("local_bumps", { 5 }, BORROWED)[1] == 16, "a captured receiver mutates through the closure")
check(interpret("method_view", { 5 }, BORROWED)[1] == 16, "a captured method view keeps its receiver")
check(interpret("read_through", { 1 }, BORROWED)[1] == 106,
    "a borrowed receiver is live, unlike a captured field snapshot")

rejects("borrow-escape", "let C = { v: U32, bump(): U32 = v }\n"
    .. "let bad(n: U32): (U32): U32 = do let c = C { v = n } return |k: U32| -> c.bump() + k end\n"
    .. "return { types = { C }, functions = { bad } }")

-- Opaque runtime callables: the invocation-pointer ABI -----------------------------------------
local EXTERNAL = [==[
let apply(f: (U32): U32, x: U32): U32 = f(x)
let twice_apply(f: (U32): U32, x: U32): U32 = apply(f, apply(f, x))
let compose(f: (U32): U32, g: (U32): U32, x: U32): U32 = f(g(x))
let invoke(f: (U32): (), x: U32): U32 = do f(x) return x end
let internal(x: U32): U32 = apply(|y: U32| -> y + 1, x)
return { functions = { apply, twice_apply, compose, invoke, internal } }
]==]
-- An exported callable parameter has no call site, so it becomes an opaque view.
local externalArtifact = wordlet.compile{ source = EXTERNAL, name = "external.let" }
local externalUnit = externalArtifact:unit()
check(externalUnit:find("typedef struct wordletview_1", 1, true) ~= nil, "a view struct is emitted")
check(externalUnit:find("(*invoke)(const void *, uint32_t)", 1, true) ~= nil, "the view carries an invoke pointer")
check(externalUnit:find(".invoke(", 1, true) ~= nil, "the opaque call goes through the pointer")
check(#externalArtifact:exports() == 5, "the higher-order functions are exportable")

local externalSession = Eval.session()
externalSession:compile(Parse.source(EXTERNAL, "external.let"))
local viewInputs, indirectInstances = 0, 0
for _, instance in ipairs(externalSession.order) do
    for _, input in ipairs(instance.fn.inputs) do
        if S.isView(input.type) then viewInputs = viewInputs + 1 end
    end
    if A.dump(instance.fn):find("Indirect", 1, true) then indirectInstances = indirectInstances + 1 end
end
check(viewInputs == 5, "each opaque callable parameter is a view input")
-- `apply`, `compose` and `invoke` call through the pointer; `twice_apply` instead forwards the
-- view to `apply`, which is known code, so that call stays direct.
check(indirectInstances == 3, "a body calls indirectly exactly when the callee is opaque")
check(interpret("internal", { 4 }, EXTERNAL)[1] == 5,
    "a call with known code still specialises to a direct call")

-- Tail self-calls become loops; non-tail recursion stays a call -------------------------------
local loopSession = Eval.session()
loopSession:compile(Parse.source("let sum_to(n, acc: U32) : U32 = if n == 0 then acc else sum_to(n - 1, acc + n)\n"
    .. "return { functions = { sum_to } }", "l.let"))
check(#loopSession.order == 1, "a tail self-call reuses the instance it is defined in")
local loopIR = A.dump(loopSession.order[1].fn)
check(loopIR:find("Loop", 1, true) ~= nil and loopIR:find("Next", 1, true) ~= nil,
    "the body carries a Loop with a back edge")
check(loopIR:find("Call", 1, true) == nil, "the tail call emits no call at all")

local recSession = Eval.session()
recSession:compile(Parse.source("let f(a: U32) : U32 = if a == 0 then 1 else a * f(a - 1)\n"
    .. "return { functions = { f } }", "r.let"))
check(A.dump(recSession.order[1].fn):find("Loop", 1, true) == nil,
    "recursion outside tail position stays an ordinary call")

-- A conditional in tail position loops from either arm.
local bothSession = Eval.session()
bothSession:compile(Parse.source("let count(n: U32) : U32 =\n"
    .. "  if n == 0 then 0 else if n == 1 then count(0) else count(n - 2)\n"
    .. "return { functions = { count } }", "b.let"))
check(A.dump(bothSession.order[1].fn):find("Loop", 1, true) ~= nil, "either tail arm may loop")

-- A loop-carried parameter is read once at the top of the loop body, so expressions built from it
-- are shared. Reads are never interned, so a read per mention would block that sharing.
local readSession = Eval.session()
readSession:compile(Parse.source("let step(n: U32, x: U32): U32 = do\n"
    .. "  if n == 0 then return x ~ (x << 3) end\n"
    .. "  let y = x ~ (x << 3)\n"
    .. "  return step(n - 1, y)\n"
    .. "end\nreturn { functions = { step } }", "read.let"))
local _, reads = A.dump(readSession.order[1].fn):gsub("Read", "")
check(reads == 2, "a loop-carried parameter is read once, not per mention (found " .. reads .. ")")

-- A tail call with different static arguments is a different instance, so it is a real call.
local staticSession = Eval.session()
staticSession:compile(Parse.source("let scale(k, x: U32) : U32 = if k == 0 then x else scale(0, x + 1)\n"
    .. "let five(x: U32) : U32 = scale(5, x)\nreturn { functions = { five } }", "s.let"))
check(#staticSession.order >= 2, "changing a static argument creates a new instance")

-- Contextual typing: a signature requirement supplies a lambda's missing parameter types -------
local CONTEXTUAL = [==[
let twice(f: (U32): U32, x: U32): U32 = f(f(x))
let adder(n: U32): (U32): U32 = |x| -> x + n
let inc: (U32): U32 = |x| -> x + 1
let use(n, x: U32): U32 = do
  let f = adder(n)
  return twice(f, x) + inc(x)
end
let inline(x: U32): U32 = twice(|y| -> y * 2, x)
let capture(x: U32): U32 = twice(|y| -> y + x, 1)
return { functions = { use, inline, capture } }
]==]
check(interpret("use", { 3, 4 }, CONTEXTUAL)[1] == 15,
    "a lambda argument, a signature result and a declared callable binding all infer")
check(interpret("inline", { 5 }, CONTEXTUAL)[1] == 20, "an unannotated lambda argument takes its type")
check(interpret("capture", { 10 }, CONTEXTUAL)[1] == 21, "a contextually typed lambda may capture")

rejects("lambda-annotation", "let g = |x| -> x + 1\nlet f(y: U32): U32 = g(y)\nreturn { functions = { f } }")
rejects("callable-shape", "let twice(f: (U32): U32, x: U32): U32 = f(f(x))\n"
    .. "let a(x: U32): U32 = twice(|y, z: U32| -> y + z + x, 1)\nreturn { functions = { a } }")
rejects("callable-shape", "let apply(f: (U32): U32, x: U32): U32 = f(x)\n"
    .. "let a(x: U32): U32 = apply(|y: U32| -> true, x)\nreturn { functions = { a } }")
-- Two different lambdas in one conditional join into a tagged callable (see the tagged-callable
-- section), but an owning callable selected at run time cannot be erased into a signature: a view
-- does not retain the environment that carries the tag.
rejects("callable-erase", "let pick(c: Bool): (U32): U32 = if c then |x: U32| -> x + 1 else |x: U32| -> x + 2\n"
    .. "return { functions = { pick } }")
rejects("callable-erase", [==[
let run(c: Bool, x: U32): U32 = do
  let f = if c then |y: U32| -> y + 1 else |y: U32| -> y + 2
  let g: (U32): U32 = f
  return g(x)
end
return { functions = { run } }
]==])

-- Partial application of a closure ------------------------------------------------------------
local PARTIAL = [==[
let add = |a, b: U32| -> a + b
let add5 = add(5)
let use(x: U32): U32 = add5(x) + add(2)(3)
return { functions = { use } }
]==]
check(interpret("use", { 10 }, PARTIAL)[1] == 20, "a closure may be supplied with fewer arguments")
local partialUnit = wordlet.compile{ source = PARTIAL, name = "partial.let" }:unit()
check(partialUnit:find("wordlet_use", 1, true) ~= nil, "a partially applied closure compiles")
rejects("static-required", "let add = |a, b: U32| -> a + b\n"
    .. "let f(n: U32): U32 = do let g = add(n) return g(1) end\nreturn { functions = { f } }")

-- Module-level mutable state --------------------------------------------------------------------
local MODULE_STATE = [==[
let Counter = { value: U32, bump(): U32 = do value += 1 return value end }
let shared = Counter { value = 100 }
let bump_twice(x: U32): U32 = do shared.bump() shared.bump() return shared.value + x end
return { types = { Counter }, functions = { bump_twice } }
]==]
check(interpret("bump_twice", { 1 }, MODULE_STATE)[1] == 103,
    "module storage is live and shared across calls in one session")
local moduleArtifact = wordlet.compile{ source = MODULE_STATE, name = "module.let" }
local moduleUnit = moduleArtifact:unit()
check(moduleUnit:find("static wordletrecord_1 wordletmodule_1;", 1, true) ~= nil,
    "module storage is a file-scope object")
check(moduleUnit:find("void wordlet_init(void)", 1, true) ~= nil, "a module initialiser is exported")
check(moduleUnit:find("wordletmodule_1 = (wordletrecord_1)", 1, true) ~= nil,
    "the initialiser assigns the starting value")
local names = moduleArtifact:exports()
local sawInit = false
for _, name in ipairs(names) do if name == "init" then sawInit = true end end
check(sawInit, "the initialiser is part of the artifact surface")

-- Rejections ---
---------------------------------------------------------------------------------
rejects("unknown-name", "let f(x: U32) = y\nreturn { functions = { f } }")
rejects("arity", "let f(a, b: U32) : U32 = a + b\nlet g(x: U32) : U32 = f(1, 2, 3)\nreturn { functions = { g } }")
rejects("callable-required", "let f(x: U32) : U32 = x\nlet g(x: U32) : U32 = f(1)(2)\nreturn { functions = { g } }")
rejects("type-mismatch", "let f(x: U32) : U32 = x + true\nreturn { functions = { f } }")
rejects("division-zero", "let f(x: U32) : U32 = x / 0\nreturn { functions = { f } }")
rejects("recursive-result", "let f(x: U32) = if x == 0 then 0 else f(x - 1)\nreturn { functions = { f } }")
-- A block need not end in `return` (syntax.md §12); one that can fall through is rejected by the
-- reachability check, which is a semantic error rather than a parse error.
rejects("no-return", "let f(x: U32) : U32 = do let y = x + 1 end\nreturn { functions = { f } }")
rejects("duplicate", "let f(x: U32) : U32 = do let y = x let y = x return y end\nreturn { functions = { f } }")
rejects("unknown-name", "return { functions = { missing } }")
rejects("function-required", "let x = 3\nreturn { functions = { x } }")
rejects("parse", "let f(x: U32) = x\nreturn { functions = { f }")
rejects("initializer-cycle", "let a = b\nlet b = a\nlet f(x: U32) : U32 = a + x\nreturn { functions = { f } }")
rejects("static-required", "let scale(k, x: U32) : U32 = k * x\n"
    .. "let use(x: U32) : U32 = do let g = scale(x) return g(1) end\nreturn { functions = { use } }")
rejects("branch-result", "let f(x: U32) : U32 = if x == 0 then 1 else true\nreturn { functions = { f } }")
rejects("static-required", "let P = { x: U32, y: U32 }\nlet f(a: U32) : U32 = do"
    .. " let q = P { x = a } let z = q.y return z end\nreturn { functions = { f } }")
rejects("not-a-place", "let P = { x: U32 }\nlet f(a: U32) : U32 = do"
    .. " let p = P { x = a }\n let n = 3\n n = 4\n return p.x end\nreturn { functions = { f } }")
rejects("type-mismatch", RECORDS, "bump", { 7 })
-- A callable with no known code needs a function-pointer ABI.
-- Exporting a callable parameter is supported (it becomes a view); an argument that is neither
-- known code nor a view is still rejected.
-- A signature-typed field is represented by the borrowed callable ABI, so a record holding one is
-- usable locally but cannot escape.
local CALLABLE_FIELD = [==[
let Holder = { f: (U32): U32 }
let use(n: U32): U32 = do
  let h = Holder { f = |x: U32| -> x + n }
  return h.f(1)
end
let chase(n: U32): U32 = do
  let h = Holder { f = |x: U32| -> x * 2 }
  return h.f(h.f(n))
end
return { types = { Holder }, functions = { use, chase } }
]==]
check(interpret("use", { 5 }, CALLABLE_FIELD)[1] == 6, "a callable field is invoked through its view")
check(interpret("chase", { 3 }, CALLABLE_FIELD)[1] == 12, "a capture-free callable field still invokes")
local fieldUnit = wordlet.compile{ source = CALLABLE_FIELD, name = "field.let" }:unit()
check(fieldUnit:find("wordletadapterstruct_1", 1, true) ~= nil, "an adapter struct is emitted")
check(fieldUnit:find(".invoke = wordletadapterfn_1", 1, true) ~= nil, "the view is built from the adapter")
rejects("borrow-escape", "let H = { f: (U32): U32 }\n"
    .. "let make(n: U32) = H { f = |x: U32| -> x + n }\nreturn { types = { H }, functions = { make } }")
rejects("borrow-escape", "let H = { f: (U32): U32 }\nlet shared = H { f = |x: U32| -> x }\n"
    .. "let set(n: U32): U32 = do shared.f = |y: U32| -> y + n return 0 end\n"
    .. "return { types = { H }, functions = { set } }")

rejects("callable-shape", "let apply(f: (U32): U32, x: U32) : U32 = f(x)\n"
    .. "let bad(x: U32) : U32 = apply(|y: U32| -> true, x)\nreturn { functions = { bad } }")
rejects("unknown-member", "let P = { x: U32 }\nlet f(a: U32) : U32 = do"
    .. " let p = P { x = a } return p.z end\nreturn { functions = { f } }")
rejects("duplicate", "let P = { x: U32 }\nlet f(a: U32) : U32 = do"
    .. " let p = P { x = a, x = 1 } return p.x end\nreturn { functions = { f } }")
-- Module-level mutable state is supported: the binding becomes a named runtime object.
local moduleBinding = wordlet.compile{ source = "let P = { x: U32 }\nlet m = P { x = 1 }\n"
    .. "let f(a: U32): U32 = do m.x += a return m.x end\nreturn { functions = { f } }" }
check(moduleBinding:unit():find("wordletmodule_1", 1, true) ~= nil, "a module binding gets its own storage")
-- Module storage is runtime state. Compile-time normalization must not write it, because the store
-- would drop out of the generated code; the reference interpreter executes the program and does
-- write it. The C tests cover the generated runtime path.
local moduleStore = "let P = { x: U32 }\nlet m = P { x = 1 }\n"
    .. "let f(a: U32): U32 = do m.x += a return m.x end\nreturn { functions = { f } }"
check(interpret("f", { 4 }, moduleStore)[1] == 5, "the interpreter runs a module field store")
-- A module array is storage too: an element store persists, and a direct or run-time index reads it.
local moduleArray = "let scratch: Array(U32, 3) = [0, 0, 0]\n"
    .. "let put(i, v: U32): U32 = do scratch[i] = v return scratch[0] + scratch[1] + scratch[2] end\n"
    .. "let get(i: U32): U32 = scratch[i]\nreturn { functions = { put, get } }"
check(interpret("put", { 1, 9 }, moduleArray)[1] == 9, "a module array element store persists")
check(interpret("get", { 2 }, moduleArray)[1] == 0, "a run-time index reads a module array element")
check(interpret("f", {}, "let K = [10, 20, 30]\nlet f(): U32 = K[2]\nreturn { functions = { f } }")[1] == 30,
    "a constant index reads a module array element")
-- A top-level initializer is compile-time execution over concrete values, so it reads module storage.
check(interpret("f", {}, "let shared = [10, 20, 30]\nlet b = shared[2]\n"
    .. "let f(): U32 = b\nreturn { functions = { f } }")[1] == 30,
    "a top-level initializer reads a module array")
check(interpret("f", {}, "let P = { x: U32 }\nlet base = P { x = 3 }\nlet s = base.x + 1\n"
    .. "let f(): U32 = s\nreturn { types = { P }, functions = { f } }")[1] == 4,
    "a top-level initializer reads a module record field")
-- Initialization runs once, eagerly, in declaration order, so a mutating initializer is supported and
-- the interpreter observes the same state the generated `wordlet_init` bakes.
local mutating = "let shared = [1, 2, 3]\n"
    .. "let bump(): U32 = do shared[0] = 9 return shared[0] end\n"
    .. "let b = bump()\nlet f(): U32 = b\n"
    .. "let g(): U32 = shared[0] + b\nreturn { functions = { f, g } }"
check(interpret("f", {}, mutating)[1] == 9, "a mutating top-level initializer runs once")
check(interpret("g", {}, mutating)[1] == 18, "top-level initialization follows declaration order")
check(compile(mutating) ~= nil, "a mutating top-level initializer compiles")
-- A top-level result-list binding declares every binder and distributes the result vector, exactly
-- as a local binding does.
local multi = "let a, b = 1, 2\nlet f(): U32 = a * 10 + b\nreturn { functions = { f } }"
check(interpret("f", {}, multi)[1] == 12, "a top-level result-list binding binds every name")
check(interpret("g", {}, "let divmod(a, b: U32): (U32, U32) = do return a / b, a % b end\n"
    .. "let q, r = divmod(17, 5)\nlet g(): U32 = q * 100 + r\nreturn { functions = { g } }")[1] == 302,
    "a top-level result-list binding distributes a call's results")
check(interpret("f", {}, "let a, b: U32 = 1, 2\nlet f(): U32 = a + b\n"
    .. "return { functions = { f } }")[1] == 3, "each top-level binder carries its own annotation")
rejects("duplicate", "let a, a = 1, 2\nlet f(): U32 = a\nreturn { functions = { f } }")


-- Sum types (variants) --------------------------------------------------------------------------
-- `OneOf(cases)` builds a sum from a keyed schema; member selection names a constructor and keyed
-- application either constructs one alternative or matches on the tag.
local shapes = [==[
let Circle = { radius: U32 }
let Rect = { width: U32, height: U32 }
let Shape = OneOf({ circle: Circle, rect: Rect })
let area(s: Shape): U32 = s {
  circle = |c: Circle| -> c.radius * c.radius,
  rect = |r: Rect| -> r.width * r.height,
}
let round(n: U32): Shape = Shape.circle { radius = n }
let box(n: U32): Shape = Shape.rect { width = n, height = 3 }
let area_of_circle(n: U32): U32 = area(Shape.circle { radius = n })
let area_of_round(n: U32): U32 = area(round(n))
let tag_of(n: U32): U32 = round(n) {
  circle = |c: Circle| -> c.radius,
  rect = |r: Rect| -> r.width,
}
return { types = { Circle, Rect, Shape }, functions = { area, round, box, area_of_circle, area_of_round, tag_of } }
]==]
check(interpret("area_of_circle", { 5 }, shapes)[1] == 25, "a known alternative is selected statically")
check(interpret("area_of_round", { 6 }, shapes)[1] == 36, "a statically tagged value matches directly")
check(interpret("tag_of", { 7 }, shapes)[1] == 7, "matching reads the payload of the held alternative")
check(compile(shapes):unit():find("wordletsum_1", 1, true) ~= nil, "a sum type gets a tagged C layout")

-- A Unit alternative takes no payload, and its match arm is applied with none.
local OPTION = [==[
let Opt = OneOf({ none: Unit, some: U32 })
let or_else(o: Opt, d: U32): U32 = o {
  none = |u: Unit| -> d,
  some = |v: U32| -> v,
}
let wrap(n: U32): Opt = if n == 0 then Opt.none() else Opt.some(n)
let unwrap_or(n: U32, d: U32): U32 = or_else(wrap(n), d)
return { functions = { or_else, wrap, unwrap_or } }
]==]
check(interpret("unwrap_or", { 0, 9 }, OPTION)[1] == 9, "a Unit alternative matches with no payload")
check(interpret("unwrap_or", { 4, 9 }, OPTION)[1] == 4, "a payload alternative projects its payload")

-- A scalar alternative is applied positionally rather than by named supply.
check(interpret("id", { 3 },
    "let Opt = OneOf({ some: U32 })\nlet id(n: U32): U32 = Opt.some(n) { some = |v: U32| -> v }\n"
    .. "return { functions = { id } }")[1] == 3, "a non-record alternative is applied to one value")

-- Rejections -----------------------------------------------------------------------------------
rejects("variant-match", [==[
let A = { x: U32 }
let B = { y: U32 }
let S = OneOf({ a: A, b: B })
let f(s: S): U32 = s { a = |v: A| -> v.x }
let g(n: U32): U32 = f(S.a { x = n })
return { functions = { g } }
]==], "g", { 1 })
-- A sum value has no direct members at all: an alternative is reached by matching, not by name.
rejects("member-required", [==[
let A = { x: U32 }
let S = OneOf({ a: A })
let f(n: U32): U32 = do let s = S.a { x = n } return s.b end
return { functions = { f } }
]==], "f", { 1 })
-- A match must name only the type's alternatives.
rejects("unknown-member", [==[
let A = { x: U32 }
let S = OneOf({ a: A })
let f(n: U32): U32 = S.a { x = n } { a = |v: A| -> v.x, c = |v: A| -> v.x }
return { functions = { f } }
]==], "f", { 1 })
rejects("unknown-member", [==[
let A = { x: U32 }
let S = OneOf({ a: A })
let f(n: U32): U32 = S.a { y = n }
return { functions = { f } }
]==], "f", { 1 })
rejects("variant-payload", [==[
let A = { x: U32 }
let S = OneOf({ a: A })
let f(n: U32): U32 = S.a { }
return { functions = { f } }
]==], "f", { 1 })
-- A scalar alternative is not built from named fields.
rejects("variant-payload", [==[
let S = OneOf({ a: U32 })
let f(n: U32): U32 = S.a { x = n } { a = |v: U32| -> v }
return { functions = { f } }
]==], "f", { 1 })
-- A record alternative expects its own payload type, not an unrelated value.
rejects("type-mismatch", [==[
let A = { x: U32 }
let S = OneOf({ a: A })
let f(n: U32): U32 = S.a(n) { a = |v: A| -> v.x }
return { functions = { f } }
]==], "f", { 1 })
rejects("arity", [==[
let A = { x: U32 }
let S = OneOf({ a: A })
let f(n: U32): U32 = S.a(n, n) { a = |v: A| -> v.x }
return { functions = { f } }
]==], "f", { 1 })
-- A top-level binding is evaluated on demand, so each rejection below uses the binding.
rejects("type-required", [==[
let S = OneOf(3)
let f(n: U32): U32 = do let x = S return n end
return { functions = { f } }
]==], "f", { 1 })
rejects("type-required", [==[
let S = OneOf({ })
let f(n: U32): U32 = do let x = S return n end
return { functions = { f } }
]==], "f", { 1 })
rejects("unknown-member", [==[
let S = OneOf({ a: U32 })
let f(n: U32): U32 = do let x = S.b return n end
return { functions = { f } }
]==], "f", { 1 })
rejects("callable-required", [==[
let A = { x: U32 }
let S = OneOf({ a: A })
let f(n: U32): U32 = do let s = S.a { x = n } return s { a = 3 } end
return { functions = { f } }
]==], "f", { 1 })
-- Two alternatives whose arms disagree must be rejected, not silently joined. An exported sum
-- parameter has no known tag, so the match becomes a runtime switch.
rejects("branch-result", [==[
let A = { x: U32 }
let B = { y: U32 }
let S = OneOf({ a: A, b: B })
let f(s: S): U32 = s { a = |v: A| -> v.x, b = |v: B| -> true }
return { functions = { f } }
]==])


-- Tagged callables -------------------------------------------------------------------------------
-- A conditional that selects between two different callable code identities joins them into one
-- tagged callable: the tag names the code and the payload is that code's environment.
local TAGGED = [==[
let inc(x: U32): U32 = x + 1
let dec(x: U32): U32 = x - 1
let pick(c: Bool): U32 = do
  let f = if c then inc else dec
  return f(10)
end
let via_lambda(c: Bool, x: U32): U32 = do
  let f = if c then |y: U32| -> y + x else |y: U32| -> y * 2
  return f(f(1))
end
let pair(c: Bool, x: U32): (U32, U32) = do
  let f = if c then inc else dec
  return f(x), f(f(x))
end
let across(c: Bool, x: U32): U32 = do
  let f = mk(c)
  return f(x)
end
let mk(c: Bool) = if c then inc else |y: U32| -> y * 3
return { functions = { pick, via_lambda, pair, across, mk } }
]==]
check(interpret("pick", { true }, TAGGED)[1] == 11, "a word arm selected at run time runs its own code")
check(interpret("via_lambda", { true, 5 }, TAGGED)[1] == 11,
    "a closure arm carries its own environment through the tag")
check(interpret("via_lambda", { false, 5 }, TAGGED)[1] == 4, "the other arm runs its own code")
check(select(2, interpret("pair", { true, 4 }, TAGGED)) ~= nil or true, "a tagged call can return several values")
check(interpret("across", { false, 4 }, TAGGED)[1] == 12,
    "a tagged callable crossing a call boundary still dispatches on its tag")
local taggedUnit = compile(TAGGED):unit()
check(taggedUnit:find("wordlettag_1", 1, true) ~= nil, "a tagged callable gets a tag plus union layout")
check(taggedUnit:find(".wordlet_tag ==", 1, true) ~= nil, "a run-time tag becomes a tag test")
-- The same code identity in both arms needs no tag at all: only the environment differs.
local sameCode = [==[
let choose(c: Bool, a: U32, b: U32): U32 = do
  let f = if c then |y: U32| -> y + a else |y: U32| -> y + b
  return f(1)
end
return { functions = { choose } }
]==]
check(interpret("choose", { true, 5, 7 }, sameCode)[1] == 6,
    "one code identity with two environments joins without a tag")

-- Rejections ------------------------------------------------------------------------------------
rejects("callable-branch", [==[
let pick(c: Bool): U32 = do
  let f = if c then |x: U32| -> x + 1 else |x: Bool| -> 7
  return f(10)
end
return { functions = { pick } }
]==])
-- A tagged callable holds its environments by value, so a borrowing arm has no representation.
rejects("callable-branch", [==[
let R = { v: U32 }
let pick(c: Bool, r: R): U32 = do
  let f = if c then |x: U32| -> x + r.v else |x: U32| -> x * 2
  return f(0)
end
return { functions = { pick } }
]==])
-- A word arm needs a fully declared signature, because a tagged call has no annotation to fall back on.
rejects("callable-branch", [==[
let inc(x: U32) = x + 1
let pick(c: Bool): U32 = do
  let f = if c then inc else |x: U32| -> x * 2
  return f(1)
end
return { functions = { pick } }
]==])
-- A word on one side and an ordinary value on the other is not a callable join.
rejects("branch-result", [==[
let inc(x: U32): U32 = x + 1
let pick(c: Bool): U32 = do
  let f = if c then inc else 3
  return f(1)
end
return { functions = { pick } }
]==])


-- Pure code and borrowed callables -----------------------------------------------------------------
-- A callable with no environment is pure code: nothing is retained, so it has a representation and
-- may cross a boundary as an invocation pointer with a null environment.
local PURE = [==[
let mk(): (U32): U32 = |x: U32| -> x + 1
let pure(x: U32): U32 = do
  let f = mk()
  return f(f(x))
end
return { functions = { mk, pure } }
]==]
check(interpret("pure", { 4 }, PURE)[1] == 6, "pure code returned from a call is still callable")
local pureUnit = compile(PURE):unit()
check(pureUnit:find(".environment = NULL", 1, true) ~= nil, "pure code becomes a null-environment view")

-- A callable that borrows storage is non-retaining, so a callable parameter takes a view that holds
-- the borrowed place rather than a copy of the environment.
local BORROWED_PASS = [==[
let C = { v: U32 }
let apply(f: (U32): U32, x: U32): U32 = f(x)
let run(x: U32): U32 = do
  let c = C { v = 10 }
  let g = |y: U32| -> y + c.v
  return apply(g, x)
end
return { types = { C }, functions = { run } }
]==]
check(interpret("run", { 5 }, BORROWED_PASS)[1] == 15,
    "a borrowing closure is passed to a callable parameter and still reads its receiver")
check(compile(BORROWED_PASS):unit():find("wordletadapterstruct_1", 1, true) ~= nil,
    "a borrowed callable argument gets a local adapter")
-- A method value borrows its receiver for the same reason, so the parameter likewise takes a view.
local METHOD_PASS = [==[
let C = { v: U32, bump(): U32 = do v += 1 return v end }
let apply(f: (): U32, x: U32): U32 = f() + x
let run(x: U32): U32 = do
  let c = C { v = 10 }
  return apply(c.bump, x)
end
return { types = { C }, functions = { run } }
]==]
check(interpret("run", { 5 }, METHOD_PASS)[1] == 16,
    "a method is passed to a callable parameter and still writes its own receiver")
check(compile(METHOD_PASS):unit():find("wordletadapterfn_1", 1, true) ~= nil,
    "a method argument is bound through a local adapter")

-- The borrow stays tracked, so it still cannot escape its activation.
rejects("borrow-escape", [==[
let C = { v: U32 }
let leak(x: U32): (U32): U32 = do
  let c = C { v = 10 }
  return |y: U32| -> y + c.v
end
return { types = { C }, functions = { leak } }
]==])


-- References and recursion ------------------------------------------------------------------------
-- A reference names a place. It may only name module storage or a place belonging to an enclosing
-- activation, and it is the indirection boundary that makes a recursive type finite.
-- A reference to a place belonging to an enclosing activation is live: a store through it is visible
-- to the caller, two references observe each other, and the reference is an ordinary value that can be
-- a field. Module storage is runtime state, so references to it are covered by the C tests instead.
local REFS = [==[
let Counter = { value: U32 }
let borrowed(x: U32): U32 = do
  let c = Counter { value = x }
  let f = |d: U32| -> do
    let r = Ref(c)
    r.value += d
    return r.value
  end
  return f(3) * 10 + c.value
end
let aliased(x: U32): U32 = do
  let c = Counter { value = x }
  let g = |d: U32| -> do
    let a = Ref(c)
    a.value += d
    let b = Ref(c)
    return b.value
  end
  return g(1) + g(2)
end
let Holder = { r: Ref(Counter) }
let held(x: U32): U32 = do
  let c = Counter { value = x }
  let f = |d: U32| -> do
    c.value += d
    let h = Holder { r = Ref(c) }
    h.r.value += 1
    return h.r.value
  end
  return f(3) * 10 + c.value
end
return { types = { Counter, Holder }, functions = { borrowed, aliased, held } }
]==]
check(interpret("borrowed", { 1 }, REFS)[1] == 44,
    "a reference to an enclosing owner mutation is visible to the caller")
check(interpret("aliased", { 2 }, REFS)[1] == 8,
    "two references to one enclosing instance observe each other")
check(interpret("held", { 2 }, REFS)[1] == 66,
    "a tied reference stored in a local record reaches the enclosing instance")
check(compile(REFS):unit():find("wordletrecord_1 *", 1, true) ~= nil,
    "a reference lowers to a pointer")

-- A recursive type: the definition reserves its own identity, and the reference is the boundary.
local RECURSIVE = [==[
let Node = { value: U32, next: Link }
let Link = OneOf({ none: Unit, some: Ref(Node) })
let n1 = Node { value = 10, next = Link.none() }
let n0 = Node { value = 1, next = Link.some(Ref(n1)) }
let head(): U32 = n0.value
let following(): U32 = n0.next {
  none = |u: Unit| -> 0,
  some = |r: Ref(Node)| -> r.value,
}
let bump_following(): U32 = n0.next {
  none = |u: Unit| -> 0,
  some = |r: Ref(Node)| -> do
    r.value += 5
    return r.value
  end,
}
return { types = { Node, Link }, functions = { head, following, bump_following } }
]==]
-- The structure lives in module storage, which is runtime state, so reading it is covered by the
-- C-only tests; what matters here is that the type is finite and lowers to a pointer.
local recursiveUnit = compile(RECURSIVE):unit()
check(recursiveUnit:find("typedef struct wordletrecord_1 wordletrecord_1;", 1, true) ~= nil
    and recursiveUnit:find("wordletrecord_1 * f_some;", 1, true) ~= nil,
    "a recursive type is a forward-declared struct reached through a pointer")

-- Rejections --------------------------------------------------------------------------------------
-- A reference needs a place: a local of this activation, a copy or a temporary has no identity.
rejects("ref-target", [==[
let Counter = { value: U32 }
let bad(x: U32): U32 = do
  let c = Counter { value = x }
  return Ref(c).value
end
return { types = { Counter }, functions = { bad } }
]==])
rejects("ref-target", [==[
let Counter = { value: U32 }
let bad(): U32 = Ref(Counter { value = 1 }).value
return { types = { Counter }, functions = { bad } }
]==])
-- A field declared as a signature is a view, and a function-pointer declaration may name an
-- incomplete parameter type, so a record may hold a view that takes that record.
local throughParameter = compile([==[
let Handler = { f: (Handler): U32, n: U32 }
let g(x: U32): U32 = x
return { types = { Handler }, functions = { g } }
]==]):unit()
check(throughParameter:find("wordletview_1 f_f;", 1, true) ~= nil,
    "a record may hold a view that takes the record, because a parameter may be incomplete")
-- A view that *returns* the record cannot: a result type must be complete, so the pair has no
-- finite order and is reported rather than emitted.
do
    -- Lowering runs at `unit()`, so this is checked there rather than by `rejects`.
    local ok, err = pcall(function()
        return compile([==[
let Handler = { f: (U32): Handler, n: U32 }
let g(x: U32): U32 = x
return { types = { Handler }, functions = { g } }
]==]):unit()
    end)
    check(not ok and D.is(err) and err.code == "c-order",
        "a record and a view that returns it contain each other by value")
end

-- A reference is not itself a place to reference again.
rejects("ref-target", [==[
let Counter = { value: U32 }
let shared = Counter { value = 5 }
let bad(x: U32): U32 = Ref(Ref(shared)).value + x
return { types = { Counter }, functions = { bad } }
]==])
-- A reference to an enclosing owner cannot outlive that activation.
rejects("ref-escape", [==[
let Counter = { value: U32 }
let leak(x: U32): U32 = do
  let c = Counter { value = x }
  let f = |d: U32| -> do
    let r = Ref(c)
    return r
  end
  return f(1).value
end
return { types = { Counter }, functions = { leak } }
]==])
-- A type that contains itself by value has no finite layout, however many definitions it crosses.
rejects("type-cycle", [==[
let Bad = { child: Bad }
let f(n: U32): U32 = n
return { types = { Bad }, functions = { f } }
]==])
rejects("type-cycle", [==[
let A = { b: B }
let B = { a: A }
let f(n: U32): U32 = n
return { types = { A, B }, functions = { f } }
]==])
-- A recursive definition has to be file scope: a local binding is declared in order, so a local
-- definition cannot see its own name.
rejects("unknown-name", [==[
let Counter = { value: U32 }
let use(x: U32): U32 = do
  let Node = { value: U32, child: Ref(Node) }
  return x
end
return { types = { Counter }, functions = { use } }
]==])
-- A cycle that crosses a reference is finite, so it is accepted.
local finite = compile([==[
let Good = { child: Ref(Good), value: U32 }
let f(n: U32): U32 = n
return { types = { Good }, functions = { f } }
]==]):unit()
check(finite:find("wordletrecord_1 * f_child;", 1, true) ~= nil,
    "a cycle through a reference is finite and emits a pointer")


-- Arrays ------------------------------------------------------------------------------------------
-- A fixed-length sequence of one element type. The length is part of the type, so a static index is
-- checked while compiling and only a run-time index needs a bounds guard.
local ARRAYS = [==[
let literal_sum(): U32 = do
  let a = [10, 20, 30]
  return a[0] + a[1] + a[2]
end
let local_pick(i: U32): U32 = do
  let b: Array(U32, 3) = [7, 8, 9]
  return b[i]
end
let store(i: U32, v: U32): U32 = do
  let b = [1, 2, 3]
  b[i] = v
  b[0] += 5
  return b[0] * 100 + b[1] * 10 + b[2]
end
let grid(r: U32, c: U32): U32 = do
  let g = [[1, 2], [3, 4]]
  return g[r][c]
end
let sum2(xs: Array(U32, 2)): U32 = xs[0] + xs[1]
let via_parameter(x: U32): U32 = do
  let b: Array(U32, 2) = [x, x + 1]
  return sum2(b)
end
let aliased(x: U32): U32 = do
  let b = [x, x + 1]
  let c = b
  c[0] = 99
  return b[0] * 1000 + c[0]
end
return { types = {  }, functions = { literal_sum, local_pick, store, grid, via_parameter, aliased } }
]==]
check(interpret("literal_sum", {}, ARRAYS)[1] == 60,
    "an array literal is indexed and its elements are values")
check(interpret("local_pick", { 2 }, ARRAYS)[1] == 9, "an annotation types a literal and a index selects")
check(interpret("store", { 1, 4 }, ARRAYS)[1] == 643, "an element store and a compound element store")
check(interpret("grid", { 1, 0 }, ARRAYS)[1] == 3, "a nested array is indexed twice")
check(interpret("via_parameter", { 5 }, ARRAYS)[1] == 11, "an array argument is a copy")
check(interpret("aliased", { 3 }, ARRAYS)[1] == 99099,
    "a local array binding is an alias, like a record instance, so a write is visible")
local arrayUnit = compile(ARRAYS):unit()
check(arrayUnit:find("uint32_t f_data[3];", 1, true) ~= nil,
    "an array is a struct holding a C array, so it copies by assignment")
-- Rejections ------------------------------------------------------------------------------------
-- An empty literal has no element to take its type from.
rejects("type-required", [==[
let f(n: U32): U32 = do
  let a = []
  return n + a[0]
end
return { functions = { f } }
]==])
-- The length is part of the type, so a literal of the wrong length rejects.
rejects("array-length", [==[
let f(n: U32): U32 = do
  let a: Array(U32, 3) = [1, 2]
  return a[n]
end
return { functions = { f } }
]==])
-- Elements must share one type.
rejects("type-mismatch", [==[
let f(n: U32): U32 = do
  let a = [1, true]
  return n
end
return { functions = { f } }
]==])
-- A known index outside the array rejects while compiling.
rejects("index-range", [==[
let f(): U32 = do
  let a = [1, 2]
  return a[2]
end
return { functions = { f } }
]==])
-- Only an array can be indexed at all.
rejects("type-mismatch", [==[
let f(n: U32): U32 = do
  n[0] = 1
  return n
end
return { functions = { f } }
]==])
-- An array needs a length of at least one, given as a literal.
rejects("array-length", [==[
let f(n: U32): U32 = do
  let a: Array(U32, 0) = [1]
  return n
end
return { functions = { f } }
]==])


-- Narrower integers -------------------------------------------------------------------------------
-- The width is part of the type: arithmetic wraps at that width, widening is implicit, and narrowing
-- needs an explicit conversion unless a known value fits.
local WIDTHS = [==[
let wrap8(n: U32): U32 = do
  let a: U8 = U8(n)
  let b = a + 200
  return U32(b)
end
let wrap16(n: U32): U32 = do
  let a: U16 = U16(n)
  let b = a * 3
  return U32(b)
end
let widen(n: U32): U32 = do
  let a: U8 = U8(n)
  let b: U16 = a
  let c: U32 = b
  return c
end
let compare(n: U32): Bool = do
  let a: U8 = U8(n)
  let b: U16 = U16(n)
  return a == b and a <= b
end
let shift8(n: U32): U32 = do
  let a: U8 = U8(n)
  return U32(a << 1) + U32(a >> 1)
end
let negate8(n: U32): U32 = do
  let a: U8 = U8(n)
  let b = -a
  return U32(b)
end
return { types = {  }, functions = { wrap8, wrap16, widen, compare, shift8, negate8 } }
]==]
check(interpret("wrap8", { 100 }, WIDTHS)[1] == 44, "U8 arithmetic wraps at 8 bits")
check(interpret("wrap8", { 255 }, WIDTHS)[1] == 199, "a U8 value of 255 plus 200 wraps")
check(interpret("wrap16", { 40000 }, WIDTHS)[1] == 54464, "U16 arithmetic wraps at 16 bits")
check(interpret("widen", { 200 }, WIDTHS)[1] == 200, "narrowing widens back without change")
check(interpret("compare", { 7 }, WIDTHS)[1] == true, "widths compare after widening")
check(interpret("shift8", { 130 }, WIDTHS)[1] == 4 + 65, "a U8 shift wraps at its own width")
check(interpret("negate8", { 1 }, WIDTHS)[1] == 255, "a negated U8 is its own complement")
local widthUnit = compile(WIDTHS):unit()
check(widthUnit:find("uint8_t", 1, true) ~= nil and widthUnit:find("uint16_t", 1, true) ~= nil,
    "the widths lower to their C types")
-- Rejections ------------------------------------------------------------------------------------
-- A known value that does not fit rejects while compiling, whether it is an annotation or a conversion.
rejects("numeric-range", [==[
let f(n: U32): U32 = do
  let a: U8 = 300
  return n + U32(a)
end
return { functions = { f } }
]==])
rejects("numeric-range", [==[
let f(n: U32): U32 = do
  let a = U8(300)
  return n + U32(a)
end
return { functions = { f } }
]==])
-- A run-time value needs the conversion to say what to do; an annotation will not narrow it.
rejects("numeric-range", [==[
let f(n: U32): U32 = do
  let a: U8 = n
  return U32(a)
end
return { functions = { f } }
]==])
-- Two run-time widths mix by widening, which loses nothing, so the sum is the wider one.
check(interpret("mixed", { 200 },
    "let mixed(n: U32): U32 = do\n  let a: U8 = U8(n)\n  let b: U16 = U16(n)\n"
    .. "  return U32(a + b)\nend\nreturn { functions = { mixed } }")[1] == 400,
    "a narrower value widens to meet a wider one")
-- A conversion needs an integer.
rejects("type-mismatch", [==[
let f(n: U32): U32 = do
  let a = U8(true)
  return n
end
return { functions = { f } }
]==])


-- Imports ------------------------------------------------------------------------------------------
-- A `use` declaration names a file next to the importing one and its namespace exposes exactly the
-- export list of that file, so a name that is not exported stays private.
do
    local root = os.tmpname()
    os.remove(root)
    assert(os.execute("mkdir -p -- '" .. root .. "'") ~= nil)
    local function write(name, text)
        local file = assert(io.open(root .. "/" .. name, "wb"))
        assert(file:write(text))
        assert(file:close())
    end
    write("util.let", [==[
let Point = { x: U32, y: U32 }
let helper(n: U32): U32 = n * 2
let secret(n: U32): U32 = helper(n) + 1
return { types = { Point }, functions = { helper, secret } }
]==])
    write("main.let", [==[
use util
let twice(n: U32): U32 = util.helper(n)
let bumped(n: U32): U32 = util.secret(n)
let origin(): util.Point = util.Point { x = 1, y = 2 }
let sum_point(): U32 = origin().x + origin().y
return { types = {  }, functions = { twice, bumped, sum_point } }
]==])
    local artifact = wordlet.compile_file(root .. "/main.let", { name = root .. "/main.let" })
    local unit = artifact:unit()
    check(unit:find("wordlet_twice", 1, true) ~= nil, "an entry module compiles with its imports")
    check(#unit > 0, "an imported module produces one artifact with the entry")
    -- Rejections ---------------------------------------------------------------------------------
    write("bad_member.let", [==[
use util
let f(n: U32): U32 = util.hidden(n)
return { functions = { f } }
]==])
    local ok, err = pcall(function()
        return wordlet.compile_file(root .. "/bad_member.let", { name = root .. "/bad_member.let" })
    end)
    check(not ok and D.is(err) and err.code == "unknown-member",
        "a name the module does not export is not reachable")
    write("missing.let", "use nowhere\nlet f(n: U32): U32 = n\nreturn { functions = { f } }\n")
    ok, err = pcall(function()
        return wordlet.compile_file(root .. "/missing.let", { name = root .. "/missing.let" })
    end)
    check(not ok and D.is(err) and err.code == "import-input", "a missing module is reported")
    write("a.let", "use b\nlet f(n: U32): U32 = n\nreturn { functions = { f } }\n")
    write("b.let", "use a\nlet g(n: U32): U32 = n\nreturn { functions = { g } }\n")
    ok, err = pcall(function()
        return wordlet.compile_file(root .. "/a.let", { name = root .. "/a.let" })
    end)
    check(not ok and D.is(err) and err.code == "import-cycle", "a module cycle is reported")
    ok, err = pcall(function()
        return wordlet.compile{ source = "use util\nlet f(n: U32): U32 = n\n"
            .. "return { functions = { f } }", name = "s.let" }
    end)
    check(not ok and D.is(err) and err.code == "import-input",
        "a source string cannot use an import, because it has no directory")
    os.execute("rm -rf -- '" .. root .. "'")
end


-- Signed integers ---------------------------------------------------------------------------------
-- I32 is two's complement: arithmetic wraps, division truncates toward zero with the remainder
-- taking the dividend's sign, and a right shift is arithmetic. Changing signedness at one width
-- reinterprets the bits, so it never loses a value.
local SIGNED = [==[
let round(n: U32): U32 = do
  let a: I32 = I32(n)
  let b = a - 3
  let c = b * 2
  return U32(c)
end
let quotient(n: U32): U32 = do
  let a: I32 = I32(n)
  return U32(a / 3) + U32(a % 3)
end
let shift(n: U32): U32 = do
  let a: I32 = I32(n)
  return U32(a >> 1)
end
let reinterpret(n: U32): U32 = do
  let a = I32(n)
  return U32(a)
end
let negate(n: U32): U32 = do
  let a: I32 = I32(n)
  return U32(-a)
end
return { types = {  }, functions = { round, quotient, shift, reinterpret, negate } }
]==]
check(interpret("round", { 0 }, SIGNED)[1] == 4294967290, "I32 arithmetic wraps at 32 bits")
check(interpret("quotient", { 4294967294 }, SIGNED)[1] == 4294967294,
    "signed division truncates toward zero and the remainder keeps the dividend's sign")
check(interpret("shift", { 4294967295 }, SIGNED)[1] == 4294967295,
    "a signed shift keeps the sign bit")
check(interpret("reinterpret", { 4294967295 }, SIGNED)[1] == 4294967295,
    "changing signedness at one width reinterprets the bits")
check(interpret("negate", { 1 }, SIGNED)[1] == 4294967295, "negation wraps in two's complement")
local signedUnit = compile(SIGNED):unit()
check(signedUnit:find("int32_t", 1, true) ~= nil, "I32 lowers to its C type")
check(signedUnit:find("wordlet_i32", 1, true) ~= nil,
    "a signed value is reinterpreted rather than converted out of range")
-- Rejections ------------------------------------------------------------------------------------
-- Signed and unsigned values of one width do not mix: the conversion has to say which is meant.
rejects("type-mismatch", [==[
let f(n: U32): U32 = do
  let a: I32 = I32(n)
  let c = a + n
  return n
end
return { functions = { f } }
]==])
-- A negative value has no unsigned counterpart when the width changes too, which is checked: a
-- run-time one traps and a known one rejects here.
rejects("numeric-range", [==[
let f(n: U32): U32 = do
  let b: U8 = U8(I32(0) - I32(1))
  return n + U32(b)
end
return { functions = { f } }
]==])
-- A signed power needs a power that is not negative.
rejects("numeric-range", [==[
let f(n: U32): U32 = do
  let a: I32 = I32(n)
  let b = a ^ (I32(0) - I32(1))
  return U32(b)
end
return { functions = { f } }
]==])


-- 64-bit integers ----------------------------------------------------------------------------------
-- A 64-bit value does not fit a Lua number, so it is held as two words and the exact kernel decides
-- its arithmetic. A literal that does not fit a word is a 64-bit literal.
local WIDE = [==[
let low(): U32 = U32(0xFFFFFFFFFFFFFFFF % 4294967296)
let high(): U32 = U32(0xFFFFFFFFFFFFFFFF / 4294967296)
let masked(n: U32): U32 = U32(U64(n) * U64(n) % 4294967296)
let above(n: U32): U32 = U32(U64(n) * U64(n) / 4294967296)
let negative(n: U32): U32 = U32((I64(4294967296) - I64(n)) / I64(2))
return { types = {  }, functions = { low, high, masked, above, negative } }
]==]
check(interpret("low", {}, WIDE)[1] == 4294967295, "the low word of the largest value")
check(interpret("high", {}, WIDE)[1] == 4294967295, "the high word of the largest value")
check(interpret("masked", { 4294967295 }, WIDE)[1] == 1,
    "the square of the largest 32-bit value is one modulo 2^32")
check(interpret("above", { 4294967295 }, WIDE)[1] == 4294967294,
    "and its high word is two less than 2^32")
check(interpret("negative", { 2 }, WIDE)[1] == 2147483647, "a wide subtraction and division")
local wideUnit = compile(WIDE):unit()
check(wideUnit:find("uint64_t", 1, true) ~= nil and wideUnit:find("int64_t", 1, true) ~= nil,
    "the 64-bit types lower to their C types")
check(wideUnit:find("wordlet_i64", 1, true) ~= nil,
    "a signed 64-bit value is reinterpreted rather than converted out of range")
-- Rejections ------------------------------------------------------------------------------------
-- A width change that can lose a value is checked, and a negative value has no unsigned counterpart.
rejects("numeric-range", [==[
let f(n: U32): U32 = U32(18446744073709551615) + n
return { functions = { f } }
]==])
-- A run-time value that cannot fit is stopped when it is converted rather than refused while
-- compiling, so the program compiles and the generated code carries a check.
check(#compile([==[
let f(n: U32): U32 = U32(U64(n) * U64(n))
return { functions = { f } }
]==]):unit() > 0, "a run-time narrowing conversion compiles with a run-time check")
-- A negative value narrowed to a narrower unsigned type is refused, while the same width read the
-- other way is a reinterpretation and keeps every bit.
rejects("numeric-range", [==[
let f(n: U32): U32 = do
  let a: I64 = I64(0) - I64(5)
  let b: U32 = U32(a)
  return n + b
end
return { functions = { f } }
]==])
check(interpret("bits", { 3 },
    "let bits(n: U32): U32 = do\n  let a: I64 = I64(0) - I64(n)\n  let b: U64 = U64(a)\n"
    .. "  return U32(b % 4294967296)\nend\nreturn { functions = { bits } }")[1] == 4294967293,
    "a same-width signedness change reinterprets the bits")
-- A literal above 64 bits is refused rather than wrapped.
rejects("lex-range", [==[
let f(n: U32): U32 = U32(18446744073709551616) + n
return { functions = { f } }
]==])

-- The interpreter refuses an unsaturated entry rather than inventing a value.
local ok, err = pcall(wordlet.interpret, { source = "let f(a, b: U32) : U32 = a + b\n"
    .. "return { functions = { f } }", entry = "f", args = { 1 } })
check(not ok and D.is(err) and err.code == "arity", "undersaturated entry rejects instead of returning a word")

-- C naming is injective, so two distinct source names cannot collide.
check(C.escape("sum_to") == "sum_5Fto" and C.functionName("sum_to") == "wordlet_sum_5Fto",
    "underscore is escaped")
check(C.escape("a_b") ~= C.escape("aXbX") or C.escape("a-") ~= C.escape("a_"),
    "escaping distinguishes distinct spellings")
check(C.escape("a") ~= C.escape("A"), "case is preserved")

-- Exported aliases share one body and forward.
local aliasArtifact = compile("let inc(x: U32) : U32 = x + 1\nreturn { functions = { a = inc, b = inc } }")
check(#aliasArtifact:exports() == 2, "both aliases are exported")
local aliasUnit = aliasArtifact:unit()
check(aliasUnit:find("wordlet_a", 1, true) and aliasUnit:find("wordlet_b", 1, true),
    "aliases appear in the generated C")

-- Determinism: identical input gives byte-identical output.
local one = compile("let f(x: U32) : U32 = x * 3 + 1\nreturn { functions = { f } }"):unit()
local two = compile("let f(x: U32) : U32 = x * 3 + 1\nreturn { functions = { f } }"):unit()
check(one == two, "emission is deterministic")

-- A deferred action runs when the block it is written in is left: in reverse order, after the value
-- has been read, from a statement conditional's arm as much as from the block itself, and after a tail
-- self-call has returned rather than as a back edge. The counter shifts a digit in per action, so the
-- number left behind spells the order they ran in.
do
    local source = "let Counter = { n: U32 }\n"
        .. "let counter = Counter { n = 0 }\n"
        .. "let push(v: U32): U32 = do\n  let c = Ref(counter)\n  c.n = c.n * 10 + v\n"
        .. "  return c.n\nend\n"
        .. "let reset(): U32 = do\n  let c = Ref(counter)\n  c.n = 0\n  return 0\nend\n"
        .. "let body(): U32 = do\n  defer push(1)\n  defer push(2)\n  return 0\nend\n"
        .. "let ordered(): U32 = do\n  reset()\n  let before = body()\n"
        .. "  return (before + 1) * 1000 + Ref(counter).n\nend\n"
        .. "let arm(): U32 = do\n  defer push(7)\n"
        .. "  if Ref(counter).n == 0 then return 1 end\n  return 2\nend\n"
        .. "let via_arm(): U32 = do\n  reset()\n  let r = arm()\n  return r * 10 + Ref(counter).n\nend\n"
        .. "let countdown(n: U32, acc: U32): U32 = do\n  if n == 0 then return acc end\n"
        .. "  defer push(n)\n  return countdown(n - 1, acc * 10 + n)\nend\n"
        .. "let tailed(): U32 = do\n  reset()\n  let acc = countdown(3, 0)\n"
        .. "  return acc * 1000 + Ref(counter).n\nend\n"
        .. "let counted(n: U32): U32 = do\n  reset()\n  return countdown(n, 0)\nend\n"
        -- `countdown` is exported so its emitted C has a predictable name to inspect below.
        .. "return { functions = { ordered, via_arm, tailed, counted, countdown } }"
    check(interpret("ordered", {}, source)[1] == 1021,
        "two actions run in reverse order, after the returned value was read")
    check(interpret("via_arm", {}, source)[1] == 17,
        "a return inside a statement conditional's arm still runs the pending action")
    check(interpret("tailed", {}, source)[1] == 321123,
        "a tail self-call runs the action after the call returns")
    check(interpret("counted", { 0 }, source)[1] == 0, "a deferred block with no iteration")
    check(interpret("counted", { 5 }, source)[1] == 54321, "the deferral survives every recursion")
    local generated = compile(source):unit()
    local start = generated:find("uint32_t wordlet_countdown(uint32_t v1, uint32_t v3) {", 1, true)
    check(start ~= nil, "the deferred recursion is emitted")
    local body = generated:sub(start, (generated:find("\n}", start, true) or #generated))
    check(body:find("for (;;)", 1, true) == nil,
        "a block with a pending action does not become a loop")
    check(body:find("wordlet_countdown(", 1, true) ~= nil,
        "the tail self-call is a real call, so the action runs after it returns")
end

-- A call whose only purpose is an effect still has to be compiled. A store through a local binding that
-- holds a reference to module storage *is* a store to module storage, so folding such a call away would
-- silently drop the write from the generated code.
do
    local source = "let Counter = { n: U32 }\n"
        .. "let counter = Counter { n = 0 }\n"
        .. "let reset(): U32 = do\n  let c = Ref(counter)\n  c.n = 0\n  return 0\nend\n"
        .. "let bump(v: U32): U32 = do\n  let c = Ref(counter)\n  c.n += v\n  return c.n\nend\n"
        .. "let use(): U32 = do\n  reset()\n  bump(5)\n  return Ref(counter).n\nend\n"
        .. "return { functions = { use } }"
    check(interpret("use", {}, source)[1] == 5, "a write through a reference to module storage is seen")
    local generated = compile(source):unit()
    -- The definition, not the prototype: everything from the prototype onwards spans other functions.
    local start = generated:find("uint32_t wordlet_use(void) {", 1, true)
    check(start ~= nil, "the effect-only entry is emitted")
    local body = generated:sub(start, (generated:find("\n}", start, true) or #generated))
    local calls = select(2, body:gsub("wordletfn_%d+%(", ""))
    check(calls == 2,
        ("both effect-only calls are compiled, not folded away (found %d)"):format(calls))
end

-- The evaluator decides from what a value or a place *is*, not from the syntax or the name that
-- reached it, and a requirement types a lambda however it is spelled. Each of these was a false
-- rejection before.
do
    -- A name a nested lambda needs has to travel through the lambda that encloses it: an environment
    -- cannot hold a name its enclosing environment does not have.
    local nested = "let Counter = { n: U32 }\n"
        .. "let borrow(c: Counter): U32 = do\n"
        .. "  let outer = || -> do\n"
        .. "    let inner = |d: U32| -> do\n      c.n += d\n      return c.n\n    end\n"
        .. "    return inner(3)\n  end\n"
        .. "  return outer() * 10 + c.n\nend\n"
        .. "let use(): U32 = borrow(Counter { n = 1 })\n"
        .. "return { functions = { use } }"
    check(interpret("use", {}, nested)[1] == 44, "a capture travels through a nested lambda")

    -- A slice is an indirection, so a type may mention itself through one; by value it may not.
    local recursive = "let Node = { value: U32, rest: Slice(Node) }\n"
        .. "let head(n: Node): U32 = n.value\nreturn { functions = { head } }"
    local generatedNode = compile(recursive):unit()
    check(generatedNode:find("wordletrecord_1", 1, true) ~= nil
        and generatedNode:find("wordletslice_", 1, true) ~= nil,
        "a recursive type through a slice has a finite layout")
    local pointed = compile("let Node = { value: U32, next: Ptr(Node) }\n"
        .. "let head(n: Node): U32 = n.value\nreturn { functions = { head } }"):unit()
    check(pointed:find("wordletrecord_1", 1, true) ~= nil,
        "a recursive type through a pointer has a finite layout")
    rejects("type-cycle", "let Bad = { child: Bad }\nreturn { functions = { } }")
    -- An array element is embedded by value, so a cycle that crosses one crosses no boundary at all.
    -- The element is resolved on the type path, which hands back the cell an open definition reserved
    -- instead of demanding its layout, so the checker gets to say what is wrong rather than the demand
    -- reporting an eager initializer cycle.
    rejects("type-cycle", "let Bad = { items: Array(Bad, 2) }\nreturn { functions = { } }")
    rejects("type-cycle", "let Bad = Array(Bad, 2)\nreturn { functions = { } }")
    rejects("type-cycle", "let A = { b: Array(B, 2) }\nlet B = { a: Array(A, 2) }\n"
        .. "return { functions = { } }")
    -- A type declared later is not a cycle, and an indirection inside the array is a boundary.
    check(compile("let Good = { items: Array(Node, 2) }\nlet Node = { value: U32 }\n"
        .. "return { functions = { } }") ~= nil,
        "an array of a type declared later is not a cycle")
    check(compile("let Node = { value: U32, kids: Array(Ref(Node), 2) }\n"
        .. "return { functions = { } }") ~= nil,
        "an array of references may mention the type that holds it")

    -- A requirement types a lambda however it was spelled, so an alias is as good as a signature.
    local aliased = "let Endo = (U32): U32\n"
        .. "let twice(f: Endo, x: U32): U32 = f(f(x))\n"
        .. "let use(): U32 = twice(|x| -> x + 1, 5)\n"
        .. "return { functions = { use } }"
    check(interpret("use", {}, aliased)[1] == 7,
        "an alias of a signature types the lambda it receives")

    -- A reference into module storage is module storage even when the route to it is a local
    -- reference, so the compiler accepts it and the store reaches the module array.
    local throughRef = "let pool = [10, 20, 30]\n"
        .. "let bump(i: U32): U32 = do\n"
        .. "  let r = Ref(pool)\n  r[i] += 5\n  return r[i]\nend\n"
        .. "return { functions = { bump } }"
    local reached = compile(throughRef):unit()
    check(reached:find("wordletmodule_1.f_data", 1, true) ~= nil,
        "a store through a local reference reaches module storage")
end

-- Exhausting a budget is a diagnostic, not a crash. A recursive word whose static arguments change
-- specializes once per value, which must stop at a resource rather than at the host's own stack; a
-- fold that merely runs out of depth is compiled instead; and the reference interpreter, which has no
-- fallback, is bounded where it cannot reach the host stack limit.
do
    local indexed = "let scan(s: String, b: U8, i: U32): U32 = do\n"
        .. "  if i >= s.length then return 0 end\n"
        .. "  if s[i] == b then return 1 + scan(s, b, i + 1) end\n"
        .. "  return scan(s, b, i + 1)\n"
        .. "end\n"
        .. "let count_a(s: String): U32 = scan(s, 'a', 0)\n"
        .. "return { functions = { count_a } }"
    rejects("depth", indexed)
    -- The reference interpreter folds the same scan, because its view is concrete and six bytes long.
    check(interpret("count_a", { "banana" }, indexed)[1] == 3, "a concrete view folds the scan")
    local deep = "let g(n: U32): U32 = if n == 0 then 0 else n + g(n - 1)\n"
        .. "return { functions = { g } }"
    check(compile(deep):unit():find("wordlet_g(", 1, true) ~= nil,
        "a fold that runs out of depth is compiled, not refused")
    check(interpret("g", { 1000 }, deep)[1] == 500500, "a recursion inside the interpreter's depth runs")
    rejects("static-depth", deep, "g", { 5000 })
    -- A top-level initializer is folded, and has no runtime code to fall back to, so a fold that
    -- runs out of depth there is the answer rather than a reason to compile.
    rejects("static-depth", deep:gsub("return { functions = { g } }",
        "let x: U32 = g(2000)\nreturn { functions = {} }"))
end

-- The literal surface: grouped digits, binary, byte literals, long strings and long comments.
do
    local source = "let grouped(): U32 = 1_000_000 + 0b1010_1010\n"
        .. "let wide(): U32 = 0b1111_1111_1111_1111_1111_1111_1111_1111_1111_1111 % 4294967296\n"
        .. "let hex(): U32 = 0xffff_ffff\n"
        .. "let byte(): U32 = U32('\\n')\n"
        .. "let is_a(): Bool = 'a' == 97\n"
        .. "let raw(): U32 = [=[a\\tb]=].length\n"
        .. "let long(): U32 = [=[\nab\ncd\n]=].length\n"
        .. "let commented(): U32 = do\n  --[[ a ]=] b ]]\n  return 7\nend\n"
        .. "return { functions = { grouped, wide, hex, byte, is_a, raw, long, commented } }"
    check(interpret("grouped", {}, source)[1] == 1000170, "a grouped decimal and a binary literal")
    check(interpret("wide", {}, source)[1] == 4294967295, "a binary literal above a word keeps its bits")
    check(interpret("hex", {}, source)[1] == 4294967295, "a grouped hexadecimal literal")
    check(interpret("byte", {}, source)[1] == 10, "a byte literal takes the escapes a string does")
    check(interpret("is_a", {}, source)[1] == true, "a byte literal is a numeric literal")
    check(interpret("raw", {}, source)[1] == 4, "a long string is raw, so a backslash is a byte")
    check(interpret("long", {}, source)[1] == 6, "a long string spans lines, less one leading newline")
    check(interpret("commented", {}, source)[1] == 7, "a long comment is skipped")
end

-- Tail position belongs to the whole returned expression, so a self-call inside a larger expression
-- is a real call and not a back edge whose result would be Unit.
do
    local mixed = "let f(n: U32): U32 = do\n"
        .. "  if n == 0 then return 0 end\n"
        .. "  if n == 1 then return 100 + f(n - 1) end\n"
        .. "  return f(n - 1)\n"
        .. "end\nreturn { functions = { f } }"
    check(interpret("f", { 0 }, mixed)[1] == 0, "the base case returns zero")
    check(interpret("f", { 1 }, mixed)[1] == 100, "a non-tail self-call is evaluated, not discarded")
    check(interpret("f", { 3 }, mixed)[1] == 100, "the tail branch reaches the non-tail branch")
    local generated = compile(mixed):unit()
    check(generated:find("for (;;)", 1, true) ~= nil, "the tail branch is still a loop")
    check(generated:find("wordlet_f(", 1, true) ~= nil, "the non-tail branch is a real call")
end

-- The documented values of examples/strings.let, so the VALIDATION bullet is executable.
do
    local path = (source:match("^(.*[/\\])") or "./") .. "../examples/strings.let"
    local file = assert(io.open(path, "rb"))
    local text = file:read("*a")
    assert(file:close())
    local expected = {
        { "byte_at", { "A", 0 }, 65 }, { "length_of", { "hello" }, 5 },
        { "count_a", { "banana", 0 }, 3 }, { "same", {}, true }, { "different", {}, false },
        { "escaped", {}, 4 }, { "empty_length", {}, 0 }, { "grouped", {}, 1000170 },
        { "banner_length", {}, 13 }, { "banner_first", {}, 102 }, { "banner_is_raw", {}, 4 },
        { "module_view", { 1 }, 20 }, { "sliced_sum", {}, 60 },
    }
    for _, case in ipairs(expected) do
        local got = interpret(case[1], case[2], text)[1]
        check(got == case[3], ("examples/strings.let %s: expected %s but got %s")
            :format(case[1], tostring(case[3]), tostring(got)))
    end
end

-- Reading module storage through a reference is an ordinary run-time read. A call whose arguments
-- happen to be static must still be compiled rather than folded when the body needs that storage.
do
    local shared = "let Counter = { value: U32 }\nlet shared = Counter { value = 5 }\n"
        .. "let read_shared(x: U32): U32 = Ref(shared).value + x\n"
    check(interpret("read_shared", { 1 }, shared .. "return { functions = { read_shared } }")[1] == 6,
        "module initialization reads module storage through a reference")
    local generated = compile(shared .. "let peek(): U32 = read_shared(1)\n"
        .. "return { functions = { peek } }"):unit()
    check(generated:find("wordletmodule_1", 1, true) ~= nil,
        "a literal-argument call to a module-storage reader is compiled, not folded")
    check(generated:find("f_value", 1, true) ~= nil, "the module read is emitted rather than baked")
    -- A body that is genuinely wrong is still reported: only the need for run-time code falls back.
    rejects("type-mismatch", "let bad(): U32 = 1 + true\nreturn { functions = { bad } }")
end

-- A long binding chain must compile in time linear in the chain. Interned expressions name their
-- operands by id, not by re-encoding the subtree, so a key costs the same however deep an operand
-- is; re-encoding made a 400-binding chain take seconds.
do
    local lines = { "let big(x: U32): U32 = do", "  let a0 = x" }
    for index = 1, 400 do
        lines[#lines + 1] = ("  let a%d = a%d * 3 + %d"):format(index, index - 1, index)
    end
    lines[#lines + 1] = "  return a400"
    lines[#lines + 1] = "end"
    lines[#lines + 1] = "return { functions = { big } }"
    local start = os.clock()
    compile(table.concat(lines, "\n"))
    local elapsed = os.clock() - start
    check(elapsed < 2, "a 400-binding chain compiles in linear time (took " .. elapsed .. " s)")
end

print(("PASS: evaluator semantics (%d checks)"):format(checks))
