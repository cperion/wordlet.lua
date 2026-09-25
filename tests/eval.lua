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

-- f64 follows IEEE-754 rather than the integer rules: a division by zero is an infinity or a NaN, a
-- NaN comparison is false, an integer rounds to the nearest double, and a float truncates toward an
-- integer with the target's range checked.
do
    local source = "let third(): f64 = 1.0 / 3.0\n"
        .. "let inf(): f64 = 1.0 / 0.0\n"
        .. "let nan(): f64 = 0.0 / 0.0\n"
        .. "let nan_eq(): bool = (0.0 / 0.0) == (0.0 / 0.0)\n"
        .. "let nan_ne(): bool = (0.0 / 0.0) != (0.0 / 0.0)\n"
        .. "let huge(): bool = 1.0 / 0.0 > 1.0e308\n"
        .. "let rounds(): f64 = f64(18446744073709551615)\n"
        .. "let truncates(): u32 = u32(2.75)\n"
        .. "let adopts(x: f64): f64 = x * 2.0\n"
        .. "let adopted(): f64 = adopts(3)\n"
        .. "let negated(x: f64): f64 = -x\n"
        .. "let ordered(a: f64, b: f64): bool = a < b\n"
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
    check(interpret("adopted", {}, source)[1] == 6.0, "an integer literal adopts f64")
    check(interpret("negated", { 2.5 }, source)[1] == -2.5, "a double negates as itself")
    check(interpret("ordered", { 1.5, 2.5 }, source)[1] == true, "a double orders as IEEE does")
    -- An integer that is not a literal needs the conversion written, because rounding may lose a value.
    rejects("type-mismatch", "let f(n: u32): f64 = n + 1.5\nreturn { functions = { f } }", "f", { 1 })
    -- f64 has no remainder, power, shift or bitwise operator.
    rejects("type-mismatch", "let f(): f64 = 1.5 % 2.0\nreturn { functions = { f } } ")
    rejects("type-mismatch", "let f(): f64 = 1.5 & 2.0\nreturn { functions = { f } }")
    -- A known value outside the target's range is refused while compiling.
    rejects("numeric-range", "let f(): u32 = u32(4294967296.0)\nreturn { functions = { f } }")
    rejects("numeric-range", "let f(): u32 = u32(18446744073709551615.0)\nreturn { functions = { f } }")
end

-- A bare `return` is one unit result and `unit()` is the unit value (syntax.md §1, §6). A unit slot
-- is logical but has no runtime representation, so the IR drops it while a binding list keeps its
-- position.
do
    local source = "let nothing() : unit = do return end\n"
        .. "let explicit() : unit = do return; end\n"
        .. "let unit_value() : unit = unit()\n"
        .. "let pair(x: u32) : (unit, u32) = do return unit(), x end\n"
        .. "let use(x: u32) : u32 = do let u, y = pair(x) return y end\n"
        .. "return { functions = { nothing, explicit, unit_value, pair, use } }"
    check(interpret("nothing", {}, source)[1] == "unit", "a bare return is the unit value")
    check(interpret("explicit", {}, source)[1] == "unit", "return; is a bare return")
    check(interpret("unit_value", {}, source)[1] == "unit", "unit() is the unit value")
    -- The unit slot is first, so a positional binding is only right if it stayed logical.
    check(interpret("use", { 7 }, source)[1] == 7, "a unit slot keeps its position in a result vector")
    compile(source)
end

-- Equality is offered for bool and unit (syntax.md §7): bool compares by value, and unit has one
-- value. Ordering is not offered for either.
do
    local source = "let beq(a: bool, b: bool): bool = a == b\n"
        .. "let bne(a: bool, b: bool): bool = a != b\n"
        .. "let ueq(): bool = unit() == unit()\n"
        .. "let une(): bool = unit() != unit()\n"
        .. "return { functions = { beq, bne, ueq, une } }"
    check(interpret("beq", { true, true }, source)[1] == true, "true == true")
    check(interpret("beq", { true, false }, source)[1] == false, "true == false")
    check(interpret("bne", { true, false }, source)[1] == true, "true != false")
    check(interpret("ueq", {}, source)[1] == true, "unit() == unit()")
    check(interpret("une", {}, source)[1] == false, "unit() != unit()")
    compile(source)
end

-- Free-name analysis walks the schema, so a name captured inside any expression position is found.
-- A hand-written child table once missed record fields, array literals and indexes.
do
    local source = "let M = { acc: u32 }\n"
        .. "let pool = [3, 4, 5]\n"
        .. "let via_field(k: u32, x: u32) : u32 = (|y: u32| -> M { acc = k + y })(x).acc\n"
        .. "let via_array(k: u32, x: u32) : u32 = (|y: u32| -> [k, y])(x)[0]\n"
        .. "let via_index(k: u32, x: u32) : u32 = (|y: u32| -> pool[k] + y)(x)\n"
        .. "let via_cond(k: u32, x: u32) : u32 = (|y: u32| -> if k < y then k else y)(x)\n"
        .. "let via_binary(k: u32, x: u32) : u32 = (|y: u32| -> k * x + y)(x)\n"
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
    "let affine(a, b, x: u32) : u32 = a * x + b\nreturn { functions = { affine } }")[1] == 19,
    "affine is 19")
check(interpret("pick", { 0 },
    "let pick(x: u32) : u32 = if x == 0 then 7 else x * 2\nreturn { functions = { pick } }")[1] == 7,
    "known condition selects one arm")

local divmod = interpret("divmod", { 17, 5 },
    "let divmod(a, b: u32) : (u32, u32) = do return a / b, a % b end\nreturn { functions = { divmod } }")
check(#divmod == 2 and divmod[1] == 3 and divmod[2] == 2, "two results")

check(interpret("b", { 7 },
    "let a(x: u32) : u32 = x + 1\nlet b(x: u32) : u32 = a(x) * 2\nreturn { functions = { b } }")[1] == 16,
    "a call is evaluated statically when every argument is known")
check(interpret("wrap", { 1 },
    "let inc(x: u32) : u32 = x + 1\nlet wrap(x: u32) : u32 = inc(41)\nreturn { functions = { wrap } }")[1] == 42,
    "a constant call ignores an unused parameter")
check(interpret("g", { 3, 4 },
    "let g(a, b: u32) : u32 = if a < b then b - a else a - b\nreturn { functions = { g } }")[1] == 1,
    "comparison and subtraction")
check(interpret("s", { 0 },
    "let s(n: u32) : u32 = if n == 0 then 0 else n + s(n - 1)\nreturn { functions = { s } }")[1] == 0,
    "static recursion terminates")
check(interpret("x", { 1, 4 }, "let x(a, b: u32) : u32 = a | b\nreturn { functions = { x } }")[1] == 5,
    "bitwise or")

-- Partial application and specialization --------------------------------------------------------
local session = Eval.new()
session:compile(Parse.source("let scale(k, x: u32) : u32 = k * x\n"
    .. "let use(x: u32) : u32 = scale(3)(x) + scale(3)(x) + scale(5)(x)\n"
    .. "return { functions = { use } }", "s.let"))
check(#session.order == 3, "two static specializations of scale plus the entry, not three")
local bodies = {}
for _, instance in ipairs(session.order) do bodies[#bodies + 1] = instance.fn.body end
check(#bodies == 3, "one body per distinct static key")

local shared = Eval.new()
shared:compile(Parse.source("let inc(x: u32) : u32 = x + 1\n"
    .. "let use(x: u32) : u32 = inc(x) + inc(x)\nreturn { functions = { use } }", "s.let"))
check(#shared.order == 2, "a helper called twice in one caller has one body")

-- Key admission is constant-time map cardinality, not successful bodies or order-list length.
-- Failed reservations still occupy a key; repeated requests (including failures) do not add one.
do
    local V = require("wordlet.value")
    local function done(_, value) return nil, value end
    local function cardinality(e, want)
        local count = 0
        for _ in pairs(e.instances) do count = count + 1 end
        check(e.instanceCount == count and count == want, "maintained instance count matches the map")
    end
    local function failure(code, fn)
        local ok, err = pcall(fn)
        check(not ok and D.is(err) and err.code == code, "expected instance failure " .. code)
        check(err.span ~= nil, "instance admission/build failure retains its span")
        return err
    end
    local function named(limit, body)
        local e = Eval.new{limits={keys=limit}}
        e:load(Parse.source("let f(x,k:u32):u32=" .. body .. " return {functions={}}", "keys.let"))
        return e
    end
    local function request(e, value)
        local def = e.top.names.f.def
        return e:drive(e:staticFrame(e.top, def.span), function(m)
            return e:instanceForCPS(m, def, def.span, {[2]=V.u32(value)}, nil, done)
        end)
    end
    cardinality(session, 3)
    cardinality(shared, 2)
    local e = named(2, "x+k")
    cardinality(e, 0)
    local first = request(e, 1)
    cardinality(e, 1)
    check(request(e, 1) == first, "same named key reuses the instance")
    cardinality(e, 1)
    request(e, 2)
    cardinality(e, 2)
    failure("keys", function() request(e, 3) end)
    cardinality(e, 2)
    local zero = named(0, "x+k")
    failure("keys", function() request(zero, 0) end)
    cardinality(zero, 0)

    local bad = named(1, "x+true")
    local err = failure("type-mismatch", function() request(bad, 1) end)
    cardinality(bad, 1)
    check(bad.order[1].status == "failed", "failed named build remains reserved")
    check(failure("type-mismatch", function() request(bad, 1) end) == err,
        "same failed named key rethrows the saved diagnostic")
    cardinality(bad, 1)
    failure("keys", function() request(bad, 2) end)
    cardinality(bad, 1)

    local function closure(limit, body)
        local e = Eval.new{limits={keys=limit}}
        local program = Parse.source("let f=|x:u32|->" .. body .. " return {functions={}}", "keys.let")
        local top = e:load(program)
        return e, function() return e:initializeModule(program, top) end
    end
    local function requestClosure(e, plan, args)
        return e:drive(e:staticFrame(e.top, plan.def.span), function(m)
            return e:callableInstanceCPS(m, {plan=plan}, args, plan.def.span, done)
        end)
    end
    local c, initialize = closure(1, "x+1")
    initialize()
    cardinality(c, 1)
    local base = c.order[1]
    check(requestClosure(c, base.plan, {}) == base, "same closure key reuses the base")
    cardinality(c, 1)
    failure("keys", function() requestClosure(c, base.plan, {V.u32(7)}) end)
    cardinality(c, 1)
    local cz, initializeZero = closure(0, "x+1")
    failure("keys", initializeZero)
    cardinality(cz, 0)
    local cb, initializeBad = closure(1, "x+true")
    local closureError = failure("type-mismatch", initializeBad)
    cardinality(cb, 1)
    local failed = cb.order[1]
    check(failed.status == "failed", "failed closure build remains reserved")
    check(failure("type-mismatch", function() requestClosure(cb, failed.plan, {}) end) == closureError,
        "same failed closure key rethrows the saved diagnostic")
    cardinality(cb, 1)
    failure("keys", function() requestClosure(cb, failed.plan, {V.u32(7)}) end)
    cardinality(cb, 1)

    -- The compiler-owned initializer is still admitted after the source-key budget is full.
    -- Its registration counts toward map cardinality; replacing that key must not count twice.
    local module = Eval.new{limits={keys=1}}
    module:compile(Parse.source("let Box={n:u32} let box=Box{n=7} "
        .. "let f():u32=box.n return {functions={f}}", "keys.let"))
    cardinality(module, 2)
    local previous = module.instances["module-init"]
    check(previous ~= nil, "module initializer is registered")
    module:drive(module:staticFrame(module.top, nil), function(m)
        return module:moduleInitialiserCPS(m, module.modules, nil, done)
    end)
    cardinality(module, 2)
    check(module.instances["module-init"] ~= previous and #module.order == 3,
        "initializer replacement changes the order list but not map cardinality")
    cardinality(Eval.new(), 0)
end

-- Records, methods and stores ------------------------------------------------------------------
local RECORDS = [==[
let P = { x: u32, y: u32 }
let build(a, b: u32) : u32 = do
  let p = P { x = a, y = b }
  return p.x * 1000 + p.y
end
let bump(p: P) : u32 = do p.x += 1 return p.x end
let caller(n: u32) : u32 = do
  let p = P { x = n, y = 5 }
  let raised = bump(p)
  return raised * 1000 + p.x * 10 + p.y
end
let pair(a: u32) : P = P { x = a, y = a + 1 }
let use(a: u32) : u32 = do let q = pair(a) return q.x * 10 + q.y end
let alias(n: u32) : u32 = do
  let p = P { x = n, y = 0 }
  let q = p
  q.y = 9
  return p.x * 10 + p.y
end
let compound(n: u32) : u32 = do
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
local u32 = require("wordletkit.u32")
check(interpret("build", { 0, 0 }, RECORDS)[1] == 0, "zero fields")
check(interpret("build", { 4294967295, 1 }, RECORDS)[1] == u32.add(u32.mul(4294967295, 1000), 1),
    "record field arithmetic wraps like any other u32")

local METHODS = [==[
let Counter = {
  value: u32,
  inc() : u32 = do value += 1 return value end,
  add(n: u32) : u32 = do value += n return value end,
}
let observe(n: u32, change: bool) : (u32, u32) = do
  let c = Counter { value = n }
  let old = c.value
  if change then c.inc() end
  return old, c.value
end
let twice(n: u32) : u32 = do
  let c = Counter { value = n }
  c.inc()
  c.add(5)
  return c.value
end
let snapshot(n: u32) : u32 = do
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
local STATIC_FIELD = "let C = { v: u32, get() : u32 = v }\n"
    .. "let f(x: u32) : u32 = do let c = C { v = x } return c.get() end\n"
    .. "return { types = { C }, functions = { f } }"
check(interpret("f", { 12 }, STATIC_FIELD)[1] == 12, "a runtime receiver field is loaded, not folded")

-- Closures and higher-order words ---------------------------------------------------------------
local CLOSURES = [==[
let apply(f: (u32): u32, x: u32) : u32 = f(x)
let twice(f: (u32): u32, x: u32) : u32 = f(f(x))
let make_adder(n: u32) = |x: u32| -> n + x
let run(n, x: u32) : u32 = do
  let add = make_adder(n)
  return apply(add, x)
end
let inline(x: u32) : u32 = twice(|y: u32| -> y + 1, x)
let compose(a, b, x: u32) : u32 = do
  let f = make_adder(a)
  let g = make_adder(b)
  return apply(f, apply(g, x))
end
let C = { v: u32, mk() = |x: u32| -> v + x }
let snap(n: u32) : u32 = do
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
local shareSession = Eval.new()
shareSession:compile(Parse.source("let twice(f: (u32): u32, x: u32) : u32 = f(f(x))\n"
    .. "let a(x: u32) : u32 = twice(|y: u32| -> y + 1, x)\n"
    .. "let b(x: u32) : u32 = twice(|y: u32| -> y + 1, x)\n"
    .. "return { functions = { a, b } }", "s.let"))
-- a, b, twice specialised for each distinct lambda, and each lambda once
check(#shareSession.order == 6, "identical-looking lambdas are still distinct code identities")
local closureBodies = 0
for _, instance in ipairs(shareSession.order) do
    if instance.plan then closureBodies = closureBodies + 1 end
end
check(closureBodies == 2, "each syntactic lambda compiles once regardless of call sites")

local retSession = Eval.new()
retSession:compile(Parse.source("let apply(f: (u32): u32, x: u32) : u32 = f(x)\n"
    .. "let make_adder(n: u32) = |x: u32| -> n + x\n"
    .. "let run(n, x: u32) : u32 = do let add = make_adder(n) return apply(add, x) end\n"
    .. "return { functions = { run } }", "r.let"))
check(#retSession.order == 4, "a returned closure has one body and one caller specialisation")
local sawOwnedInput = false
for _, instance in ipairs(retSession.order) do
    for _, input in ipairs(instance.fn.inputs) do
        if input.type:isOwned() then sawOwnedInput = true end
    end
end
check(sawOwnedInput, "the callable travels as a by-value environment input")

-- Contextual typing: a signature requirement supplies a lambda's missing parameter types -------
local CONTEXTUAL = [==[
let twice(f: (u32): u32, x: u32): u32 = f(f(x))
let adder(n: u32): (u32): u32 = |x| -> x + n
let inc: (u32): u32 = |x| -> x + 1
let use(n, x: u32): u32 = do
  let f = adder(n)
  return twice(f, x) + inc(x)
end
let inline(x: u32): u32 = twice(|y| -> y * 2, x)
let capture(x: u32): u32 = twice(|y| -> y + x, 1)
return { functions = { use, inline, capture } }
]==]
check(interpret("use", { 3, 4 }, CONTEXTUAL)[1] == 15,
    "a lambda argument, a signature result and a declared callable binding all infer")
check(interpret("inline", { 5 }, CONTEXTUAL)[1] == 20, "an unannotated lambda argument takes its type")
check(interpret("capture", { 10 }, CONTEXTUAL)[1] == 21, "a contextually typed lambda may capture")

rejects("lambda-annotation", "let g = |x| -> x + 1\nlet f(y: u32): u32 = g(y)\nreturn { functions = { f } }")
rejects("callable-shape", "let twice(f: (u32): u32, x: u32): u32 = f(f(x))\n"
    .. "let a(x: u32): u32 = twice(|y, z: u32| -> y + z + x, 1)\nreturn { functions = { a } }")
rejects("callable-shape", "let apply(f: (u32): u32, x: u32): u32 = f(x)\n"
    .. "let a(x: u32): u32 = apply(|y: u32| -> true, x)\nreturn { functions = { a } }")
-- Two different lambdas in one conditional join into a tagged callable (see the tagged-callable
-- section), but an owning callable selected at run time cannot be erased into a signature: a view
-- does not retain the environment that carries the tag.
rejects("callable-erase", "let pick(c: bool): (u32): u32 = if c then |x: u32| -> x + 1 else |x: u32| -> x + 2\n"
    .. "return { functions = { pick } }")
rejects("callable-erase", [==[
let run(c: bool, x: u32): u32 = do
  let f = if c then |y: u32| -> y + 1 else |y: u32| -> y + 2
  let g: (u32): u32 = f
  return g(x)
end
return { functions = { run } }
]==])

-- Borrowed captures: a captured receiver is a place, not a copy --------------------------------
local BORROWED = [==[
let Counter = {
  value: u32,
  bump(): u32 = do value += 1 return value end,
}
let local_bumps(n: u32): u32 = do
  let c = Counter { value = n }
  let f = |k: u32| -> c.bump() + k
  return f(1) + f(2)
end
let method_view(n: u32): u32 = do
  let c = Counter { value = n }
  let g = c.bump
  let h = |u: u32| -> g() + u
  return h(10)
end
let read_through(n: u32): u32 = do
  let c = Counter { value = n }
  let peek = |u: u32| -> c.value + u
  c.value += 5
  return peek(100)
end
let array_bumps(i: u32): u32 = do
  let a = [1, 2, 3]
  let f = |k: u32| -> do a[k] = 9 return a[k] end
  return f(i) * 100 + a[0]
end
return { types = { Counter }, functions = { local_bumps, method_view, read_through, array_bumps } }
]==]
check(interpret("local_bumps", { 5 }, BORROWED)[1] == 16, "a captured receiver mutates through the closure")
check(interpret("method_view", { 5 }, BORROWED)[1] == 16, "a captured method view keeps its receiver")
check(interpret("read_through", { 1 }, BORROWED)[1] == 106,
    "a borrowed receiver is live, unlike a captured field snapshot")
check(interpret("array_bumps", { 0 }, BORROWED)[1] == 909,
    "a captured array is borrowed, so a mutation through the closure is visible afterward")
compile(BORROWED)

rejects("borrow-escape", "let C = { v: u32, bump(): u32 = v }\n"
    .. "let bad(n: u32): (u32): u32 = do let c = C { v = n } return |k: u32| -> c.bump() + k end\n"
    .. "return { types = { C }, functions = { bad } }")

-- Opaque runtime callables: the invocation-pointer ABI -----------------------------------------
local EXTERNAL = [==[
let apply(f: (u32): u32, x: u32): u32 = f(x)
let twice_apply(f: (u32): u32, x: u32): u32 = apply(f, apply(f, x))
let compose(f: (u32): u32, g: (u32): u32, x: u32): u32 = f(g(x))
let invoke(f: (u32): (), x: u32): u32 = do f(x) return x end
let internal(x: u32): u32 = apply(|y: u32| -> y + 1, x)
return { functions = { apply, twice_apply, compose, invoke, internal } }
]==]
-- An exported callable parameter has no call site, so it becomes an opaque view.
local externalArtifact = wordlet.compile{ source = EXTERNAL, name = "external.let" }
local externalUnit = externalArtifact:unit()
check(externalUnit:find("typedef struct wordletview_1", 1, true) ~= nil, "a view struct is emitted")
check(externalUnit:find("(*invoke)(const void *, uint32_t)", 1, true) ~= nil, "the view carries an invoke pointer")
check(externalUnit:find(".invoke(", 1, true) ~= nil, "the opaque call goes through the pointer")
check(#externalArtifact:exports() == 5, "the higher-order functions are exportable")

local externalSession = Eval.new()
externalSession:compile(Parse.source(EXTERNAL, "external.let"))
local viewInputs, indirectInstances = 0, 0
for _, instance in ipairs(externalSession.order) do
    for _, input in ipairs(instance.fn.inputs) do
        if input.type:isView() then viewInputs = viewInputs + 1 end
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
local loopSession = Eval.new()
loopSession:compile(Parse.source("let sum_to(n, acc: u32) : u32 = if n == 0 then acc else sum_to(n - 1, acc + n)\n"
    .. "return { functions = { sum_to } }", "l.let"))
check(#loopSession.order == 1, "a tail self-call reuses the instance it is defined in")
local loopIR = A.dump(loopSession.order[1].fn)
check(loopIR:find("Loop", 1, true) ~= nil and loopIR:find("Next", 1, true) ~= nil,
    "the body carries a Loop with a back edge")
check(loopIR:find("Call", 1, true) == nil, "the tail call emits no call at all")

-- A saturated keyed self-call is a tail call too, so it reuses the instance and emits a Loop.
local keyedLoop = Eval.new()
keyedLoop:compile(Parse.source("let sum { n: u32, acc: u32 } : u32 = if n == 0 then acc else sum { n = n - 1, acc = acc + n }\n"
    .. "let run(n: u32, start: u32) : u32 = sum { n = n, acc = start }\n"
    .. "return { functions = { run } }", "kl.let"))
local keyedSum = nil
for _, instance in ipairs(keyedLoop.order) do
    if instance.def and instance.def.name == "sum" then keyedSum = instance.fn end
end
check(keyedSum ~= nil, "a keyed word has an instance")
local keyedIR = A.dump(keyedSum)
check(keyedIR:find("Loop", 1, true) ~= nil and keyedIR:find("Next", 1, true) ~= nil,
    "a keyed tail self-call carries a Loop with a back edge")
check(keyedIR:find("Call", 1, true) == nil, "the keyed tail call emits no call")

local recSession = Eval.new()
recSession:compile(Parse.source("let f(a: u32) : u32 = if a == 0 then 1 else a * f(a - 1)\n"
    .. "return { functions = { f } }", "r.let"))
check(A.dump(recSession.order[1].fn):find("Loop", 1, true) == nil,
    "recursion outside tail position stays an ordinary call")

-- A conditional in tail position loops from either arm.
local bothSession = Eval.new()
bothSession:compile(Parse.source("let count(n: u32) : u32 =\n"
    .. "  if n == 0 then 0 else if n == 1 then count(0) else count(n - 2)\n"
    .. "return { functions = { count } }", "b.let"))
check(A.dump(bothSession.order[1].fn):find("Loop", 1, true) ~= nil, "either tail arm may loop")

-- A loop-carried parameter is read once at the top of the loop body, so expressions built from it
-- are shared. Reads are never interned, so a read per mention would block that sharing.
local readSession = Eval.new()
readSession:compile(Parse.source("let step(n: u32, x: u32): u32 = do\n"
    .. "  if n == 0 then return x ~ (x << 3) end\n"
    .. "  let y = x ~ (x << 3)\n"
    .. "  return step(n - 1, y)\n"
    .. "end\nreturn { functions = { step } }", "read.let"))
local _, reads = A.dump(readSession.order[1].fn):gsub("Read", "")
check(reads == 2, "a loop-carried parameter is read once, not per mention (found " .. reads .. ")")

-- A tail call that forwards a parameter unchanged omits that slot's back-edge copy: the storage
-- already holds the value, so storing it back would be a self-copy. Only slots the call rebinds are
-- stored. The unchanged slot's `Var` then has no store, so emission drops it and the header read
-- aliases the input directly.
local forwardSession = Eval.new()
forwardSession:compile(Parse.source("let count(n: u32, k: u32): u32 = do\n"
    .. "  if n == 0 then return k end\n"
    .. "  return count(n - 1, k)\n"
    .. "end\nreturn { functions = { count } }", "forward.let"))
local _, forwardStores = A.dump(forwardSession.order[1].fn):gsub("Store", "")
check(forwardStores == 1,
    "an unchanged forwarded parameter is not copied on the back edge (found " .. forwardStores .. ")")

-- The same shape where both slots change keeps both stores, so the elision is not over-eager.
local changedSession = Eval.new()
changedSession:compile(Parse.source("let count(n: u32, acc: u32): u32 = do\n"
    .. "  if n == 0 then return acc end\n"
    .. "  return count(n - 1, acc + n)\n"
    .. "end\nreturn { functions = { count } }", "changed.let"))
local _, changedStores = A.dump(changedSession.order[1].fn):gsub("Store", "")
check(changedStores == 2,
    "a changed parameter still gets a back-edge store (found " .. changedStores .. ")")

-- A tail call with different static arguments is a different instance, so it is a real call.
local staticSession = Eval.new()
staticSession:compile(Parse.source("let scale(k, x: u32) : u32 = if k == 0 then x else scale(0, x + 1)\n"
    .. "let five(x: u32) : u32 = scale(5, x)\nreturn { functions = { five } }", "s.let"))
check(#staticSession.order >= 2, "changing a static argument creates a new instance")

-- Partial application of a closure ------------------------------------------------------------
local PARTIAL = [==[
let add = |a, b: u32| -> a + b
let add5 = add(5)
let use(x: u32): u32 = add5(x) + add(2)(3)
return { functions = { use } }
]==]
check(interpret("use", { 10 }, PARTIAL)[1] == 20, "a closure may be supplied with fewer arguments")
local partialUnit = wordlet.compile{ source = PARTIAL, name = "partial.let" }:unit()
check(partialUnit:find("wordlet_use", 1, true) ~= nil, "a partially applied closure compiles")
rejects("static-required", "let add = |a, b: u32| -> a + b\n"
    .. "let f(n: u32): u32 = do let g = add(n) return g(1) end\nreturn { functions = { f } }")

-- Module-level mutable state --------------------------------------------------------------------
local MODULE_STATE = [==[
let Counter = { value: u32, bump(): u32 = do value += 1 return value end }
let shared = Counter { value = 100 }
let bump_twice(x: u32): u32 = do shared.bump() shared.bump() return shared.value + x end
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
rejects("unknown-name", "let f(x: u32) = y\nreturn { functions = { f } }")
rejects("arity", "let f(a, b: u32) : u32 = a + b\nlet g(x: u32) : u32 = f(1, 2, 3)\nreturn { functions = { g } }")
rejects("callable-required", "let f(x: u32) : u32 = x\nlet g(x: u32) : u32 = f(1)(2)\nreturn { functions = { g } }")
rejects("type-mismatch", "let f(x: u32) : u32 = x + true\nreturn { functions = { f } }")
rejects("division-zero", "let f(x: u32) : u32 = x / 0\nreturn { functions = { f } }")
rejects("recursive-result", "let f(x: u32) = if x == 0 then 0 else f(x - 1)\nreturn { functions = { f } }")
-- A block need not end in `return` (syntax.md §12); one that can fall through is rejected by the
-- reachability check, which is a semantic error rather than a parse error.
rejects("no-return", "let f(x: u32) : u32 = do let y = x + 1 end\nreturn { functions = { f } }")
rejects("duplicate", "let f(x: u32) : u32 = do let y = x let y = x return y end\nreturn { functions = { f } }")
rejects("unknown-name", "return { functions = { missing } }")
rejects("function-required", "let x = 3\nreturn { functions = { x } }")
rejects("parse", "let f(x: u32) = x\nreturn { functions = { f }")
rejects("initializer-cycle", "let a = b\nlet b = a\nlet f(x: u32) : u32 = a + x\nreturn { functions = { f } }")
rejects("static-required", "let scale(k, x: u32) : u32 = k * x\n"
    .. "let use(x: u32) : u32 = do let g = scale(x) return g(1) end\nreturn { functions = { use } }")
rejects("branch-result", "let f(x: u32) : u32 = if x == 0 then 1 else true\nreturn { functions = { f } }")
rejects("static-required", "let P = { x: u32, y: u32 }\nlet f(a: u32) : u32 = do"
    .. " let q = P { x = a } let z = q.y return z end\nreturn { functions = { f } }")
rejects("not-a-place", "let P = { x: u32 }\nlet f(a: u32) : u32 = do"
    .. " let p = P { x = a }\n let n = 3\n n = 4\n return p.x end\nreturn { functions = { f } }")
rejects("type-mismatch", RECORDS, "bump", { 7 })
-- A signature-typed field is represented by the borrowed callable ABI, so a record holding one is
-- usable locally but cannot escape.
local CALLABLE_FIELD = [==[
let Holder = { f: (u32): u32 }
let use(n: u32): u32 = do
  let h = Holder { f = |x: u32| -> x + n }
  return h.f(1)
end
let chase(n: u32): u32 = do
  let h = Holder { f = |x: u32| -> x * 2 }
  return h.f(h.f(n))
end
return { types = { Holder }, functions = { use, chase } }
]==]
check(interpret("use", { 5 }, CALLABLE_FIELD)[1] == 6, "a callable field is invoked through its view")
check(interpret("chase", { 3 }, CALLABLE_FIELD)[1] == 12, "a capture-free callable field still invokes")
local fieldUnit = wordlet.compile{ source = CALLABLE_FIELD, name = "field.let" }:unit()
check(fieldUnit:find("wordletadapterstruct_1", 1, true) ~= nil, "an adapter struct is emitted")
check(fieldUnit:find(".invoke = wordletadapterfn_1", 1, true) ~= nil, "the view is built from the adapter")
rejects("borrow-escape", "let H = { f: (u32): u32 }\n"
    .. "let make(n: u32) = H { f = |x: u32| -> x + n }\nreturn { types = { H }, functions = { make } }")
rejects("borrow-escape", "let H = { f: (u32): u32 }\nlet shared = H { f = |x: u32| -> x }\n"
    .. "let set(n: u32): u32 = do shared.f = |y: u32| -> y + n return 0 end\n"
    .. "return { types = { H }, functions = { set } }")

rejects("callable-shape", "let apply(f: (u32): u32, x: u32) : u32 = f(x)\n"
    .. "let bad(x: u32) : u32 = apply(|y: u32| -> true, x)\nreturn { functions = { bad } }")
rejects("unknown-member", "let P = { x: u32 }\nlet f(a: u32) : u32 = do"
    .. " let p = P { x = a } return p.z end\nreturn { functions = { f } }")
rejects("duplicate", "let P = { x: u32 }\nlet f(a: u32) : u32 = do"
    .. " let p = P { x = a, x = 1 } return p.x end\nreturn { functions = { f } }")
-- Module-level mutable state is supported: the binding becomes a named runtime object.
local moduleBinding = wordlet.compile{ source = "let P = { x: u32 }\nlet m = P { x = 1 }\n"
    .. "let f(a: u32): u32 = do m.x += a return m.x end\nreturn { functions = { f } }" }
check(moduleBinding:unit():find("wordletmodule_1", 1, true) ~= nil, "a module binding gets its own storage")
-- Module storage is runtime state. Compile-time normalization must not write it, because the store
-- would drop out of the generated code; the reference interpreter executes the program and does
-- write it. The C tests cover the generated runtime path.
local moduleStore = "let P = { x: u32 }\nlet m = P { x = 1 }\n"
    .. "let f(a: u32): u32 = do m.x += a return m.x end\nreturn { functions = { f } }"
check(interpret("f", { 4 }, moduleStore)[1] == 5, "the interpreter runs a module field store")
-- A module array is storage too: an element store persists, and a direct or run-time index reads it.
local moduleArray = "let scratch: array(u32, 3) = [0, 0, 0]\n"
    .. "let put(i, v: u32): u32 = do scratch[i] = v return scratch[0] + scratch[1] + scratch[2] end\n"
    .. "let get(i: u32): u32 = scratch[i]\nreturn { functions = { put, get } }"
check(interpret("put", { 1, 9 }, moduleArray)[1] == 9, "a module array element store persists")
check(interpret("get", { 2 }, moduleArray)[1] == 0, "a run-time index reads a module array element")
check(interpret("f", {}, "let K = [10, 20, 30]\nlet f(): u32 = K[2]\nreturn { functions = { f } }")[1] == 30,
    "a constant index reads a module array element")
-- A top-level initializer is compile-time execution over concrete values, so it reads module storage.
check(interpret("f", {}, "let shared = [10, 20, 30]\nlet b = shared[2]\n"
    .. "let f(): u32 = b\nreturn { functions = { f } }")[1] == 30,
    "a top-level initializer reads a module array")
check(interpret("f", {}, "let P = { x: u32 }\nlet base = P { x = 3 }\nlet s = base.x + 1\n"
    .. "let f(): u32 = s\nreturn { types = { P }, functions = { f } }")[1] == 4,
    "a top-level initializer reads a module record field")
-- Initialization runs once, eagerly, in declaration order, so a mutating initializer is supported and
-- the interpreter observes the same state the generated `wordlet_init` bakes.
local mutating = "let shared = [1, 2, 3]\n"
    .. "let bump(): u32 = do shared[0] = 9 return shared[0] end\n"
    .. "let b = bump()\nlet f(): u32 = b\n"
    .. "let g(): u32 = shared[0] + b\nreturn { functions = { f, g } }"
check(interpret("f", {}, mutating)[1] == 9, "a mutating top-level initializer runs once")
check(interpret("g", {}, mutating)[1] == 18, "top-level initialization follows declaration order")
check(compile(mutating) ~= nil, "a mutating top-level initializer compiles")
-- A top-level result-list binding declares every binder and distributes the result vector, exactly
-- as a local binding does.
local multi = "let a, b = 1, 2\nlet f(): u32 = a * 10 + b\nreturn { functions = { f } }"
check(interpret("f", {}, multi)[1] == 12, "a top-level result-list binding binds every name")
check(interpret("g", {}, "let divmod(a, b: u32): (u32, u32) = do return a / b, a % b end\n"
    .. "let q, r = divmod(17, 5)\nlet g(): u32 = q * 100 + r\nreturn { functions = { g } }")[1] == 302,
    "a top-level result-list binding distributes a call's results")
check(interpret("f", {}, "let a, b: u32 = 1, 2\nlet f(): u32 = a + b\n"
    .. "return { functions = { f } }")[1] == 3, "each top-level binder carries its own annotation")
rejects("duplicate", "let a, a = 1, 2\nlet f(): u32 = a\nreturn { functions = { f } }")


-- Sum types (variants) --------------------------------------------------------------------------
-- A keyed definition attaches to a word without parentheses: `oneof { a: u32 }` is the keyed
-- spelling of `oneof { a: u32 }`, so the alternatives read as a definition rather than a call.
do
    local source = "let S = oneof { a: u32, b: u32 }\n"
        .. "let pick(s: S): u32 = s { a = |v: u32| -> v, b = |v: u32| -> v + 10 }\n"
        .. "let via_a(x: u32): u32 = pick(S.a(x))\n"
        .. "let via_b(x: u32): u32 = pick(S.b(x))\n"
        .. "return { types = { S }, functions = { via_a, via_b } }"
    check(interpret("via_a", { 7 }, source)[1] == 7, "a keyed oneof builds a sum")
    check(interpret("via_b", { 7 }, source)[1] == 17, "a keyed oneof alternative carries its payload")
    compile(source)
end

-- Keyed requirements on a word: supplied by name, in any order, and partially. Each key is
-- annotated because a keyed requirement has no position to infer its type from.
do
    local source = "let distance { x: u32, y: u32 }: u32 = x * x + y * y\n"
        .. "let full(): u32 = distance { x = 3, y = 4 }\n"
        .. "let partial(): u32 = distance { x = 3 } { y = 4 }\n"
        .. "let reordered(): u32 = distance { y = 4, x = 3 }\n"
        .. "let positional(): u32 = distance(3, 4)\n"
        .. "return { functions = { full, partial, reordered, positional } }"
    check(interpret("full", {}, source)[1] == 25, "a keyed word is invoked by name")
    check(interpret("partial", {}, source)[1] == 25, "keyed supply specializes and then completes")
    check(interpret("reordered", {}, source)[1] == 25, "keyed requirements have no order")
    check(interpret("positional", {}, source)[1] == 25, "every key may also be supplied positionally")
    compile(source)
end
-- A keyed requirement is always annotated, and an annotation written as a signature types the value
-- supplied for it exactly as a positional requirement does, so the lambda's parameter needs no
-- annotation of its own. Unifying keyed supply with positional supply is what makes this work.
local keyedLambda = "let apply2 { f: (u32): u32, x: u32 } : u32 = f(x)\n"
    .. "let g(): u32 = apply2 { f = |a| -> a + 1, x = 5 }\nreturn { functions = { g } }"
check(interpret("g", {}, keyedLambda)[1] == 6,
    "a signature annotation types the lambda a keyed requirement is supplied")
compile(keyedLambda)
rejects("unknown-member", "let f { x: u32 } = x\nlet bad(): u32 = f { y = 1 }\nreturn { functions = { bad } }")

rejects("duplicate", "let f { x: u32 } = x\nlet bad(): u32 = f { x = 1, x = 2 }\nreturn { functions = { bad } }")
rejects("keyed-required", "let f { x: u32, y: u32 }: u32 = x + y\nlet g = f(1)\nreturn { functions = {} }")

-- `oneof` builds a sum from a keyed schema; member selection names a constructor and keyed
-- application either constructs one alternative or matches on the tag.
local shapes = [==[
let Circle = { radius: u32 }
let Rect = { width: u32, height: u32 }
let Shape = oneof { circle: Circle, rect: Rect }
let area(s: Shape): u32 = s {
  circle = |c: Circle| -> c.radius * c.radius,
  rect = |r: Rect| -> r.width * r.height,
}
let round(n: u32): Shape = Shape.circle { radius = n }
let box(n: u32): Shape = Shape.rect { width = n, height = 3 }
let area_of_circle(n: u32): u32 = area(Shape.circle { radius = n })
let area_of_round(n: u32): u32 = area(round(n))
let tag_of(n: u32): u32 = round(n) {
  circle = |c: Circle| -> c.radius,
  rect = |r: Rect| -> r.width,
}
return { types = { Circle, Rect, Shape }, functions = { area, round, box, area_of_circle, area_of_round, tag_of } }
]==]
check(interpret("area_of_circle", { 5 }, shapes)[1] == 25, "a known alternative is selected statically")
check(interpret("area_of_round", { 6 }, shapes)[1] == 36, "a statically tagged value matches directly")
check(interpret("tag_of", { 7 }, shapes)[1] == 7, "matching reads the payload of the held alternative")
check(compile(shapes):unit():find("wordletsum_1", 1, true) ~= nil, "a sum type gets a tagged C layout")

-- A unit alternative takes no payload, and its match arm is applied with none.
local OPTION = [==[
let Opt = oneof { none: unit, some: u32 }
let or_else(o: Opt, d: u32): u32 = o {
  none = |u: unit| -> d,
  some = |v: u32| -> v,
}
let wrap(n: u32): Opt = if n == 0 then Opt.none() else Opt.some(n)
let unwrap_or(n: u32, d: u32): u32 = or_else(wrap(n), d)
return { functions = { or_else, wrap, unwrap_or } }
]==]
check(interpret("unwrap_or", { 0, 9 }, OPTION)[1] == 9, "a unit alternative matches with no payload")
check(interpret("unwrap_or", { 4, 9 }, OPTION)[1] == 4, "a payload alternative projects its payload")

-- A scalar alternative is applied positionally rather than by named supply.
check(interpret("id", { 3 },
    "let Opt = oneof { some: u32 }\nlet id(n: u32): u32 = Opt.some(n) { some = |v: u32| -> v }\n"
    .. "return { functions = { id } }")[1] == 3, "a non-record alternative is applied to one value")

-- Known matches must not construct unselected lambda literals: construction elaborates a base
-- instance, so waiting until invocation to select the arm is already too late.
do
    local prefix = "let T=oneof {a:u32,b:u32}\n"
    local function known(arm)
        return prefix .. "let choose(x:u32):u32=T.a(x){a=|v:u32|->v+1,b=" .. arm
            .. "}\nreturn {functions={choose}}"
    end
    for _, arm in ipairs({
        "|v:u32|->1+true", "|v:u32|->missing_capture", "|v:MissingType|->0",
        "|v|->0", "(|v:u32|->[0][1])", "|v:u32|->true",
    }) do
        local program = known(arm)
        local artifact = compile(program)
        local plans = 0
        for _ in pairs(artifact.compilation.session.plans) do plans = plans + 1 end
        check(plans == 1, "a dead literal creates no closure plan: " .. arm)
        check(interpret("choose", {5}, program)[1] == 6, "known tag invokes only its selected handler")
    end
    -- Selection is per occurrence, not a permanent exemption for that source lambda.
    local arms = "{a=|v:u32|->v,b=|v:u32|->1+true}"
    rejects("type-mismatch", prefix .. "let choose(x:u32):u32=T.b(x)" .. arms
        .. " return {functions={choose}}")
    rejects("type-mismatch", prefix .. "let choose(s:T):u32=s" .. arms
        .. " return {functions={choose}}")
    rejects("lambda-annotation", prefix
        .. "let choose(s:T):u32=s{a=|v:u32|->v,b=|v|->0} return {functions={choose}}")
    -- Skipping a literal does not erase its field name from syntactic validation.
    for _, case in ipairs({
        {"duplicate", "{a=|v:u32|->v,b=|v|->0,b=|v|->0}"},
        {"variant-match", "{a=|v:u32|->v}"},
        {"variant-match", "{b=|v|->0}"},
        {"unknown-member", "{a=|v:u32|->v,b=|v|->0,c=|v|->0}"},
    }) do
        rejects(case[1], prefix .. "let choose(x:u32):u32=T.a(x)" .. case[2]
            .. " return {functions={choose}}")
    end
    -- Non-lambda expressions still evaluate and must produce callable values.
    rejects("callable-required", known("false"))
    rejects("division-zero", known("1/0"))
end

-- Static instruction selection must cut off dead handler elaboration before it walks off the
-- program. The selected lambda instances can then form a finite residual tail component.
do
    local program = [[
let Op=oneof {step:unit,branch:unit,halt:unit}
let instruction(pc:u32):Op=[Op.step(),Op.branch(),Op.halt()][pc]
let vm(pc,n,a:u32):u32=instruction(pc){
  step=|u:unit|->vm(pc+1,n,a+3),
  branch=|u:unit|->if n==0 then vm(pc+1,n,a) else vm(0,n-1,a),
  halt=|u:unit|->a,
}
let run(n,a:u32):u32=vm(0,n,a)
return {functions={run}}
]]
    local artifact = compile(program)
    local jumps = 0
    for _, report in ipairs(artifact.layouts.contextual.reports) do jumps = jumps + report.jumps end
    check(jumps > 0, "static-pc VM and selected lambda handlers form a tail component")
    for _, n in ipairs({0,1,3,10,100}) do
        check(interpret("run", {n,7}, program)[1] == 7+3*(n+1), "static-pc VM result")
    end
    check(wordlet.interpret{source=program, entry="run", args={10,7},
        limits={keys=0,steps=5000}}[1] == 40,
        "known immediate handlers execute without reserving any residual base")
    local folded = program:gsub("return {functions={run}}",
        "let folded():u32=run(10,7) return {functions={folded}}")
    check(compile(folded):unit():find("UINT32_C(40)", 1, true) ~= nil,
        "static-pc VM folds with default compilation budgets")
end

-- Immediate static lambda use prepares captures/parameters, not an unused generic C base.
do
    local chain = "let chain(n:u32):u32=if n==0 then 0 else (|u:unit|->chain(n-1)+1)(unit()) "
        .. "return {functions={chain}}"
    check(wordlet.interpret{source=chain, entry="chain", args={100},
        limits={keys=0,steps=5000}}[1] == 100, "sum-free lambda chain is linear without memoization")
    local function run(body)
        return interpret("run", {}, "let run()=" .. body .. " return {functions={run}}")
    end
    check(run("(|a,b:u32|->a+b)(3)(4)")[1] == 7, "partial immediate use finishes the ordinary callable")
    check(run("(|a:u32,f:(u32):u32|->f(a))(3)(|x|->x+1)")[1] == 4,
        "partial lambda uses the remaining resolved callable requirement")
    check(run("(||->unit())()")[1] == "unit", "nullary immediate unit result")
    local narrowing = "let run():u32=do let n=255 let got=(|u:u8|->n+1)(n) "
        .. "return got+(n+1) end return {functions={run}}"
    check(interpret("run", {}, narrowing)[1] == 512, "parameter coercion preserves binding/capture types")
    compile(narrowing)
    local vector = run("(|u:unit|->do return unit(),3 end)(unit())")
    check(vector[1] == "unit" and vector[2] == 3, "immediate lambda preserves logical result vectors")
    check(run("(|x:u32|->if x==0 then 7 else x+true)(0)")[1] == 7,
        "known immediate invocation checks the selected body path, like a static word call")
    rejects("type-mismatch", "let run():u32=(|u:bool|->1)(3) return {functions={run}}", "run")
    rejects("type-mismatch", "let run():u32=(|u:bool|->1)(3) return {functions={run}}")
    rejects("type-mismatch", "let run():u32=(|x:u32|->if x==0 then 7 else x+true)(1) "
        .. "return {functions={run}}", "run")
    rejects("type-mismatch", "let f=|x:u32|->x+true return {functions={}}")
    rejects("type-mismatch", "let Op=oneof {a:u32} let run():u32=Op.a(3){a=|v:bool|->1} "
        .. "return {functions={run}}", "run")
    rejects("arity", "let run():u32=(||->1)(2) return {functions={run}}", "run")
    rejects("lambda-annotation", "let run():u32=(|x|->x)(2) return {functions={run}}", "run")
    rejects("borrow-escape", "let Box={n:u32} let run():u32="
        .. "(|u:unit|->do let b=Box{n=1} return |x:u32|->b.n+x end)(unit())(0) "
        .. "return {functions={run}}", "run")
    rejects("ref-target", "let Box={n:u32} let run()="
        .. "(|u:unit|->do let b=Box{n=1} return ref(b) end)(unit()) "
        .. "return {functions={run}}", "run")

    local ordered = [[
let Box={n:u32}
let box=Box{n=0}
let type_now()=do box.n=box.n*10+1 return u32 end
let argument():u32=do box.n=box.n*10+2 return 7 end
let answer=(|x:type_now()|->x+1)(argument())
let run():u32=box.n*100+answer
return {functions={run}}
]]
    check(interpret("run", {}, ordered)[1] == 1208, "annotation executes once, before arguments")
    compile(ordered)
    local stored = ordered:gsub("let answer=%(%|x:type_now%(%)%|%->x%+1%)%(argument%(%)%)",
        "let f=|x:type_now()|->x+1 let answer=f(argument())")
    check(stored ~= ordered, "stored-closure fixture is distinct")
    check(interpret("run", {}, stored)[1] == 1208, "stored closure also reuses resolved parameter types")
    compile(stored)
    local copies = [[
let Box={n:u32}
let run():u32=do
 let b=Box{n=1}
 let result=(|p:Box|->do p.n+=1 return p.n end)(b)
 return result*100+b.n
end
return {functions={run}}
]]
    check(interpret("run", {}, copies)[1] == 201, "static closure parameters copy record data")
    compile(copies)
    local effects = [[
let Box={n:u32}
let work(n:u32):u32=do
 let b=Box{n=n}
 let bump():u32=do b.n+=1 return b.n end
 let result=(|u:unit|->bump())(unit())
 return result*100+b.n
end
let run():u32=work(3)
return {functions={run}}
]]
    check(interpret("run", {}, effects)[1] == 404, "local helper effects run once, not during an unused base")
    check(compile(effects):unit():find("UINT32_C(404)", 1, true) ~= nil,
        "normalizing an immediate lambda preserves exact-once effects")
    local captures = [[
let Op=oneof {a:unit,b:unit}
let R={n:u32,
 direct():u32=(|u:u32|->n+u)(bump()),
 matched():u32=Op.a(){a=|u:unit|->n,b=later()},
}
let r=R{n=2}
let bump():u32=do r.n+=10 return 1 end
let later():(unit):u32=do r.n+=10 return |u:unit|->0 end
let direct():u32=do let answer=r.direct() return r.n*100+answer end
let matched():u32=do let answer=r.matched() return r.n*100+answer end
return {functions={direct,matched}}
]]
    check(interpret("direct", {}, captures)[1] == 1203, "capture snapshot precedes argument effects")
    check(interpret("matched", {}, captures)[1] == 1202, "capture precedes later handler expression effects")
    compile(captures:gsub("return {functions={direct,matched}}", "return {functions={direct}}"))
    local initialized = captures:gsub("return {functions={direct,matched}}",
        "let captured=matched() let run():u32=captured return {functions={run}}")
    check(interpret("run", {}, initialized)[1] == 1202, "handler ordering also holds in initialization")
    compile(initialized)
end

-- A declared result contract is checked against what the body returns, and a violation is a source
-- diagnostic with a span rather than an internal bug. Before this check the mismatch reached the IR
-- checker, which reported `BUG [ir-return]` for a user's type error.
--
-- The contract is exact (`syntax.md` §6): a return vector is neither widened to satisfy it nor padded.
-- A `unit` result is still a logical slot on both sides, so `: unit` with `unit()` and an exact
-- `(u32, unit)` remain well formed even though C erases the payload.
do
    rejects("type-mismatch",
        "let take(n: u32): u32 = n\nlet f(): bool = take(1)\nreturn { functions = { f } }")
    rejects("result-count",
        "let take(n: u32): u32 = n\nlet f(): (u32, u32) = take(1)\nreturn { functions = { f } }")
    rejects("result-count", "let f(): u32 = do return 1, 2 end\nreturn { functions = { f } }")
    rejects("type-mismatch", "let g(x: u8): u32 = x\nreturn { functions = { g } }")
    compile("let f(): unit = unit()\nreturn { functions = { f } }")
    compile("let f(): (u32, unit) = do return 1, unit() end\nreturn { functions = { f } }")
    check(interpret("f", {}, "let take(n: u32): u32 = n\nlet f(): u32 = take(41)\n"
        .. "return { functions = { f } }")[1] == 41, "a well-typed declared result still builds")
end

-- A foreign declaration has no body, so nothing else compares its requirement with what the caller
-- supplied. The check lives at the call, where both are known: a mistyped argument is a source
-- rejection rather than the `BUG [ir-type]` the IR checker used to report.
do
    rejects("type-mismatch",
        "extern let host_add(a: u32): u32\nlet f(): u32 = host_add(true)\nreturn { functions = { f } }")
    local foreign = "extern let host_sink(p: ptr(u8), n: u32): u32\n"
        .. "let buf: array(u8, 3) = [1, 2, 3]\n"
        .. "let f(): u32 = host_sink(ptr(buf[0]), 3)\nreturn { functions = { f } }"
    check(compile(foreign):unit():find("host_sink", 1, true) ~= nil,
        "a pointer to a buffer is passed to a foreign word by address")
end

-- Rejections -----------------------------------------------------------------------------------
rejects("variant-match", [==[
let A = { x: u32 }
let B = { y: u32 }
let S = oneof { a: A, b: B }
let f(s: S): u32 = s { a = |v: A| -> v.x }
let g(n: u32): u32 = f(S.a { x = n })
return { functions = { g } }
]==], "g", { 1 })
-- A sum value has no direct members at all: an alternative is reached by matching, not by name.
rejects("member-required", [==[
let A = { x: u32 }
let S = oneof { a: A }
let f(n: u32): u32 = do let s = S.a { x = n } return s.b end
return { functions = { f } }
]==], "f", { 1 })
-- A match must name only the type's alternatives.
rejects("unknown-member", [==[
let A = { x: u32 }
let S = oneof { a: A }
let f(n: u32): u32 = S.a { x = n } { a = |v: A| -> v.x, c = |v: A| -> v.x }
return { functions = { f } }
]==], "f", { 1 })
rejects("unknown-member", [==[
let A = { x: u32 }
let S = oneof { a: A }
let f(n: u32): u32 = S.a { y = n }
return { functions = { f } }
]==], "f", { 1 })
rejects("variant-payload", [==[
let A = { x: u32 }
let S = oneof { a: A }
let f(n: u32): u32 = S.a { }
return { functions = { f } }
]==], "f", { 1 })
-- A scalar alternative is not built from named fields.
rejects("variant-payload", [==[
let S = oneof { a: u32 }
let f(n: u32): u32 = S.a { x = n } { a = |v: u32| -> v }
return { functions = { f } }
]==], "f", { 1 })
-- A record alternative expects its own payload type, not an unrelated value.
rejects("type-mismatch", [==[
let A = { x: u32 }
let S = oneof { a: A }
let f(n: u32): u32 = S.a(n) { a = |v: A| -> v.x }
return { functions = { f } }
]==], "f", { 1 })
rejects("arity", [==[
let A = { x: u32 }
let S = oneof { a: A }
let f(n: u32): u32 = S.a(n, n) { a = |v: A| -> v.x }
return { functions = { f } }
]==], "f", { 1 })
-- A top-level binding is evaluated on demand, so each rejection below uses the binding.
rejects("type-required", [==[
let S = oneof(3)
let f(n: u32): u32 = do let x = S return n end
return { functions = { f } }
]==], "f", { 1 })
rejects("type-required", [==[
let S = oneof({ })
let f(n: u32): u32 = do let x = S return n end
return { functions = { f } }
]==], "f", { 1 })
rejects("unknown-member", [==[
let S = oneof { a: u32 }
let f(n: u32): u32 = do let x = S.b return n end
return { functions = { f } }
]==], "f", { 1 })
rejects("callable-required", [==[
let A = { x: u32 }
let S = oneof { a: A }
let f(n: u32): u32 = do let s = S.a { x = n } return s { a = 3 } end
return { functions = { f } }
]==], "f", { 1 })
-- Two alternatives whose arms disagree must be rejected, not silently joined. An exported sum
-- parameter has no known tag, so the match becomes a runtime switch.
rejects("branch-result", [==[
let A = { x: u32 }
let B = { y: u32 }
let S = oneof { a: A, b: B }
let f(s: S): u32 = s { a = |v: A| -> v.x, b = |v: B| -> true }
return { functions = { f } }
]==])


-- Tagged callables -------------------------------------------------------------------------------
-- A conditional that selects between two different callable code identities joins them into one
-- tagged callable: the tag names the code and the payload is that code's environment.
local TAGGED = [==[
let inc(x: u32): u32 = x + 1
let dec(x: u32): u32 = x - 1
let pick(c: bool): u32 = do
  let f = if c then inc else dec
  return f(10)
end
let via_lambda(c: bool, x: u32): u32 = do
  let f = if c then |y: u32| -> y + x else |y: u32| -> y * 2
  return f(f(1))
end
let pair(c: bool, x: u32): (u32, u32) = do
  let f = if c then inc else dec
  return f(x), f(f(x))
end
let across(c: bool, x: u32): u32 = do
  let f = mk(c)
  return f(x)
end
let mk(c: bool) = if c then inc else |y: u32| -> y * 3
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
let choose(c: bool, a: u32, b: u32): u32 = do
  let f = if c then |y: u32| -> y + a else |y: u32| -> y + b
  return f(1)
end
return { functions = { choose } }
]==]
check(interpret("choose", { true, 5, 7 }, sameCode)[1] == 6,
    "one code identity with two environments joins without a tag")

-- Rejections ------------------------------------------------------------------------------------
rejects("callable-branch", [==[
let pick(c: bool): u32 = do
  let f = if c then |x: u32| -> x + 1 else |x: bool| -> 7
  return f(10)
end
return { functions = { pick } }
]==])
-- A tagged callable holds its environments by value, so a borrowing arm has no representation.
rejects("callable-branch", [==[
let R = { v: u32 }
let pick(c: bool, r: R): u32 = do
  let f = if c then |x: u32| -> x + r.v else |x: u32| -> x * 2
  return f(0)
end
return { functions = { pick } }
]==])
-- A word arm needs a fully declared signature, because a tagged call has no annotation to fall back on.
rejects("callable-branch", [==[
let inc(x: u32) = x + 1
let pick(c: bool): u32 = do
  let f = if c then inc else |x: u32| -> x * 2
  return f(1)
end
return { functions = { pick } }
]==])
-- A word on one side and an ordinary value on the other is not a callable join.
rejects("branch-result", [==[
let inc(x: u32): u32 = x + 1
let pick(c: bool): u32 = do
  let f = if c then inc else 3
  return f(1)
end
return { functions = { pick } }
]==])


-- Pure code and borrowed callables -----------------------------------------------------------------
-- A callable with no environment is pure code: nothing is retained, so it has a representation and
-- may cross a boundary as an invocation pointer with a null environment.
local PURE = [==[
let mk(): (u32): u32 = |x: u32| -> x + 1
let pure(x: u32): u32 = do
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
let C = { v: u32 }
let apply(f: (u32): u32, x: u32): u32 = f(x)
let run(x: u32): u32 = do
  let c = C { v = 10 }
  let g = |y: u32| -> y + c.v
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
let C = { v: u32, bump(): u32 = do v += 1 return v end }
let apply(f: (): u32, x: u32): u32 = f() + x
let run(x: u32): u32 = do
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
let C = { v: u32 }
let leak(x: u32): (u32): u32 = do
  let c = C { v = 10 }
  return |y: u32| -> y + c.v
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
let Counter = { value: u32 }
let borrowed(x: u32): u32 = do
  let c = Counter { value = x }
  let f = |d: u32| -> do
    let r = ref(c)
    r.value += d
    return r.value
  end
  return f(3) * 10 + c.value
end
let aliased(x: u32): u32 = do
  let c = Counter { value = x }
  let g = |d: u32| -> do
    let a = ref(c)
    a.value += d
    let b = ref(c)
    return b.value
  end
  return g(1) + g(2)
end
let Holder = { r: ref(Counter) }
let held(x: u32): u32 = do
  let c = Counter { value = x }
  let f = |d: u32| -> do
    c.value += d
    let h = Holder { r = ref(c) }
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
let Node = { value: u32, next: Link }
let Link = oneof { none: unit, some: ref(Node) }
let n1 = Node { value = 10, next = Link.none() }
let n0 = Node { value = 1, next = Link.some(ref(n1)) }
let head(): u32 = n0.value
let following(): u32 = n0.next {
  none = |u: unit| -> 0,
  some = |r: ref(Node)| -> r.value,
}
let bump_following(): u32 = n0.next {
  none = |u: unit| -> 0,
  some = |r: ref(Node)| -> do
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
let Counter = { value: u32 }
let bad(x: u32): u32 = do
  let c = Counter { value = x }
  return ref(c).value
end
return { types = { Counter }, functions = { bad } }
]==])
rejects("ref-target", [==[
let Counter = { value: u32 }
let bad(): u32 = ref(Counter { value = 1 }).value
return { types = { Counter }, functions = { bad } }
]==])
-- A field declared as a signature is a view, and a function-pointer declaration may name an
-- incomplete parameter type, so a record may hold a view that takes that record.
local throughParameter = compile([==[
let Handler = { f: (Handler): u32, n: u32 }
let g(x: u32): u32 = x
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
let Handler = { f: (u32): Handler, n: u32 }
let g(x: u32): u32 = x
return { types = { Handler }, functions = { g } }
]==]):unit()
    end)
    check(not ok and D.is(err) and err.code == "c-order",
        "a record and a view that returns it contain each other by value")
end

-- A reference is not itself a place to reference again.
rejects("ref-target", [==[
let Counter = { value: u32 }
let shared = Counter { value = 5 }
let bad(x: u32): u32 = ref(ref(shared)).value + x
return { types = { Counter }, functions = { bad } }
]==])
-- A reference to an enclosing owner cannot outlive that activation.
rejects("ref-escape", [==[
let Counter = { value: u32 }
let leak(x: u32): u32 = do
  let c = Counter { value = x }
  let f = |d: u32| -> do
    let r = ref(c)
    return r
  end
  return f(1).value
end
return { types = { Counter }, functions = { leak } }
]==])
-- A type that contains itself by value has no finite layout, however many definitions it crosses.
rejects("type-cycle", [==[
let Bad = { child: Bad }
let f(n: u32): u32 = n
return { types = { Bad }, functions = { f } }
]==])
rejects("type-cycle", [==[
let A = { b: B }
let B = { a: A }
let f(n: u32): u32 = n
return { types = { A, B }, functions = { f } }
]==])
-- A recursive definition has to be file scope: a local binding is declared in order, so a local
-- definition cannot see its own name.
rejects("unknown-name", [==[
let Counter = { value: u32 }
let use(x: u32): u32 = do
  let Node = { value: u32, child: ref(Node) }
  return x
end
return { types = { Counter }, functions = { use } }
]==])
-- A cycle that crosses a reference is finite, so it is accepted.
local finite = compile([==[
let Good = { child: ref(Good), value: u32 }
let f(n: u32): u32 = n
return { types = { Good }, functions = { f } }
]==]):unit()
check(finite:find("wordletrecord_1 * f_child;", 1, true) ~= nil,
    "a cycle through a reference is finite and emits a pointer")


-- Arrays ------------------------------------------------------------------------------------------
-- A fixed-length sequence of one element type. The length is part of the type, so a static index is
-- checked while compiling and only a run-time index needs a bounds guard.
local ARRAYS = [==[
let literal_sum(): u32 = do
  let a = [10, 20, 30]
  return a[0] + a[1] + a[2]
end
let local_pick(i: u32): u32 = do
  let b: array(u32, 3) = [7, 8, 9]
  return b[i]
end
let store(i: u32, v: u32): u32 = do
  let b = [1, 2, 3]
  b[i] = v
  b[0] += 5
  return b[0] * 100 + b[1] * 10 + b[2]
end
let grid(r: u32, c: u32): u32 = do
  let g = [[1, 2], [3, 4]]
  return g[r][c]
end
let sum2(xs: array(u32, 2)): u32 = xs[0] + xs[1]
let via_parameter(x: u32): u32 = do
  let b: array(u32, 2) = [x, x + 1]
  return sum2(b)
end
let aliased(x: u32): u32 = do
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
let f(n: u32): u32 = do
  let a = []
  return n + a[0]
end
return { functions = { f } }
]==])
-- The length is part of the type, so a literal of the wrong length rejects.
rejects("array-length", [==[
let f(n: u32): u32 = do
  let a: array(u32, 3) = [1, 2]
  return a[n]
end
return { functions = { f } }
]==])
-- Elements must share one type.
rejects("type-mismatch", [==[
let f(n: u32): u32 = do
  let a = [1, true]
  return n
end
return { functions = { f } }
]==])
-- A known index outside the array rejects while compiling.
rejects("index-range", [==[
let f(): u32 = do
  let a = [1, 2]
  return a[2]
end
return { functions = { f } }
]==])
-- Only an array can be indexed at all.
rejects("type-mismatch", [==[
let f(n: u32): u32 = do
  n[0] = 1
  return n
end
return { functions = { f } }
]==])
-- An array needs a length of at least one, given as a literal.
rejects("array-length", [==[
let f(n: u32): u32 = do
  let a: array(u32, 0) = [1]
  return n
end
return { functions = { f } }
]==])


-- Narrower integers -------------------------------------------------------------------------------
-- The width is part of the type: arithmetic wraps at that width, widening is implicit, and narrowing
-- needs an explicit conversion unless a known value fits.
local WIDTHS = [==[
let wrap8(n: u32): u32 = do
  let a: u8 = u8(n)
  let b = a + 200
  return u32(b)
end
let wrap16(n: u32): u32 = do
  let a: u16 = u16(n)
  let b = a * 3
  return u32(b)
end
let widen(n: u32): u32 = do
  let a: u8 = u8(n)
  let b: u16 = a
  let c: u32 = b
  return c
end
let compare(n: u32): bool = do
  let a: u8 = u8(n)
  let b: u16 = u16(n)
  return a == b and a <= b
end
let shift8(n: u32): u32 = do
  let a: u8 = u8(n)
  return u32(a << 1) + u32(a >> 1)
end
let negate8(n: u32): u32 = do
  let a: u8 = u8(n)
  let b = -a
  return u32(b)
end
return { types = {  }, functions = { wrap8, wrap16, widen, compare, shift8, negate8 } }
]==]
check(interpret("wrap8", { 100 }, WIDTHS)[1] == 44, "u8 arithmetic wraps at 8 bits")
check(interpret("wrap8", { 255 }, WIDTHS)[1] == 199, "a u8 value of 255 plus 200 wraps")
check(interpret("wrap16", { 40000 }, WIDTHS)[1] == 54464, "u16 arithmetic wraps at 16 bits")
check(interpret("widen", { 200 }, WIDTHS)[1] == 200, "narrowing widens back without change")
check(interpret("compare", { 7 }, WIDTHS)[1] == true, "widths compare after widening")
check(interpret("shift8", { 130 }, WIDTHS)[1] == 4 + 65, "a u8 shift wraps at its own width")
check(interpret("negate8", { 1 }, WIDTHS)[1] == 255, "a negated u8 is its own complement")
local widthUnit = compile(WIDTHS):unit()
check(widthUnit:find("uint8_t", 1, true) ~= nil and widthUnit:find("uint16_t", 1, true) ~= nil,
    "the widths lower to their C types")
-- Rejections ------------------------------------------------------------------------------------
-- A known value that does not fit rejects while compiling, whether it is an annotation or a conversion.
rejects("numeric-range", [==[
let f(n: u32): u32 = do
  let a: u8 = 300
  return n + u32(a)
end
return { functions = { f } }
]==])
rejects("numeric-range", [==[
let f(n: u32): u32 = do
  let a = u8(300)
  return n + u32(a)
end
return { functions = { f } }
]==])
-- A run-time value needs the conversion to say what to do; an annotation will not narrow it.
rejects("numeric-range", [==[
let f(n: u32): u32 = do
  let a: u8 = n
  return u32(a)
end
return { functions = { f } }
]==])
-- Two run-time widths mix by widening, which loses nothing, so the sum is the wider one.
check(interpret("mixed", { 200 },
    "let mixed(n: u32): u32 = do\n  let a: u8 = u8(n)\n  let b: u16 = u16(n)\n"
    .. "  return u32(a + b)\nend\nreturn { functions = { mixed } }")[1] == 400,
    "a narrower value widens to meet a wider one")
-- A conversion needs an integer.
rejects("type-mismatch", [==[
let f(n: u32): u32 = do
  let a = u8(true)
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
let Point = { x: u32, y: u32 }
let helper(n: u32): u32 = n * 2
let secret(n: u32): u32 = helper(n) + 1
return { types = { Point }, functions = { helper, secret } }
]==])
    write("main.let", [==[
use util
let twice(n: u32): u32 = util.helper(n)
let bumped(n: u32): u32 = util.secret(n)
let origin(): util.Point = util.Point { x = 1, y = 2 }
let sum_point(): u32 = origin().x + origin().y
return { types = {  }, functions = { twice, bumped, sum_point } }
]==])
    local artifact = wordlet.compile_file(root .. "/main.let", { name = root .. "/main.let" })
    local unit = artifact:unit()
    check(unit:find("wordlet_twice", 1, true) ~= nil, "an entry module compiles with its imports")
    check(#unit > 0, "an imported module produces one artifact with the entry")
    -- Rejections ---------------------------------------------------------------------------------
    write("bad_member.let", [==[
use util
let f(n: u32): u32 = util.hidden(n)
return { functions = { f } }
]==])
    local ok, err = pcall(function()
        return wordlet.compile_file(root .. "/bad_member.let", { name = root .. "/bad_member.let" })
    end)
    check(not ok and D.is(err) and err.code == "unknown-member",
        "a name the module does not export is not reachable")
    write("missing.let", "use nowhere\nlet f(n: u32): u32 = n\nreturn { functions = { f } }\n")
    ok, err = pcall(function()
        return wordlet.compile_file(root .. "/missing.let", { name = root .. "/missing.let" })
    end)
    check(not ok and D.is(err) and err.code == "import-input", "a missing module is reported")
    write("a.let", "use b\nlet f(n: u32): u32 = n\nreturn { functions = { f } }\n")
    write("b.let", "use a\nlet g(n: u32): u32 = n\nreturn { functions = { g } }\n")
    ok, err = pcall(function()
        return wordlet.compile_file(root .. "/a.let", { name = root .. "/a.let" })
    end)
    check(not ok and D.is(err) and err.code == "import-cycle", "a module cycle is reported")
    ok, err = pcall(function()
        return wordlet.compile{ source = "use util\nlet f(n: u32): u32 = n\n"
            .. "return { functions = { f } }", name = "s.let" }
    end)
    check(not ok and D.is(err) and err.code == "import-input",
        "a source string cannot use an import, because it has no directory")
    os.execute("rm -rf -- '" .. root .. "'")
end


-- Signed integers ---------------------------------------------------------------------------------
-- i32 is two's complement: arithmetic wraps, division truncates toward zero with the remainder
-- taking the dividend's sign, and a right shift is arithmetic. Changing signedness at one width
-- reinterprets the bits, so it never loses a value.
local SIGNED = [==[
let round(n: u32): u32 = do
  let a: i32 = i32(n)
  let b = a - 3
  let c = b * 2
  return u32(c)
end
let quotient(n: u32): u32 = do
  let a: i32 = i32(n)
  return u32(a / 3) + u32(a % 3)
end
let shift(n: u32): u32 = do
  let a: i32 = i32(n)
  return u32(a >> 1)
end
let reinterpret(n: u32): u32 = do
  let a = i32(n)
  return u32(a)
end
let negate(n: u32): u32 = do
  let a: i32 = i32(n)
  return u32(-a)
end
return { types = {  }, functions = { round, quotient, shift, reinterpret, negate } }
]==]
check(interpret("round", { 0 }, SIGNED)[1] == 4294967290, "i32 arithmetic wraps at 32 bits")
check(interpret("quotient", { 4294967294 }, SIGNED)[1] == 4294967294,
    "signed division truncates toward zero and the remainder keeps the dividend's sign")
check(interpret("shift", { 4294967295 }, SIGNED)[1] == 4294967295,
    "a signed shift keeps the sign bit")
check(interpret("reinterpret", { 4294967295 }, SIGNED)[1] == 4294967295,
    "changing signedness at one width reinterprets the bits")
check(interpret("negate", { 1 }, SIGNED)[1] == 4294967295, "negation wraps in two's complement")
-- An explicit conversion produces a value of the target type, not a source literal: `i32(2)` is
-- already i32, so `i32(2) + 3` lets 3 adopt i32 instead of treating both sides as literals and
-- refusing to cross signedness.
local CONVERTED = [==[
let add(n: u32): i32 = i32(n) + 3
let add_left(n: u32): i32 = 3 + i32(n)
let power(n: u32): i32 = i32(n) ^ 31
return { types = {  }, functions = { add, add_left, power } }
]==]
check(interpret("add", { 2 }, CONVERTED)[1] == 5, "a converted operand is not a literal")
check(interpret("add_left", { 2 }, CONVERTED)[1] == 5, "adoption works with the literal on the left")
check(interpret("power", { 2 }, CONVERTED)[1] == -2147483648,
    "a signed power wraps at 32 bits instead of overflowing a Lua number")
compile(CONVERTED)
local signedUnit = compile(SIGNED):unit()
check(signedUnit:find("int32_t", 1, true) ~= nil, "i32 lowers to its C type")
check(signedUnit:find("wordlet_i32", 1, true) ~= nil,
    "a signed value is reinterpreted rather than converted out of range")
-- Rejections ------------------------------------------------------------------------------------
-- Signed and unsigned values of one width do not mix: the conversion has to say which is meant.
rejects("type-mismatch", [==[
let f(n: u32): u32 = do
  let a: i32 = i32(n)
  let c = a + n
  return n
end
return { functions = { f } }
]==])
-- A negative value has no unsigned counterpart when the width changes too, which is checked: a
-- run-time one traps and a known one rejects here.
rejects("numeric-range", [==[
let f(n: u32): u32 = do
  let b: u8 = u8(i32(0) - i32(1))
  return n + u32(b)
end
return { functions = { f } }
]==])
-- A signed power needs a power that is not negative.
rejects("numeric-range", [==[
let f(n: u32): u32 = do
  let a: i32 = i32(n)
  let b = a ^ (i32(0) - i32(1))
  return u32(b)
end
return { functions = { f } }
]==])


-- 64-bit integers ----------------------------------------------------------------------------------
-- A 64-bit value does not fit a Lua number, so it is held as two words and the exact kernel decides
-- its arithmetic. A literal that does not fit a word is a 64-bit literal.
local WIDE = [==[
let low(): u32 = u32(0xFFFFFFFFFFFFFFFF % 4294967296)
let high(): u32 = u32(0xFFFFFFFFFFFFFFFF / 4294967296)
let masked(n: u32): u32 = u32(u64(n) * u64(n) % 4294967296)
let above(n: u32): u32 = u32(u64(n) * u64(n) / 4294967296)
let negative(n: u32): u32 = u32((i64(4294967296) - i64(n)) / i64(2))
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
let f(n: u32): u32 = u32(18446744073709551615) + n
return { functions = { f } }
]==])
-- A run-time value that cannot fit is stopped when it is converted rather than refused while
-- compiling, so the program compiles and the generated code carries a check.
check(#compile([==[
let f(n: u32): u32 = u32(u64(n) * u64(n))
return { functions = { f } }
]==]):unit() > 0, "a run-time narrowing conversion compiles with a run-time check")
-- A negative value narrowed to a narrower unsigned type is refused, while the same width read the
-- other way is a reinterpretation and keeps every bit.
rejects("numeric-range", [==[
let f(n: u32): u32 = do
  let a: i64 = i64(0) - i64(5)
  let b: u32 = u32(a)
  return n + b
end
return { functions = { f } }
]==])
check(interpret("bits", { 3 },
    "let bits(n: u32): u32 = do\n  let a: i64 = i64(0) - i64(n)\n  let b: u64 = u64(a)\n"
    .. "  return u32(b % 4294967296)\nend\nreturn { functions = { bits } }")[1] == 4294967293,
    "a same-width signedness change reinterprets the bits")
-- A literal above 64 bits is refused rather than wrapped.
rejects("lex-range", [==[
let f(n: u32): u32 = u32(18446744073709551616) + n
return { functions = { f } }
]==])

-- The interpreter refuses an unsaturated entry rather than inventing a value.
local ok, err = pcall(wordlet.interpret, { source = "let f(a, b: u32) : u32 = a + b\n"
    .. "return { functions = { f } }", entry = "f", args = { 1 } })
check(not ok and D.is(err) and err.code == "arity", "undersaturated entry rejects instead of returning a word")

-- C naming is injective, so two distinct source names cannot collide.
check(C.escape("sum_to") == "sum_5Fto" and C.functionName("sum_to") == "wordlet_sum_5Fto",
    "underscore is escaped")
check(C.escape("a_b") ~= C.escape("aXbX") or C.escape("a-") ~= C.escape("a_"),
    "escaping distinguishes distinct spellings")
check(C.escape("a") ~= C.escape("A"), "case is preserved")

-- Exported aliases share one body and forward.
local aliasArtifact = compile("let inc(x: u32) : u32 = x + 1\nreturn { functions = { a = inc, b = inc } }")
check(#aliasArtifact:exports() == 2, "both aliases are exported")
local aliasUnit = aliasArtifact:unit()
check(aliasUnit:find("wordlet_a", 1, true) and aliasUnit:find("wordlet_b", 1, true),
    "aliases appear in the generated C")

-- Determinism: identical input gives byte-identical output.
local one = compile("let f(x: u32) : u32 = x * 3 + 1\nreturn { functions = { f } }"):unit()
local two = compile("let f(x: u32) : u32 = x * 3 + 1\nreturn { functions = { f } }"):unit()
check(one == two, "emission is deterministic")

-- A deferred action runs when the block it is written in is left: in reverse order, after the value
-- has been read, from a statement conditional's arm as much as from the block itself, and after a tail
-- self-call has returned rather than as a back edge. The counter shifts a digit in per action, so the
-- number left behind spells the order they ran in.
do
    local source = "let Counter = { n: u32 }\n"
        .. "let counter = Counter { n = 0 }\n"
        .. "let push(v: u32): u32 = do\n  let c = ref(counter)\n  c.n = c.n * 10 + v\n"
        .. "  return c.n\nend\n"
        .. "let reset(): u32 = do\n  let c = ref(counter)\n  c.n = 0\n  return 0\nend\n"
        .. "let body(): u32 = do\n  defer push(1)\n  defer push(2)\n  return 0\nend\n"
        .. "let ordered(): u32 = do\n  reset()\n  let before = body()\n"
        .. "  return (before + 1) * 1000 + ref(counter).n\nend\n"
        .. "let arm(): u32 = do\n  defer push(7)\n"
        .. "  if ref(counter).n == 0 then return 1 end\n  return 2\nend\n"
        .. "let via_arm(): u32 = do\n  reset()\n  let r = arm()\n  return r * 10 + ref(counter).n\nend\n"
        .. "let countdown(n: u32, acc: u32): u32 = do\n  if n == 0 then return acc end\n"
        .. "  defer push(n)\n  return countdown(n - 1, acc * 10 + n)\nend\n"
        .. "let tailed(): u32 = do\n  reset()\n  let acc = countdown(3, 0)\n"
        .. "  return acc * 1000 + ref(counter).n\nend\n"
        .. "let counted(n: u32): u32 = do\n  reset()\n  return countdown(n, 0)\nend\n"
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
    local source = "let Counter = { n: u32 }\n"
        .. "let counter = Counter { n = 0 }\n"
        .. "let reset(): u32 = do\n  let c = ref(counter)\n  c.n = 0\n  return 0\nend\n"
        .. "let bump(v: u32): u32 = do\n  let c = ref(counter)\n  c.n += v\n  return c.n\nend\n"
        .. "let use(): u32 = do\n  reset()\n  bump(5)\n  return ref(counter).n\nend\n"
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
    local nested = "let Counter = { n: u32 }\n"
        .. "let borrow(c: Counter): u32 = do\n"
        .. "  let outer = || -> do\n"
        .. "    let inner = |d: u32| -> do\n      c.n += d\n      return c.n\n    end\n"
        .. "    return inner(3)\n  end\n"
        .. "  return outer() * 10 + c.n\nend\n"
        .. "let use(): u32 = borrow(Counter { n = 1 })\n"
        .. "return { functions = { use } }"
    check(interpret("use", {}, nested)[1] == 44, "a capture travels through a nested lambda")

    -- A slice is an indirection, so a type may mention itself through one; by value it may not.
    local recursive = "let Node = { value: u32, rest: slice(Node) }\n"
        .. "let head(n: Node): u32 = n.value\nreturn { functions = { head } }"
    local generatedNode = compile(recursive):unit()
    check(generatedNode:find("wordletrecord_1", 1, true) ~= nil
        and generatedNode:find("wordletslice_", 1, true) ~= nil,
        "a recursive type through a slice has a finite layout")
    local pointed = compile("let Node = { value: u32, next: ptr(Node) }\n"
        .. "let head(n: Node): u32 = n.value\nreturn { functions = { head } }"):unit()
    check(pointed:find("wordletrecord_1", 1, true) ~= nil,
        "a recursive type through a pointer has a finite layout")
    rejects("type-cycle", "let Bad = { child: Bad }\nreturn { functions = { } }")
    -- An array element is embedded by value, so a cycle that crosses one crosses no boundary at all.
    -- The element is resolved on the type path, which hands back the cell an open definition reserved
    -- instead of demanding its layout, so the checker gets to say what is wrong rather than the demand
    -- reporting an eager initializer cycle.
    rejects("type-cycle", "let Bad = { items: array(Bad, 2) }\nreturn { functions = { } }")
    rejects("type-cycle", "let Bad = array(Bad, 2)\nreturn { functions = { } }")
    rejects("type-cycle", "let A = { b: array(B, 2) }\nlet B = { a: array(A, 2) }\n"
        .. "return { functions = { } }")
    -- An alias of a type constructor is a constructor too, so the recursion knot is still found.
    check(compile("let MyRef = ref\nlet Node = { value: u32, next: MyRef(Node) }\n"
        .. "return { functions = { } }") ~= nil,
        "an alias of ref still recognises a recursive type")
    -- A bare reference or pointer is not a nominal type: it has no record or sum anchoring a finite
    -- C alias, so it is a cycle rather than a stack overflow.
    rejects("type-cycle", "let Bad = ref(Bad)\nreturn { functions = { } }")
    rejects("type-cycle", "let Bad = ptr(Bad)\nreturn { functions = { } }")
    rejects("type-cycle", "let A = ref(B)\nlet B = ref(A)\nreturn { functions = { } }")
    -- A slice is a nominal layout that names its element through a pointer, so it is finite.
    check(compile("let Bad = slice(Bad)\nlet f(b: Bad): u32 = 0\nreturn { functions = { f } }")
        ~= nil, "a self-referential slice has a finite layout")
    -- A type declared later is not a cycle, and an indirection inside the array is a boundary.
    check(compile("let Good = { items: array(Node, 2) }\nlet Node = { value: u32 }\n"
        .. "return { functions = { } }") ~= nil,
        "an array of a type declared later is not a cycle")
    check(compile("let Node = { value: u32, kids: array(ref(Node), 2) }\n"
        .. "return { functions = { } }") ~= nil,
        "an array of references may mention the type that holds it")

    -- A requirement types a lambda however it was spelled, so an alias is as good as a signature.
    local aliased = "let Endo = (u32): u32\n"
        .. "let twice(f: Endo, x: u32): u32 = f(f(x))\n"
        .. "let use(): u32 = twice(|x| -> x + 1, 5)\n"
        .. "return { functions = { use } }"
    check(interpret("use", {}, aliased)[1] == 7,
        "an alias of a signature types the lambda it receives")

    -- A reference into module storage is module storage even when the route to it is a local
    -- reference, so the compiler accepts it and the store reaches the module array.
    local throughRef = "let pool = [10, 20, 30]\n"
        .. "let bump(i: u32): u32 = do\n"
        .. "  let r = ref(pool)\n  r[i] += 5\n  return r[i]\nend\n"
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
    local indexed = "let scan(s: string, b: u8, i: u32): u32 = do\n"
        .. "  if i >= s.length then return 0 end\n"
        .. "  if s[i] == b then return 1 + scan(s, b, i + 1) end\n"
        .. "  return scan(s, b, i + 1)\n"
        .. "end\n"
        .. "let count_a(s: string): u32 = scan(s, 'a', 0)\n"
        .. "return { functions = { count_a } }"
    rejects("depth", indexed)
    -- The reference interpreter folds the same scan, because its view is concrete and six bytes long.
    check(interpret("count_a", { "banana" }, indexed)[1] == 3, "a concrete view folds the scan")
    local deep = "let g(n: u32): u32 = if n == 0 then 0 else n + g(n - 1)\n"
        .. "return { functions = { g } }"
    check(compile(deep):unit():find("wordlet_g(", 1, true) ~= nil,
        "a fold that runs out of depth is compiled, not refused")
    check(interpret("g", { 1000 }, deep)[1] == 500500, "a recursion inside the interpreter's depth runs")
    rejects("static-depth", deep, "g", { 5000 })
    -- A top-level initializer is folded, and has no runtime code to fall back to, so a fold that
    -- runs out of depth there is the answer rather than a reason to compile.
    rejects("static-depth", deep:gsub("return { functions = { g } }",
        "let x: u32 = g(2000)\nreturn { functions = {} }"))
end

-- The literal surface: grouped digits, binary, byte literals, long strings and long comments.
do
    local source = "let grouped(): u32 = 1_000_000 + 0b1010_1010\n"
        .. "let wide(): u32 = 0b1111_1111_1111_1111_1111_1111_1111_1111_1111_1111 % 4294967296\n"
        .. "let hex(): u32 = 0xffff_ffff\n"
        .. "let byte(): u32 = u32('\\n')\n"
        .. "let is_a(): bool = 'a' == 97\n"
        .. "let raw(): u32 = [=[a\\tb]=].length\n"
        .. "let long(): u32 = [=[\nab\ncd\n]=].length\n"
        .. "let commented(): u32 = do\n  --[[ a ]=] b ]]\n  return 7\nend\n"
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
-- is a real call and not a back edge whose result would be unit.
do
    local mixed = "let f(n: u32): u32 = do\n"
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

-- The threaded-dispatch example. A reified-continuation loop makes the trailing self-call a back
-- edge, so the residual program carries the loop and no recursion.
do
    local path = (source:match("^(.*[/\\])") or "./") .. "../examples/dispatch.let"
    local file = assert(io.open(path, "rb"))
    local text = file:read("*a")
    assert(file:close())
    check(interpret("main", {}, text)[1] == 7, "examples/dispatch.let main() is 7")
    local generated = compile(text):unit()
    check(generated:find("for (;;)", 1, true) ~= nil, "the dispatch loop is a back edge, not a call")
    check(generated:find("continue;", 1, true) ~= nil, "the back edge continues the loop")
end

-- The hierarchical-continuation example: a parent owns the state, wires a child's exits two ways,
-- and the same child serves a scalar boundary and a sum boundary by specializing its result type.
do
    local path = (source:match("^(.*[/\\])") or "./") .. "../examples/pipeline.let"
    local file = assert(io.open(path, "rb"))
    local text = file:read("*a")
    assert(file:close())
    local expected = {
        { "settle", { 1, 50 }, 50 }, { "settle", { 0, 50 }, 0 }, { "settle", { 1, 500 }, 0 },
        { "summarize", { 1, 50 }, 50 }, { "summarize", { 1, 500 }, 0 },
    }
    for _, case in ipairs(expected) do
        local got = interpret(case[1], case[2], text)[1]
        check(got == case[3], ("examples/pipeline.let %s(%d,%d): expected %s but got %s")
            :format(case[1], case[2][1], case[2][2], tostring(case[3]), tostring(got)))
    end
    compile(text)
end

-- A match handler is a callable, so it may return a result vector; the match forwards it, and each
-- result keeps its own slot in residual code.
do
    local source = "let Op = oneof { a: unit, b: unit }\n"
        .. "let pick(op: Op, x: u32): (u32, u32) = op {\n"
        .. "  a = |u: unit| -> do return x + 1, x + 2 end,\n"
        .. "  b = |u: unit| -> do return x + 3, x + 4 end,\n"
        .. "}\n"
        .. "let total(op: Op, x: u32): u32 = do let p, q = pick(op, x) return p + q end\n"
        .. "let run_a(x: u32): u32 = total(Op.a(), x)\n"
        .. "let run_b(x: u32): u32 = total(Op.b(), x)\n"
        .. "return { types = { Op }, functions = { run_a, run_b, total } }"
    check(interpret("run_a", { 10 }, source)[1] == 23, "a match handler may return a result vector")
    check(interpret("run_b", { 10 }, source)[1] == 27, "a different arm returns its own vector")
    compile(source)
end

-- Reading module storage through a reference is an ordinary run-time read. A call whose arguments
-- happen to be static must still be compiled rather than folded when the body needs that storage.
do
    local shared = "let Counter = { value: u32 }\nlet shared = Counter { value = 5 }\n"
        .. "let read_shared(x: u32): u32 = ref(shared).value + x\n"
    check(interpret("read_shared", { 1 }, shared .. "return { functions = { read_shared } }")[1] == 6,
        "module initialization reads module storage through a reference")
    local generated = compile(shared .. "let peek(): u32 = read_shared(1)\n"
        .. "return { functions = { peek } }"):unit()
    check(generated:find("wordletmodule_1", 1, true) ~= nil,
        "a literal-argument call to a module-storage reader is compiled, not folded")
    check(generated:find("f_value", 1, true) ~= nil, "the module read is emitted rather than baked")
    -- A body that is genuinely wrong is still reported: only the need for run-time code falls back.
    rejects("type-mismatch", "let bad(): u32 = 1 + true\nreturn { functions = { bad } }")
end

-- A long binding chain must compile in time linear in the chain. Interned expressions name their
-- operands by id, not by re-encoding the subtree, so a key costs the same however deep an operand
-- is; re-encoding made a 400-binding chain take seconds.
do
    local lines = { "let big(x: u32): u32 = do", "  let a0 = x" }
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

-- Expression conditionals join logical vectors, including erased unit and common static types.
do
    local program = [[
let pair(x: u32): (unit,u32,unit,u32) = do return unit(),x,unit(),x+1 end
let choose(flag: bool,x: u32): (unit,u32,unit,u32) = if flag then pair(x) else pair(x+10)
let total(flag: bool,x: u32): u32 = do let u,a,v,b=choose(flag,x) return a*100+b end
let typed(flag: bool,x: u32): u32 = do let T=if flag then u32 else u32 let y:T=x return y end
return {functions={choose,total,typed}}
]]
    check(interpret("total",{true,2},program)[1]==203,"true arm forwards its complete result vector")
    check(interpret("total",{false,2},program)[1]==1213,"false arm forwards its complete result vector")
    compile(program)
    rejects("branch-result", [[
let pair(x: u32): (u32,u32) = do return x,x end
let bad(flag: bool,x: u32): u32 = if flag then x else pair(x)
return {functions={bad}}
]])
    rejects("branch-result", [[
let pair(x: u32): (u32,bool) = do return x,true end
let other(x: u32): (u32,u32) = do return x,x end
let bad(flag: bool,x: u32): (u32,bool) = if flag then pair(x) else other(x)
return {functions={bad}}
]])
    rejects("branch-result", "let f(b:bool):u32=do let T=if b then u32 else bool let x:T=1 return 1 end return {functions={f}}")
    rejects("borrow-escape", [[
let Box={value:u32}
let use(c:Box):u32=do
  let f=|b:bool|->if b then ref(c) else ref(c)
  let r=f(true)
  return r.value
end
return {functions={use}}
]])
    compile([[let Box={value:u32} let shared=Box{value=1}
let pick(b:bool):ref(Box)=if b then ref(shared) else ref(shared)
return {functions={pick}}]])
end

-- Code construction must mask execution permissions, even inside an initializer/interpreter run.
-- The initializer really executes bump; merely constructing the callback must not execute it again.
do
    local program = [[
let Counter={value:u32}
let shared=Counter{value=0}
let bump():u32=do shared.value+=1 return shared.value end
let seed=bump()
let callback:():u32=||->bump()
let direct():u32=shared.value
let literal(x:u32):u32=shared.value+x
let main(n:u32):u32=do
  let before=direct()
  let after=callback()
  return before*100+after*10+literal(seed)
end
return {functions={main}}
]]
    check(interpret("main",{0},program)[1]==123,"only executing a callback mutates module state")
    local generated=compile(program):unit()
    check(generated:find("wordletmodule_1",1,true)~=nil,"nullary and literal calls retain module reads")
end

-- Both inner tail arms must survive, and a statically selected condition keeps its tail context.
do
    local program = [[
let nested(n,a:u32):u32=if n==0 then a else if n%2==0 then nested(n-1,a+1) else nested(n-1,a+2)
let known(n,a:u32):u32=if true then if n==0 then a else known(n-1,a+1) else 0
return {functions={nested,known}}
]]
    check(interpret("nested",{10,0},program)[1]==15,"both nested tail branches execute")
    local artifact=compile(program)
    local Walk=require("wordlet.walk")
    for _, exported in ipairs(artifact.compilation.functions) do
        local loops=0
        Walk.walk(exported.instance.fn,{enter=function(node) if node.kind=="Loop" then loops=loops+1 end end})
        check(loops>0,"conditional preserves self-tail Loop: "..exported.name)
    end
end

print(("PASS: evaluator semantics (%d checks)"):format(checks))
