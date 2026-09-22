-- Differential tests: the reference interpreter and the generated C must agree.
-- Requires a C11 compiler (CC) and GNU timeout.
local source = debug.getinfo(1, "S").source:sub(2)
package.path = (source:match("^(.*[/\\])") or "./") .. "../?.lua;"
    .. (source:match("^(.*[/\\])") or "./") .. "../?/init.lua;" .. package.path

local wordlet = require("wordlet")
local C = require("wordlet.cabi")
local S = require("wordlet.schema")
local D = require("wordlet.diag")
local checks = 0
local function check(ok, message) assert(ok, message) checks = checks + 1 end

local CC = os.getenv("CC") or "cc"
local timeout = os.getenv("WORDLET_TIMEOUT") or "20s"
local directory = os.tmpname()
os.remove(directory)
assert(os.execute("mkdir -p -- '" .. directory .. "'") ~= nil)

local function write(path, text)
    local file = assert(io.open(path, "wb"))
    assert(file:write(text))
    assert(file:close())
end
local function read(path)
    local file = assert(io.open(path, "rb"))
    local text = assert(file:read("*a"))
    assert(file:close())
    return text
end
-- LuaJIT follows Lua 5.1: os.execute returns the raw status, so success is 0 rather than true.
local function shell(command)
    local first, how = os.execute(command)
    if first == true or first == 0 then return 0 end
    if first == nil then return how end
    return first
end

-- A field's C name is the source name escaped, the same rule the backend uses.
local function cField(name) return "f_" .. C.escape(name) end

-- Asserts one interpreted value against the C value at `path`. Records compare field by field,
-- a variant compares its canonical tag index and then its payload member, and a reference compares
-- what it points at. A structure that points back at itself is only checked for being present.
local function assertValue(checks, path, value)
    local kind = type(value)
    if kind == "number" then
        checks[#checks + 1] = "    assert((" .. path .. ") == UINT32_C(" .. value .. "));"
    elseif kind == "boolean" then
        checks[#checks + 1] = "    assert((" .. path .. ") == " .. (value and "true" or "false") .. ");"
    elseif value == "unit" then
        checks[#checks + 1] = "    (void)(" .. path .. ");"
    elseif kind == "table" and value.record then
        local any = false
        for name, field in pairs(value) do
            if name ~= "record" then
                any = true
                assertValue(checks, path .. "." .. cField(name), field)
            end
        end
        if not any then checks[#checks + 1] = "    (void)(" .. path .. ");" end
    elseif kind == "table" and value.array then
        -- An array is a struct holding a C array, so its elements are indexed positionally.
        local any = false
        for index, item in ipairs(value) do
            any = true
            assertValue(checks, path .. ".f_data[" .. (index - 1) .. "]", item)
        end
        if not any then checks[#checks + 1] = "    (void)(" .. path .. ");" end
    elseif kind == "table" and value.variant then
        checks[#checks + 1] = "    assert((" .. path .. ").wordlet_tag == " .. tostring(value.tag) .. ");"
        if value.payload ~= "unit" then
            assertValue(checks, path .. ".payload." .. cField(value.case), value.payload)
        end
    elseif kind == "table" and value.ref then
        assertValue(checks, "(*(" .. path .. "))", value.target)
    elseif kind == "table" and value.cycle then
        checks[#checks + 1] = "    (void)(" .. path .. ");"
    else
        error("unsupported expected result: " .. tostring(value))
    end
end

-- The C type a call returns, read from its prototype in the generated header.
local function resultType(unit, name)
    return unit:match("([%w_]+)%s+" .. name .. "%s*%(")
end

-- Source programs exercised end to end. Each case lists concrete input vectors; expected results
-- are produced by the interpreter, then asserted by the compiled C.
local CASES = {
    {
        name = "affine",
        source = "let affine(a, b, x: U32) : U32 = a * x + b\nreturn { functions = { affine } }",
        entry = "affine", arity = 3,
        inputs = { { 3, 7, 4 }, { 1, 0, 0 }, { 4294967295, 1, 1 }, { 65536, 65536, 65537 } },
    },
    {
        name = "branch",
        source = "let pick(x: U32) : U32 = if x == 0 then 7 else x * 2\nreturn { functions = { pick } }",
        entry = "pick", arity = 1,
        inputs = { { 0 }, { 1 }, { 2147483648 }, { 4294967295 } },
    },
    {
        name = "comparison",
        source = "let classify(x: U32) : U32 = if x < 10 then 1 else if x == 10 then 2 else 3\n"
            .. "return { functions = { classify } }",
        entry = "classify", arity = 1,
        inputs = { { 0 }, { 9 }, { 10 }, { 11 }, { 4294967295 } },
    },
    {
        name = "results",
        source = "let divmod(a, b: U32) : (U32, U32) = do return a / b, a % b end\n"
            .. "let recompose(a, b: U32) : U32 = do let q, r = divmod(a, b) return q * b + r end\n"
            .. "return { functions = { divmod, recompose } }",
        entries = { { entry = "divmod", arity = 2 }, { entry = "recompose", arity = 2 } },
        inputs = { { 17, 5 }, { 1, 1 }, { 4294967295, 3 }, { 100, 7 } },
    },
    {
        name = "calls",
        source = "let inc(x: U32) : U32 = x + 1\n"
            .. "let twice(x: U32) : U32 = inc(inc(x))\n"
            .. "let offset(x: U32) : U32 = twice(x) + inc(x)\n"
            .. "return { functions = { twice, offset } }",
        entries = { { entry = "twice", arity = 1 }, { entry = "offset", arity = 1 } },
        inputs = { { 0 }, { 1 }, { 4294967294 } },
    },
    {
        name = "recursion",
        source = "let sum_to(n: U32) : U32 = if n == 0 then 0 else n + sum_to(n - 1)\n"
            .. "let factorial(n: U32) : U32 = if n == 0 then 1 else n * factorial(n - 1)\n"
            .. "return { functions = { sum_to, factorial } }",
        entries = { { entry = "sum_to", arity = 1 }, { entry = "factorial", arity = 1 } },
        inputs = { { 0 }, { 1 }, { 5 }, { 10 } },
    },
    {
        name = "staticspecialization",
        source = "let scale(k, x: U32) : U32 = k * x\n"
            .. "let by3 = scale(3)\n"
            .. "let scaled(x: U32) : U32 = by3(x) + scale(5)(x)\n"
            .. "return { functions = { scaled } }",
        entry = "scaled", arity = 1,
        inputs = { { 0 }, { 1 }, { 7 }, { 1000000 } },
    },
    {
        name = "shifts",
        source = "let xorshift(a, b, c, s: U32) : U32 = do\n"
            .. "  let s1 = s ~ (s << a)\n  let s2 = s1 ~ (s1 >> b)\n  return s2 ~ (s2 << c)\nend\n"
            .. "let next32 = xorshift(13, 17, 5)\n"
            .. "let third(s: U32) : U32 = next32(next32(next32(s)))\n"
            .. "return { functions = { next32, third } }",
        entries = { { entry = "next32", arity = 1 }, { entry = "third", arity = 1 } },
        inputs = { { 0 }, { 1 }, { 42 }, { 4294967295 } },
    },
    {
        name = "guard",
        source = "let safe_div(a, b: U32) : U32 = a / b\nreturn { functions = { safe_div } }",
        entry = "safe_div", arity = 2,
        inputs = { { 100, 3 }, { 7, 1 }, { 4294967295, 65536 } },
    },
    {
        name = "records",
        source = "let P = { x: U32, y: U32 }\n"
            .. "let build(a, b: U32) : U32 = do\n"
            .. "  let p = P { x = a, y = b }\n  return p.x * 1000 + p.y\nend\n"
            .. "let bump(p: P) : U32 = do p.x += 1 return p.x end\n"
            .. "let caller(n: U32) : U32 = do\n"
            .. "  let p = P { x = n, y = 5 }\n  let raised = bump(p)\n"
            .. "  return raised * 1000 + p.x * 10 + p.y\nend\n"
            .. "let pair(a: U32) : P = P { x = a, y = a + 1 }\n"
            .. "let use(a: U32) : U32 = do let q = pair(a) return q.x * 10 + q.y end\n"
            .. "let alias(n: U32) : U32 = do\n"
            .. "  let p = P { x = n, y = 0 }\n  let q = p\n  q.y = 9\n  return p.x * 10 + p.y\nend\n"
            .. "let compound(n: U32) : U32 = do\n"
            .. "  let p = P { x = n, y = 3 }\n  p.x += 4\n  p.y *= 2\n  p.x -= 1\n"
            .. "  return p.x * 100 + p.y\nend\n"
            .. "return { types = { P }, functions = { build, caller, use, alias, compound } }",
        entries = {
            { entry = "build", arity = 2 }, { entry = "caller", arity = 1 },
            { entry = "use", arity = 1 }, { entry = "alias", arity = 1 },
            { entry = "compound", arity = 1 },
        },
        inputs = { { 0, 0 }, { 3, 4 }, { 7, 5 }, { 10, 1 }, { 4294967295, 1 }, { 2 }, { 9 }, { 5 } },
    },
    {
        name = "methods",
        source = "let Counter = {\n  value: U32,\n  inc() : U32 = do value += 1 return value end,\n"
            .. "  add(n: U32) : U32 = do value += n return value end,\n}\n"
            .. "let observe(n: U32, change: Bool) : (U32, U32) = do\n"
            .. "  let c = Counter { value = n }\n  let old = c.value\n"
            .. "  if change then c.inc() end\n  return old, c.value\nend\n"
            .. "let twice(n: U32) : U32 = do\n"
            .. "  let c = Counter { value = n }\n  c.inc()\n  c.add(5)\n  return c.value\nend\n"
            .. "return { types = { Counter }, functions = { observe, twice } }",
        entries = { { entry = "observe", arity = 2 }, { entry = "twice", arity = 1 } },
        inputs = { { 7, true }, { 7, false }, { 0, true }, { 4294967295, true }, { 1 }, { 100 } },
    },
    {
        name = "tails",
        source = "let sum_to(n, acc: U32) : U32 = if n == 0 then acc else sum_to(n - 1, acc + n)\n"
            .. "let count_down(n: U32) : U32 = if n == 0 then 7 else count_down(n - 1)\n"
            .. "let swapdown(a, b: U32) : U32 = if a == 0 then b else swapdown(b, a - 1)\n"
            .. "return { functions = { sum_to, count_down, swapdown } }",
        entries = { { entry = "sum_to", arity = 2 }, { entry = "count_down", arity = 1 },
            { entry = "swapdown", arity = 2 } },
        inputs = { { 0, 5 }, { 1, 0 }, { 10, 3 }, { 5, 0 }, { 3, 4 }, { 0, 0 }, { 2, 5 }, { 7, 1 } },
    },
    {
        name = "closures",
        source = "let apply(f: (U32): U32, x: U32) : U32 = f(x)\n"
            .. "let twice(f: (U32): U32, x: U32) : U32 = f(f(x))\n"
            .. "let make_adder(n: U32) = |x: U32| -> n + x\n"
            .. "let run(n, x: U32) : U32 = do let add = make_adder(n) return apply(add, x) end\n"
            .. "let inline(x: U32) : U32 = twice(|y: U32| -> y + 1, x)\n"
            .. "let compose(a, b, x: U32) : U32 = do\n"
            .. "  let f = make_adder(a)\n  let g = make_adder(b)\n  return apply(f, apply(g, x))\nend\n"
            .. "let C = { v: U32, mk() = |x: U32| -> v + x }\n"
            .. "let snap(n: U32) : U32 = do\n"
            .. "  let c = C { v = n }\n  let f = c.mk()\n  c.v += 5\n  return f(100)\nend\n"
            .. "return { types = { C }, functions = { run, inline, compose, snap } }",
        entries = { { entry = "run", arity = 2 }, { entry = "inline", arity = 1 },
            { entry = "compose", arity = 3 }, { entry = "snap", arity = 1 } },
        inputs = { { 5, 7 }, { 0, 0 }, { 3 }, { 7 }, { 3, 4, 10 }, { 0, 0, 0 }, { 1 }, { 4294967295 } },
    },
    {
        name = "contextual",
        source = "let twice(f: (U32): U32, x: U32): U32 = f(f(x))\n"
            .. "let adder(n: U32): (U32): U32 = |x| -> x + n\n"
            .. "let inc: (U32): U32 = |x| -> x + 1\n"
            .. "let use(n, x: U32): U32 = do\n"
            .. "  let f = adder(n)\n  return twice(f, x) + inc(x)\nend\n"
            .. "let inline(x: U32): U32 = twice(|y| -> y * 2, x)\n"
            .. "let capture(x: U32): U32 = twice(|y| -> y + x, 1)\n"
            .. "return { functions = { use, inline, capture } }",
        entries = { { entry = "use", arity = 2 }, { entry = "inline", arity = 1 },
            { entry = "capture", arity = 1 } },
        inputs = { { 3, 4 }, { 0, 0 }, { 7, 5 }, { 5 }, { 0 }, { 10 } },
    },
    {
        name = "borrowed",
        source = "let Counter = {\n  value: U32,\n"
            .. "  bump(): U32 = do value += 1 return value end,\n}\n"
            .. "let local_bumps(n: U32): U32 = do\n"
            .. "  let c = Counter { value = n }\n"
            .. "  let f = |k: U32| -> c.bump() + k\n  return f(1) + f(2)\nend\n"
            .. "let method_view(n: U32): U32 = do\n"
            .. "  let c = Counter { value = n }\n  let g = c.bump\n"
            .. "  let h = |u: U32| -> g() + u\n  return h(10)\nend\n"
            .. "let read_through(n: U32): U32 = do\n"
            .. "  let c = Counter { value = n }\n  let peek = |u: U32| -> c.value + u\n"
            .. "  c.value += 5\n  return peek(100)\nend\n"
            .. "return { types = { Counter }, functions = { local_bumps, method_view, read_through } }",
        entries = { { entry = "local_bumps", arity = 1 }, { entry = "method_view", arity = 1 },
            { entry = "read_through", arity = 1 } },
        inputs = { { 0 }, { 5 }, { 1 }, { 100 }, { 4294967295 } },
    },
    {
        name = "partial",
        source = "let add = |a, b: U32| -> a + b\n"
            .. "let add5 = add(5)\n"
            .. "let use(x: U32): U32 = add5(x) + add(2)(3)\n"
            .. "return { functions = { use } }",
        entry = "use", arity = 1,
        inputs = { { 0 }, { 10 }, { 4294967290 } },
    },
    {
        name = "alias",
        source = "let inc(x: U32) : U32 = x + 1\nreturn { functions = { a = inc, b = inc } }",
        entries = { { entry = "a", arity = 1 }, { entry = "b", arity = 1 } },
        inputs = { { 0 }, { 5 } },
    },
    {
        name = "unitandbool",
        source = "let flag(x: U32) : Bool = x != 0\n"
            .. "let both(a, b: U32) : Bool = (a < b) and (b != 0)\n"
            .. "return { functions = { flag, both } }",
        entries = { { entry = "flag", arity = 1 }, { entry = "both", arity = 2 } },
        inputs = { { 0 }, { 1 }, { 5, 0 }, { 3, 9 }, { 9, 3 } },
    },
    {
        name = "sums",
        source = [==[
let Circle = { radius: U32 }
let Rect = { width: U32, height: U32 }
let Shape = OneOf({ circle: Circle, rect: Rect })
let area(s: Shape): U32 = s {
  circle = |c: Circle| -> c.radius * c.radius,
  rect = |r: Rect| -> r.width * r.height,
}
let wrap(n: U32): Shape = if n % 3 == 0 then Shape.rect { width = n, height = 2 } else Shape.circle { radius = n + 1 }
let via_shape(n: U32): U32 = area(wrap(n))
let direct(n: U32): U32 = area(Shape.circle { radius = n })
let Opt = OneOf({ none: Unit, some: U32 })
let or_else(o: Opt, d: U32): U32 = o {
  none = |u: Unit| -> d,
  some = |v: U32| -> v,
}
let via_option(n: U32): U32 = or_else(if n == 0 then Opt.none() else Opt.some(n * 2), 7)
return { types = { Circle, Rect, Shape }, functions = { via_shape, direct, via_option } }
]==],
        entries = { { entry = "via_shape", arity = 1 }, { entry = "direct", arity = 1 },
            { entry = "via_option", arity = 1 } },
        inputs = { { 0 }, { 1 }, { 2 }, { 3 }, { 4 }, { 100 }, { 4294967295 } },
    },
    {
        -- A record-valued conditional used to leak the arms' reads into the continuation.
        name = "recordbranch",
        source = [==[
let R = { width: U32, height: U32 }
let wrap(n: U32): R = if n == 0 then R { width = n + 2, height = 3 } else R { width = n, height = 1 }
let width_of(n: U32): U32 = wrap(n).width
return { types = { R }, functions = { wrap, width_of } }
]==],
        entries = { { entry = "width_of", arity = 1 } },
        inputs = { { 0 }, { 1 }, { 9 }, { 4294967295 } },
    },
    {
        -- Two callables of one signature chosen at run time join into a tagged callable. The
        -- interpreter selects the arm statically, so it is an independent oracle for the dispatch.
        name = "tagged",
        source = [==[
let inc(x: U32): U32 = x + 1
let dec(x: U32): U32 = x - 1
let pick(c: Bool): U32 = do
  let f = if c then inc else dec
  return f(10)
end
let twice(c: Bool, x: U32): U32 = do
  let f = if c then |y: U32| -> y + x else |y: U32| -> y * 2
  return f(f(1))
end
let choose(c: Bool, x: U32): U32 = do
  let f = if c then |y: U32| -> y + x else |y: U32| -> y * x
  return f(3) + f(4)
end
let with_zero(c: Bool, x: U32): U32 = do
  let f = if c then inc else |y: U32| -> y * 0
  return f(x)
end
let pair(c: Bool, x: U32): (U32, U32) = do
  let f = if c then inc else dec
  return f(x), f(f(x))
end
let length(c: Bool, x: U32): U32 = (if c then |y: U32| -> y + x else |y: U32| -> y * x)(7)
-- A tagged callable that crosses a call boundary: the tag is only known at run time.
let mk(c: Bool) = if c then inc else |y: U32| -> y * 3
let use(c: Bool, x: U32): U32 = do
  let f = mk(c)
  return f(x)
end
return { functions = { pick, twice, choose, with_zero, pair, length, mk, use } }
]==],
        entries = { { entry = "pick", arity = 1 }, { entry = "twice", arity = 2 },
            { entry = "choose", arity = 2 }, { entry = "with_zero", arity = 2 },
            { entry = "pair", arity = 2 }, { entry = "length", arity = 2 },
            { entry = "use", arity = 2 } },
        inputs = { { true }, { false }, { true, 5 }, { false, 5 }, { true, 0 }, { false, 0 },
            { true, 4294967295 }, { false, 4294967295 }, { true, 1 } },
    },
    {
        -- A callable that borrows storage reaches outside itself, so it crosses a callable parameter
        -- as a non-retaining view holding that borrowed place; pure code crosses as a null
        -- environment view. The interpreter resolves both, so it is an independent oracle.
        name = "callables",
        source = [==[
let C = { v: U32 }
let apply(f: (U32): U32, x: U32): U32 = f(x)
let run(x: U32): U32 = do
  let c = C { v = 10 }
  let g = |y: U32| -> y + c.v
  return apply(g, x)
end
let chained(x: U32): U32 = do
  let c = C { v = 3 }
  let g = |y: U32| -> y + c.v
  return apply(g, apply(g, x))
end
let mk(): (U32): U32 = |x: U32| -> x + 1
let pure(x: U32): U32 = do
  let f = mk()
  return f(f(x))
end
return { types = { C }, functions = { run, chained, mk, pure } }
]==],
        entries = { { entry = "run", arity = 1 }, { entry = "chained", arity = 1 },
            { entry = "pure", arity = 1 } },
        inputs = { { 0 }, { 1 }, { 5 }, { 4294967295 } },
    },
    {
        -- A method borrows its receiver, so a callable parameter takes a view whose local adapter
        -- holds that borrowed place. The interpreter binds the receiver to a concrete record, so it
        -- is an independent oracle.
        name = "methodpass",
        source = [==[
let C = { v: U32, bump(): U32 = do v += 1 return v end }
let apply(f: (): U32, x: U32): U32 = f() + x
let run(x: U32): U32 = do
  let c = C { v = 10 }
  return apply(c.bump, x)
end
let twice(x: U32): U32 = do
  let c = C { v = 0 }
  return apply(c.bump, apply(c.bump, x))
end
return { types = { C }, functions = { run, twice } }
]==],
        entries = { { entry = "run", arity = 1 }, { entry = "twice", arity = 1 } },
        inputs = { { 0 }, { 1 }, { 5 }, { 4294967295 } },
    },
    {
        -- A reference names a place in an enclosing activation, so it is live: a store through it is
        -- visible to the caller, and two references to one instance observe each other. Nothing here
        -- touches module state, so each input stands alone and the interpreter is a valid oracle.
        name = "references",
        source = [==[
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
    let r = Ref(c)
    r.value += d
    let s = Ref(c)
    return s.value
  end
  return g(1) + g(2)
end
return { types = { Counter }, functions = { borrowed, aliased } }
]==],
        entries = { { entry = "borrowed", arity = 1 }, { entry = "aliased", arity = 1 } },
        inputs = { { 0 }, { 1 }, { 2 }, { 100 }, { 4294967295 } },
    },
    {
        -- Aggregate results, compared field by field against the interpreter: a record, a variant
        -- with an empty and a non-empty payload, and a tuple that contains a record.
        name = "aggregates",
        source = [==[
let Point = { x: U32, y: U32 }
let Opt = OneOf({ none: Unit, some: U32 })
let point(x: U32): Point = Point { x = x, y = x + 1 }
let wrap(x: U32): Opt = if x == 0 then Opt.none() else Opt.some(x * 2)
let pair(x: U32): (Point, U32) = do return point(x), x end
let nested(x: U32): Point = Point { x = wrap(x) { none = |u: Unit| -> 0, some = |v: U32| -> v }, y = x }
return { types = { Point, Opt }, functions = { point, wrap, pair, nested } }
]==],
        entries = { { entry = "point", arity = 1 }, { entry = "wrap", arity = 1 },
            { entry = "pair", arity = 1 }, { entry = "nested", arity = 1 } },
        inputs = { { 0 }, { 1 }, { 7 }, { 4294967295 } },
    },
    {
        -- Arrays: a literal, a static and a run-time index, a store, a nested array, and an array
        -- returned as a result, all compared against the interpreter.
        name = "arrays",
        source = [==[
let shared = [10, 20, 30]
let first(): U32 = shared[0]
let sum(): U32 = shared[0] + shared[1] + shared[2]
let local_pick(i: U32): U32 = do
  let b: Array(U32, 3) = [7, 8, 9]
  return b[i]
end
let store(i: U32, v: U32): U32 = do
  let b = [1, 2, 3]
  b[i] = v
  return b[0] + b[1] + b[2]
end
let grid_cell(r: U32, c: U32): U32 = do
  let g = [[1, 2], [3, 4]]
  return g[r][c]
end
let sum2(a: Array(U32, 2)): U32 = a[0] + a[1]
let total(x: U32): U32 = do
  let b: Array(U32, 2) = [x, x + 1]
  return sum2(b)
end
let doubled(x: U32): Array(U32, 3) = do
  let b = [x, x + 1, x + 2]
  b[1] += 10
  return b
end
return { types = {  }, functions = { first, sum, local_pick, store, grid_cell, total, doubled } }
]==],
        entries = {
            { entry = "local_pick", arity = 1, inputs = { { 0 }, { 2 } } },
            { entry = "store", arity = 2, inputs = { { 0, 5 }, { 2, 7 } } },
            { entry = "grid_cell", arity = 2, inputs = { { 0, 1 }, { 1, 0 }, { 1, 1 } } },
            { entry = "total", arity = 1, inputs = { { 3 }, { 4294967295 } } },
            { entry = "doubled", arity = 1, inputs = { { 0 }, { 7 } } },
        },
    },
    {
        -- Narrower integers: arithmetic wraps at the width the type names, widening is implicit, and
        -- a run-time narrowing conversion is checked, which is why each entry has its own inputs.
        name = "widths",
        source = [==[
let wrap8(n: U32): U32 = do
  let a: U8 = U8(n)
  let b = a + 200
  return U32(b)
end
let mix8(n: U32): U32 = do
  let a: U8 = U8(n)
  return U32(a * 3) + U32(a / 2) + U32(a % 7)
end
let wrap16(n: U32): U32 = do
  let a: U16 = U16(n)
  let b = a * 3
  return U32(b)
end
let chain(n: U32): U32 = do
  let a: U8 = U8(n)
  let b: U16 = a
  let c: U32 = b
  return c
end
let bits(n: U32): U32 = do
  let a: U8 = U8(n)
  return U32(a & 15) + U32(a | 16) + U32(a ^ 255)
end
return { types = {  }, functions = { wrap8, mix8, wrap16, chain, bits } }
]==],
        entries = {
            { entry = "wrap8", arity = 1, inputs = { { 0 }, { 100 }, { 255 } } },
            { entry = "mix8", arity = 1, inputs = { { 0 }, { 7 }, { 200 }, { 255 } } },
            { entry = "wrap16", arity = 1, inputs = { { 0 }, { 40000 }, { 65535 } } },
            { entry = "chain", arity = 1, inputs = { { 0 }, { 200 } } },
            { entry = "bits", arity = 1, inputs = { { 0 }, { 1 }, { 130 }, { 255 } } },
        },
    },
    {
        -- Signed integers compare against the interpreter on wrapping, truncating division with the
        -- dividend's sign, and an arithmetic shift.
        name = "signed",
        source = [==[
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
let bits(n: U32): U32 = do
  let a: I32 = I32(n)
  return U32(a & I32(255)) + U32(a | I32(16)) + U32(a ^ I32(255))
end
let negate(n: U32): U32 = do
  let a: I32 = I32(n)
  return U32(-a)
end
return { types = {  }, functions = { round, quotient, shift, bits, negate } }
]==],
        entries = {
            { entry = "round", arity = 1, inputs = { { 0 }, { 5 }, { 4294967295 } } },
            { entry = "quotient", arity = 1, inputs = { { 0 }, { 5 }, { 4294967294 }, { 7 } } },
            { entry = "shift", arity = 1, inputs = { { 0 }, { 1 }, { 4294967295 }, { 2147483648 } } },
            { entry = "bits", arity = 1, inputs = { { 0 }, { 130 }, { 4294967295 } } },
            { entry = "negate", arity = 1, inputs = { { 0 }, { 1 }, { 2147483648 } } },
        },
    },
    {
        -- 64-bit integers: literals that do not fit a word, widening and narrowing, products that
        -- need both words, division and remainder of a signed value, and a shift into the high word.
        name = "wide",
        source = [==[
let low(): U32 = U32(0xFFFFFFFFFFFFFFFF % 4294967296)
let high(): U32 = U32(0xFFFFFFFFFFFFFFFF / 4294967296)
let square_low(n: U32): U32 = U32(U64(n) * U64(n) % 4294967296)
let square_high(n: U32): U32 = U32(U64(n) * U64(n) / 4294967296)
let cube_low(n: U32): U32 = U32(U64(n) * U64(n) * U64(n) % 4294967296)
let shift_high(n: U32): U32 = U32((U64(1) << (n % 64)) / 4294967296)
let signed_quotient(n: U32): U32 = U32(I64(n) / I64(3))
let signed_remainder(n: U32): U32 = U32(I64(n) % I64(3))
let signed_shift(n: U32): U32 = U32((I64(4294967296) + I64(n)) >> I64(1))
let big_literal(n: U32): U32 = U32((18446744073709551615 + U64(n)) % 4294967296)
return { types = {  }, functions = { low, high, square_low, square_high, cube_low, shift_high,
    signed_quotient, signed_remainder, signed_shift, big_literal } }
]==],
        entries = {
            { entry = "low", arity = 0, inputs = { {} } },
            { entry = "high", arity = 0, inputs = { {} } },
            { entry = "square_low", arity = 1, inputs = { { 0 }, { 3 }, { 4294967295 } } },
            { entry = "square_high", arity = 1, inputs = { { 0 }, { 65536 }, { 4294967295 } } },
            { entry = "cube_low", arity = 1, inputs = { { 0 }, { 7 }, { 4294967295 } } },
            { entry = "shift_high", arity = 1, inputs = { { 0 }, { 32 }, { 40 }, { 63 } } },
            { entry = "signed_quotient", arity = 1, inputs = { { 0 }, { 7 }, { 4294967295 } } },
            { entry = "signed_remainder", arity = 1, inputs = { { 0 }, { 7 }, { 4294967295 } } },
            { entry = "signed_shift", arity = 1, inputs = { { 0 }, { 2 }, { 4294967295 } } },
            { entry = "big_literal", arity = 1, inputs = { { 0 }, { 1 }, { 4294967295 } } },
        },
    },
}

local function cLiteral(value)
    if type(value) == "number" then return "UINT32_C(" .. value .. ")" end
    if type(value) == "boolean" then return value and "true" or "false" end
    return nil
end

local function runCase(case)
    local artifact = wordlet.compile{ source = case.source, name = case.name .. ".let" }
    local unit = artifact:unit()
    local cPath, exePath = directory .. "/" .. case.name .. ".c", directory .. "/" .. case.name
    write(cPath, unit)

    local checksList = {}
    for _, target in ipairs(case.entries or { { entry = case.entry, arity = case.arity } }) do
        -- An entry may carry its own inputs when the shared ones are not valid for it, which is what
        -- an entry with a constrained argument needs.
        for _, input in ipairs(target.inputs or case.inputs) do
          if #input >= target.arity then
            local args = {}
            for index = 1, target.arity do args[index] = input[index] end
            local expected = wordlet.interpret{ source = case.source, name = case.name .. ".let",
                entry = target.entry, args = args }
            local literalArgs = {}
            for index, value in ipairs(args) do literalArgs[index] = cLiteral(value) end
            -- Export names are escaped: underscore becomes _5F, so the C symbol is not the source name.
            local call = C.functionName(target.entry) .. "(" .. table.concat(literalArgs, ", ") .. ")"
            local before = #checksList
            local scalar = #expected == 1 and cLiteral(expected[1]) ~= nil
            if scalar then
                checksList[#checksList + 1] = "    assert((" .. call .. ") == " .. cLiteral(expected[1]) .. ");"
            else
                -- An aggregate result is bound once and then compared field by field, so the call
                -- runs once even when it has effects.
                local ty = #expected == 1 and resultType(unit, C.functionName(target.entry))
                    or select(1, unit:match("(wordlettuple_%d+) {"))
                check(ty ~= nil, "cannot find the C result type of " .. target.entry)
                checksList[#checksList + 1] = "    { " .. ty .. " r = " .. call .. ";"
                for index, value in ipairs(expected) do
                    local path = #expected == 1 and "r" or ("r.f_" .. index)
                    assertValue(checksList, path, value)
                end
                checksList[#checksList + 1] = "    }"
            end
            check(#checksList > before, "each input must produce an assertion")
          end
        end
    end

    local main = { "#include <assert.h>", "#include <stdint.h>", "#include <stdbool.h>", "",
        unit, "", "int main(void) {" }
    for _, line in ipairs(checksList) do main[#main + 1] = line end
    main[#main + 1] = "    return 0;"
    main[#main + 1] = "}"
    write(cPath, table.concat(main, "\n"))

    local flags = "-std=c11 -Wall -Wextra -Werror -O2"
    local compile = ("timeout --kill-after=2s %s %s %s -o '%s' '%s'"):format(timeout, CC, flags, exePath, cPath)
    local status = shell(compile .. " 2> " .. directory .. "/err.txt")
    check(status == 0, "C compilation failed for " .. case.name .. ":\n" .. read(directory .. "/err.txt"))
    local run = shell("timeout --kill-after=2s 10s '" .. exePath .. "'")
    check(run == 0, "generated C failed its assertions for " .. case.name .. " (status " .. tostring(run) .. ")")
end

for _, case in ipairs(CASES) do runCase(case) end

-- A self-tail call must not consume C stack. Without the loop rewrite this overflows; with it,
-- the call is a back edge and the depth is constant. This runs only in C because the reference
-- interpreter would recurse in Lua.
do
    local source = "let count_down(n: U32) : U32 = if n == 0 then 7 else count_down(n - 1)\n"
        .. "let sum_to(n, acc: U32) : U32 = if n == 0 then acc else sum_to(n - 1, acc + n)\n"
        .. "return { functions = { count_down, sum_to } }"
    local generated = wordlet.compile{ source = source, name = "deep.let" }:unit()
    local path = directory .. "/deep.c"
    write(path, generated .. "\n#include <assert.h>\n"
        .. "int main(void) {\n"
        .. "    assert(wordlet_count_5Fdown(UINT32_C(5000000)) == UINT32_C(7));\n"
        .. "    assert(wordlet_sum_5Fto(UINT32_C(65535), UINT32_C(0)) == (uint32_t)((uint64_t)65535*65536/2));\n"
        .. "    return 0;\n}\n")
    local exe = directory .. "/deep"
    check(shell("timeout --kill-after=2s 30s " .. CC .. " -std=c11 -Wall -Wextra -Werror -O2 -o '"
        .. exe .. "' '" .. path .. "' 2> " .. directory .. "/derr.txt") == 0,
        "deep-recursion C failed to compile:\n" .. read(directory .. "/derr.txt"))
    check(shell("timeout --kill-after=2s 30s '" .. exe .. "'") == 0,
        "a self-tail call must run at constant C stack depth")
end

-- Opaque runtime callables: a C caller supplies the invocation pointer, so this is a C-only test.
-- The reference interpreter has no callable values to supply.
do
    local source = "let apply(f: (U32): U32, x: U32): U32 = f(x)\n"
        .. "let twice_apply(f: (U32): U32, x: U32): U32 = apply(f, apply(f, x))\n"
        .. "let compose(f: (U32): U32, g: (U32): U32, x: U32): U32 = f(g(x))\n"
        .. "let invoke(f: (U32): (), x: U32): U32 = do f(x) return x end\n"
        .. "let internal(x: U32): U32 = apply(|y: U32| -> y + 1, x)\n"
        .. "return { functions = { apply, twice_apply, compose, invoke, internal } }"
    local generated = wordlet.compile{ source = source, name = "callbacks.let" }:unit()
    local path = directory .. "/callbacks.c"
    write(path, generated .. [[

#include <assert.h>
static uint32_t plus1(const void *e, uint32_t x) { (void)e; return x + 1u; }
static uint32_t times3(const void *e, uint32_t x) { (void)e; return x * 3u; }
static uint32_t seen = 0;
static void note(const void *e, uint32_t x) { (void)e; seen = x; }
int main(void) {
    wordletview_1 a = { .invoke = plus1, .environment = NULL };
    wordletview_1 b = { .invoke = times3, .environment = NULL };
    wordletview_2 n = { .invoke = note, .environment = NULL };
    assert(wordlet_apply(a, UINT32_C(5)) == UINT32_C(6));
    assert(wordlet_twice_5Fapply(a, UINT32_C(5)) == UINT32_C(7));
    assert(wordlet_compose(a, b, UINT32_C(5)) == UINT32_C(16));
    assert(wordlet_invoke(n, UINT32_C(42)) == UINT32_C(42) && seen == UINT32_C(42));
    assert(wordlet_internal(UINT32_C(4)) == UINT32_C(5));
    return 0;
}
]])
    local exe = directory .. "/callbacks"
    check(shell("timeout --kill-after=2s 30s " .. CC .. " -std=c11 -Wall -Wextra -Werror -O2 -o '"
        .. exe .. "' '" .. path .. "' 2> " .. directory .. "/cberr.txt") == 0,
        "callback C failed to compile:\n" .. read(directory .. "/cberr.txt"))
    check(shell("timeout --kill-after=2s 10s '" .. exe .. "'") == 0,
        "the invocation-pointer ABI failed at run time")
end

-- Module-level mutable state: the host calls the exported initialiser, then the state persists.
do
    local source = "let Counter = { value: U32, bump(): U32 = do value += 1 return value end }\n"
        .. "let shared = Counter { value = 100 }\n"
        .. "let bump_twice(x: U32): U32 = do shared.bump() shared.bump() return shared.value + x end\n"
        .. "let bump_field(a: U32): U32 = do shared.value += a return shared.value end\n"
        .. "return { types = { Counter }, functions = { bump_twice, bump_field } }"
    local generated = wordlet.compile{ source = source, name = "module.let" }:unit()
    local path = directory .. "/module.c"
    write(path, generated .. [[

#include <assert.h>
int main(void) {
    /* Not called implicitly: the host owns initialisation order. */
    assert(wordlet_bump_5Ftwice(UINT32_C(1)) == UINT32_C(3));   /* before init: zeroed storage */
    wordlet_init();
    assert(wordlet_bump_5Ftwice(UINT32_C(1)) == UINT32_C(103));
    assert(wordlet_bump_5Ftwice(UINT32_C(1)) == UINT32_C(105));
    return 0;
}
]])
    local exe = directory .. "/module"
    check(shell("timeout --kill-after=2s 30s " .. CC .. " -std=c11 -Wall -Wextra -Werror -O2 -o '"
        .. exe .. "' '" .. path .. "' 2> " .. directory .. "/moderr.txt") == 0,
        "module-state C failed to compile:\n" .. read(directory .. "/moderr.txt"))
    check(shell("timeout --kill-after=2s 10s '" .. exe .. "'") == 0,
        "module-level storage did not persist across calls")
end

-- A callable stored in a signature-typed field: the field holds a view built from a local adapter.
do
    local source = "let Holder = { f: (U32): U32 }\n"
        .. "let use(n: U32): U32 = do\n  let h = Holder { f = |x: U32| -> x + n }\n  return h.f(1)\nend\n"
        .. "let chase(n: U32): U32 = do\n  let h = Holder { f = |x: U32| -> x * 2 }\n"
        .. "  return h.f(h.f(n))\nend\n"
        .. "return { types = { Holder }, functions = { use, chase } }"
    local generated = wordlet.compile{ source = source, name = "field.let" }:unit()
    local path = directory .. "/field.c"
    write(path, generated .. [[

#include <assert.h>
int main(void) {
    assert(wordlet_use(UINT32_C(5)) == UINT32_C(6));
    assert(wordlet_chase(UINT32_C(3)) == UINT32_C(12));
    return 0;
}
]])
    local exe = directory .. "/field"
    check(shell("timeout --kill-after=2s 30s " .. CC .. " -std=c11 -Wall -Wextra -Werror -O2 -o '"
        .. exe .. "' '" .. path .. "' 2> " .. directory .. "/flderr.txt") == 0,
        "callable-field C failed to compile:\n" .. read(directory .. "/flderr.txt"))
    check(shell("timeout --kill-after=2s 10s '" .. exe .. "'") == 0,
        "a callable field did not run correctly")
end

-- Sum types at the ABI boundary: a host builds a variant, passes it by value, and reads the tag
-- and payload of one that comes back. This is C-only because the interpreter has no host values.
do
    local source = [==[
let Circle = { radius: U32 }
let Rect = { width: U32, height: U32 }
let Shape = OneOf({ circle: Circle, rect: Rect })
let area(s: Shape): U32 = s {
  circle = |c: Circle| -> c.radius * c.radius,
  rect = |r: Rect| -> r.width * r.height,
}
let rect_of(w: U32): Shape = Shape.rect { width = w, height = 2 }
return { types = { Circle, Rect, Shape }, functions = { area, rect_of } }
]==]
    local generated = wordlet.compile{ source = source, name = "shape.let" }:unit()
    local path = directory .. "/shape.c"
    write(path, generated .. [[

#include <assert.h>
int main(void) {
    wordletsum_1 built;
    built.wordlet_tag = 0;
    built.payload.f_circle.f_radius = UINT32_C(9);
    assert(wordlet_area(built) == UINT32_C(81));

    wordletsum_1 back = wordlet_rect_5Fof(UINT32_C(5));
    assert(back.wordlet_tag == 1);
    assert(back.payload.f_rect.f_width == UINT32_C(5));
    assert(back.payload.f_rect.f_height == UINT32_C(2));
    return 0;
}
]])
    local exe = directory .. "/shape"
    check(shell("timeout --kill-after=2s 30s " .. CC .. " -std=c11 -Wall -Wextra -Werror -O2 -o '"
        .. exe .. "' '" .. path .. "' 2> " .. directory .. "/sherr.txt") == 0,
        "sum ABI C failed to compile:\n" .. read(directory .. "/sherr.txt"))
    check(shell("timeout --kill-after=2s 10s '" .. exe .. "'") == 0,
        "a host-built variant or a returned variant crossed the ABI incorrectly")
end

-- A Unit parameter is erased rather than represented: a Unit alternative's handler takes no C
-- argument, and the generated code must still compile under -Werror.
do
    local source = [==[
let Opt = OneOf({ none: Unit, some: U32 })
let or_else(o: Opt, d: U32): U32 = o {
  none = |u: Unit| -> d,
  some = |v: U32| -> v,
}
let unwrap_or(n: U32, d: U32): U32 = or_else(if n == 0 then Opt.none() else Opt.some(n), d)
return { types = { Opt }, functions = { unwrap_or, or_else } }
]==]
    local generated = wordlet.compile{ source = source, name = "opt.let" }:unit()
    local path = directory .. "/opt.c"
    write(path, generated .. [[

#include <assert.h>
int main(void) {
    assert(wordlet_unwrap_5For(UINT32_C(0), UINT32_C(7)) == UINT32_C(7));
    assert(wordlet_unwrap_5For(UINT32_C(4), UINT32_C(7)) == UINT32_C(4));
    wordletsum_1 none = { .wordlet_tag = 0 };
    assert(wordlet_or_5Felse(none, UINT32_C(3)) == UINT32_C(3));
    return 0;
}
]])
    local exe = directory .. "/opt"
    check(shell("timeout --kill-after=2s 30s " .. CC .. " -std=c11 -Wall -Wextra -Werror -O2 -o '"
        .. exe .. "' '" .. path .. "' 2> " .. directory .. "/opterr.txt") == 0,
        "Unit-parameter C failed to compile:\n" .. read(directory .. "/opterr.txt"))
    check(shell("timeout --kill-after=2s 10s '" .. exe .. "'") == 0,
        "a Unit alternative did not erase cleanly at the ABI")
end

-- A tagged callable as a host-visible value: the tag is a plain word and the payload union holds
-- that arm environment, so a host can hold one and pass it back.
do
    local source = [==[
let inc(x: U32): U32 = x + 1
let dec(x: U32): U32 = x - 1
let mk(c: Bool) = if c then inc else dec
let use(c: Bool, x: U32): U32 = do
  let f = mk(c)
  return f(x)
end
return { functions = { mk, use } }
]==]
    local generated = wordlet.compile{ source = source, name = "tag.let" }:unit()
    local path = directory .. "/tag.c"
    write(path, generated .. [[

#include <assert.h>
int main(void) {
    wordlettag_1 up = wordlet_mk(true);
    wordlettag_1 down = wordlet_mk(false);
    assert(up.wordlet_tag != down.wordlet_tag);
    assert(up.wordlet_tag < 2 && down.wordlet_tag < 2);
    assert(wordlet_use(true, UINT32_C(10)) == UINT32_C(11));
    assert(wordlet_use(false, UINT32_C(10)) == UINT32_C(9));
    return 0;
}
]])
    local exe = directory .. "/tag"
    check(shell("timeout --kill-after=2s 30s " .. CC .. " -std=c11 -Wall -Wextra -Werror -O2 -o '"
        .. exe .. "' '" .. path .. "' 2> " .. directory .. "/tagerr.txt") == 0,
        "tagged-callable C failed to compile:\n" .. read(directory .. "/tagerr.txt"))
    check(shell("timeout --kill-after=2s 10s '" .. exe .. "'") == 0,
        "a tagged callable did not cross the ABI correctly")
end

-- Pure code as a host-visible value: nothing is retained, so a host may hold the invocation pointer
-- with a null environment, and a borrowing callable still has to point at its borrowed place.
do
    local source = [==[
let C = { v: U32 }
let mk(): (U32): U32 = |x: U32| -> x + 1
let pure(x: U32): U32 = do
  let f = mk()
  return f(f(x))
end
let apply(f: (U32): U32, x: U32): U32 = f(x)
let run(x: U32): U32 = do
  let c = C { v = 10 }
  let g = |y: U32| -> y + c.v
  return apply(g, x)
end
return { types = { C }, functions = { mk, pure, run } }
]==]
    local generated = wordlet.compile{ source = source, name = "pure.let" }:unit()
    local path = directory .. "/pure.c"
    write(path, generated .. [[

#include <assert.h>
int main(void) {
    wordletview_1 f = wordlet_mk();
    assert(f.environment == NULL);
    assert(f.invoke(f.environment, UINT32_C(4)) == UINT32_C(5));
    assert(wordlet_pure(UINT32_C(4)) == UINT32_C(6));
    assert(wordlet_run(UINT32_C(5)) == UINT32_C(15));
    return 0;
}
]])
    local exe = directory .. "/pure"
    check(shell("timeout --kill-after=2s 30s " .. CC .. " -std=c11 -Wall -Wextra -Werror -O2 -o '"
        .. exe .. "' '" .. path .. "' 2> " .. directory .. "/pureerr.txt") == 0,
        "pure-code C failed to compile:\n" .. read(directory .. "/pureerr.txt"))
    check(shell("timeout --kill-after=2s 10s '" .. exe .. "'") == 0,
        "pure code did not cross the ABI as a null-environment view")
end

-- Module-storage references and a recursive structure over them. The host calls the exported
-- initialiser first, and the state then persists, so this is C-only.
do
    local source = [==[
let Counter = { value: U32 }
let shared = Counter { value = 5 }
let read_shared(x: U32): U32 = Ref(shared).value + x
let via(r: Ref(Counter)): U32 = r.value
let via_set(r: Ref(Counter), v: U32): U32 = do
  r.value = v
  return r.value
end
let bump_shared(x: U32): U32 = do
  let r = Ref(shared)
  r.value += 1
  return r.value + x
end
let Node = { value: U32, next: Link }
let Link = OneOf({ none: Unit, some: Ref(Node) })
let n1 = Node { value = 10, next = Link.none() }
let n0 = Node { value = 1, next = Link.some(Ref(n1)) }
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
return { types = { Counter, Node, Link }, functions = { read_shared, via, via_set, bump_shared, following, bump_following } }
]==]
    local generated = wordlet.compile{ source = source, name = "refmod.let" }:unit()
    local path = directory .. "/refmod.c"
    write(path, generated .. [[

#include <assert.h>
int main(void) {
    wordlet_init();
    assert(wordlet_read_5Fshared(UINT32_C(1)) == UINT32_C(6));
    assert(wordlet_bump_5Fshared(UINT32_C(1)) == UINT32_C(7));
    /* the bump stores the incremented value and returns it plus its argument */
    assert(wordlet_read_5Fshared(UINT32_C(0)) == UINT32_C(6));
    /* a host may pass a pointer for a reference parameter */
    assert(wordlet_via(&wordletmodule_1) == UINT32_C(6));
    assert(wordlet_via_5Fset(&wordletmodule_1, UINT32_C(20)) == UINT32_C(20));
    assert(wordlet_read_5Fshared(UINT32_C(0)) == UINT32_C(20));
    /* a point in a stored structure, reached by a reference and mutated through it */
    assert(wordlet_following() == UINT32_C(10));
    assert(wordlet_bump_5Ffollowing() == UINT32_C(15));
    assert(wordlet_following() == UINT32_C(15));
    return 0;
}
]])
    local exe = directory .. "/refmod"
    check(shell("timeout --kill-after=2s 30s " .. CC .. " -std=c11 -Wall -Wextra -Werror -O2 -o '"
        .. exe .. "' '" .. path .. "' 2> " .. directory .. "/refmoderr.txt") == 0,
        "reference and recursion C failed to compile:\n" .. read(directory .. "/refmoderr.txt"))
    check(shell("timeout --kill-after=2s 10s '" .. exe .. "'") == 0,
        "a reference over module storage or a recursive structure did not run correctly")
end

-- A pool of nodes in module storage, reached by a reference to an element, and the bounds guard a
-- run-time index needs. Both are runtime-only, so this is C-only.
do
    local source = [==[
let Counter = { value: U32 }
let pool = [Counter { value = 1 }, Counter { value = 2 }, Counter { value = 3 }]
let bump(i: U32, d: U32): U32 = do
  let r = Ref(pool[i])
  r.value += d
  return r.value
end
let read(i: U32): U32 = Ref(pool[i]).value
let pick(i: U32): U32 = do
  let b = [10, 20, 30]
  return b[i]
end
return { types = { Counter }, functions = { bump, read, pick } }
]==]
    local generated = wordlet.compile{ source = source, name = "pool.let" }:unit()
    check(generated:find("wordletarray_1", 1, true) ~= nil, "an array of records gets an array layout")
    local path = directory .. "/pool.c"
    write(path, generated .. [[

#include <assert.h>
int main(void) {
    wordlet_init();
    assert(wordlet_read(UINT32_C(0)) == UINT32_C(1));
    assert(wordlet_bump(UINT32_C(1), UINT32_C(5)) == UINT32_C(7));
    assert(wordlet_read(UINT32_C(1)) == UINT32_C(7));
    assert(wordlet_read(UINT32_C(0)) == UINT32_C(1));
    assert(wordlet_bump(UINT32_C(0), UINT32_C(1)) == UINT32_C(2));
    assert(wordlet_read(UINT32_C(0)) == UINT32_C(2));
    assert(wordlet_pick(UINT32_C(2)) == UINT32_C(30));
    return 0;
}
]])
    local exe = directory .. "/pool"
    check(shell("timeout --kill-after=2s 30s " .. CC .. " -std=c11 -Wall -Wextra -Werror -O2 -o '"
        .. exe .. "' '" .. path .. "' 2> " .. directory .. "/poolerr.txt") == 0,
        "array pool C failed to compile:\n" .. read(directory .. "/poolerr.txt"))
    check(shell("timeout --kill-after=2s 10s '" .. exe .. "'") == 0,
        "a reference to an array element or a pool of nodes did not run correctly")

    -- The guard a run-time index needs aborts rather than reading outside the array.
    local trap = directory .. "/pooltrap.c"
    write(trap, generated .. [[

#include <assert.h>
int main(void) {
    (void)wordlet_pick(UINT32_C(9));
    return 0;
}
]])
    local trapExe = directory .. "/pooltrap"
    check(shell("timeout --kill-after=2s 30s " .. CC .. " -std=c11 -Wall -Wextra -Werror -O2 -o '"
        .. trapExe .. "' '" .. trap .. "' 2> " .. directory .. "/trapErr.txt") == 0,
        "bounds-guard C failed to compile:\n" .. read(directory .. "/trapErr.txt"))
    check(shell("timeout --kill-after=2s 10s '" .. trapExe .. "' 2> " .. directory
        .. "/trapRun.txt") ~= 0, "an out-of-range run-time index must abort")
end

-- A run-time narrowing conversion that does not fit aborts, like a run-time zero divisor.
do
    local source = [==[
let narrow(n: U32): U8 = U8(n)
let read(n: U32): U32 = U32(narrow(n))
return { functions = { narrow, read } }
]==]
    local generated = wordlet.compile{ source = source, name = "narrow.let" }:unit()
    local path = directory .. "/narrow.c"
    write(path, generated .. [[

#include <assert.h>
int main(void) {
    assert(wordlet_read(UINT32_C(255)) == UINT32_C(255));
    (void)wordlet_read(UINT32_C(256));
    return 0;
}
]])
    local exe = directory .. "/narrow"
    check(shell("timeout --kill-after=2s 30s " .. CC .. " -std=c11 -Wall -Wextra -Werror -O2 -o '"
        .. exe .. "' '" .. path .. "' 2> " .. directory .. "/narrowErr.txt") == 0,
        "conversion C failed to compile:\n" .. read(directory .. "/narrowErr.txt"))
    check(shell("timeout --kill-after=2s 10s '" .. exe .. "' 2> " .. directory
        .. "/narrowRun.txt") ~= 0, "a run-time conversion that does not fit must abort")
end

-- Single-file distribution: bundle the compiler, then compile a program through the bundle's CLI.
-- This checks the shipped artifact, not just the checkout modules.
local root = (source:match("^(.*[/\\])") or "./") .. "../"
local bundlePath = directory .. "/wordlet.lua"
check(shell("timeout --kill-after=2s 40s luajit " .. root .. "tools/bundle.lua "
    .. root .. "bundle-manifest.lua '" .. bundlePath .. "' > /dev/null") == 0,
    "bundling the compiler failed")
local generatedPath = directory .. "/bundled.c"
check(shell("timeout --kill-after=2s 20s luajit '" .. bundlePath .. "' -o '" .. generatedPath
    .. "' " .. root .. "examples/arithmetic.let") == 0, "the bundled CLI failed to emit C")
local generated = read(generatedPath)
check(generated:find("wordlet_transform", 1, true) ~= nil
    and generated:find("wordlet_consume", 1, true) ~= nil, "bundle emitted the expected exports")
write(directory .. "/bundled_main.c", generated .. "\n#include <assert.h>\n"
    .. "int main(void) { assert(wordlet_transform(UINT32_C(4)) == UINT32_C(19)); return 0; }\n")
local exe = directory .. "/bundled"
check(shell("timeout --kill-after=2s 20s " .. CC .. " -std=c11 -Wall -Wextra -Werror -O2 -o '"
    .. exe .. "' '" .. directory .. "/bundled_main.c' 2> " .. directory .. "/berr.txt") == 0,
    "bundled C failed to compile:\n" .. read(directory .. "/berr.txt"))
check(shell("timeout --kill-after=2s 10s '" .. exe .. "'") == 0, "bundled C failed its assertions")

os.execute("rm -rf -- '" .. directory .. "'")
print(("PASS: interpreter/C differential and single-file distribution (%d checks, %d programs)")
    :format(checks, #CASES))
