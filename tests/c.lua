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
    elseif kind == "string" then
        -- A string result is a slice, so its bytes are compared through the struct's own fields.
        local items = {}
        for index = 1, #value do items[#items + 1] = tostring(value:byte(index)) end
        if #items == 0 then items[1] = "0" end
        checks[#checks + 1] = "    { static const uint8_t expected[] = { " .. table.concat(items, ", ") .. " };"
        checks[#checks + 1] = "      assert((" .. path .. ").f_length == UINT32_C(" .. #value .. "));"
        checks[#checks + 1] = "      assert((" .. path .. ").f_length == UINT32_C(0) || memcmp((" .. path
            .. ").f_data, expected, " .. #value .. ") == 0); }"
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
    require("tests.interface-cases"),
    {
        name = "affine",
        source = "let affine(a, b, x: u32) : u32 = a * x + b\nreturn { functions = { affine } }",
        entry = "affine", arity = 3,
        inputs = { { 3, 7, 4 }, { 1, 0, 0 }, { 4294967295, 1, 1 }, { 65536, 65536, 65537 } },
    },
    {
        name = "branch",
        source = "let pick(x: u32) : u32 = if x == 0 then 7 else x * 2\nreturn { functions = { pick } }",
        entry = "pick", arity = 1,
        inputs = { { 0 }, { 1 }, { 2147483648 }, { 4294967295 } },
    },
    {
        name = "comparison",
        source = "let classify(x: u32) : u32 = if x < 10 then 1 else if x == 10 then 2 else 3\n"
            .. "return { functions = { classify } }",
        entry = "classify", arity = 1,
        inputs = { { 0 }, { 9 }, { 10 }, { 11 }, { 4294967295 } },
    },
    {
        name = "results",
        source = "let divmod(a, b: u32) : (u32, u32) = do return a / b, a % b end\n"
            .. "let recompose(a, b: u32) : u32 = do let q, r = divmod(a, b) return q * b + r end\n"
            .. "return { functions = { divmod, recompose } }",
        entries = { { entry = "divmod", arity = 2 }, { entry = "recompose", arity = 2 } },
        inputs = { { 17, 5 }, { 1, 1 }, { 4294967295, 3 }, { 100, 7 } },
    },
    {
        name = "calls",
        source = "let inc(x: u32) : u32 = x + 1\n"
            .. "let twice(x: u32) : u32 = inc(inc(x))\n"
            .. "let offset(x: u32) : u32 = twice(x) + inc(x)\n"
            .. "return { functions = { twice, offset } }",
        entries = { { entry = "twice", arity = 1 }, { entry = "offset", arity = 1 } },
        inputs = { { 0 }, { 1 }, { 4294967294 } },
    },
    {
        name = "recursion",
        source = "let sum_to(n: u32) : u32 = if n == 0 then 0 else n + sum_to(n - 1)\n"
            .. "let factorial(n: u32) : u32 = if n == 0 then 1 else n * factorial(n - 1)\n"
            .. "return { functions = { sum_to, factorial } }",
        entries = { { entry = "sum_to", arity = 1 }, { entry = "factorial", arity = 1 } },
        inputs = { { 0 }, { 1 }, { 5 }, { 10 } },
    },
    {
        name = "staticspecialization",
        source = "let scale(k, x: u32) : u32 = k * x\n"
            .. "let by3 = scale(3)\n"
            .. "let scaled(x: u32) : u32 = by3(x) + scale(5)(x)\n"
            .. "return { functions = { scaled } }",
        entry = "scaled", arity = 1,
        inputs = { { 0 }, { 1 }, { 7 }, { 1000000 } },
    },
    {
        name = "shifts",
        source = "let xorshift(a, b, c, s: u32) : u32 = do\n"
            .. "  let s1 = s ~ (s << a)\n  let s2 = s1 ~ (s1 >> b)\n  return s2 ~ (s2 << c)\nend\n"
            .. "let next32 = xorshift(13, 17, 5)\n"
            .. "let third(s: u32) : u32 = next32(next32(next32(s)))\n"
            .. "return { functions = { next32, third } }",
        entries = { { entry = "next32", arity = 1 }, { entry = "third", arity = 1 } },
        inputs = { { 0 }, { 1 }, { 42 }, { 4294967295 } },
    },
    {
        name = "guard",
        source = "let safe_div(a, b: u32) : u32 = a / b\nreturn { functions = { safe_div } }",
        entry = "safe_div", arity = 2,
        inputs = { { 100, 3 }, { 7, 1 }, { 4294967295, 65536 } },
    },
    {
        name = "records",
        source = "let P = { x: u32, y: u32 }\n"
            .. "let build(a, b: u32) : u32 = do\n"
            .. "  let p = P { x = a, y = b }\n  return p.x * 1000 + p.y\nend\n"
            .. "let bump(p: P) : u32 = do p.x += 1 return p.x end\n"
            .. "let caller(n: u32) : u32 = do\n"
            .. "  let p = P { x = n, y = 5 }\n  let raised = bump(p)\n"
            .. "  return raised * 1000 + p.x * 10 + p.y\nend\n"
            .. "let pair(a: u32) : P = P { x = a, y = a + 1 }\n"
            .. "let use(a: u32) : u32 = do let q = pair(a) return q.x * 10 + q.y end\n"
            .. "let alias(n: u32) : u32 = do\n"
            .. "  let p = P { x = n, y = 0 }\n  let q = p\n  q.y = 9\n  return p.x * 10 + p.y\nend\n"
            .. "let compound(n: u32) : u32 = do\n"
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
        source = "let Counter = {\n  value: u32,\n  inc() : u32 = do value += 1 return value end,\n"
            .. "  add(n: u32) : u32 = do value += n return value end,\n}\n"
            .. "let observe(n: u32, change: bool) : (u32, u32) = do\n"
            .. "  let c = Counter { value = n }\n  let old = c.value\n"
            .. "  if change then c.inc() end\n  return old, c.value\nend\n"
            .. "let twice(n: u32) : u32 = do\n"
            .. "  let c = Counter { value = n }\n  c.inc()\n  c.add(5)\n  return c.value\nend\n"
            .. "return { types = { Counter }, functions = { observe, twice } }",
        entries = { { entry = "observe", arity = 2 }, { entry = "twice", arity = 1 } },
        inputs = { { 7, true }, { 7, false }, { 0, true }, { 4294967295, true }, { 1 }, { 100 } },
    },
    {
        name = "tails",
        source = "let sum_to(n, acc: u32) : u32 = if n == 0 then acc else sum_to(n - 1, acc + n)\n"
            .. "let count_down(n: u32) : u32 = if n == 0 then 7 else count_down(n - 1)\n"
            .. "let swapdown(a, b: u32) : u32 = if a == 0 then b else swapdown(b, a - 1)\n"
            .. "return { functions = { sum_to, count_down, swapdown } }",
        entries = { { entry = "sum_to", arity = 2 }, { entry = "count_down", arity = 1 },
            { entry = "swapdown", arity = 2 } },
        inputs = { { 0, 5 }, { 1, 0 }, { 10, 3 }, { 5, 0 }, { 3, 4 }, { 0, 0 }, { 2, 5 }, { 7, 1 } },
    },
    {
        -- A keyed requirement annotated with a signature types the lambda supplied for it, so the
        -- lambda's parameter carries no annotation of its own (structure.md §5.4).
        name = "keyedsig",
        source = "let apply2 { f: (u32): u32, x: u32 } : u32 = f(x)\n"
            .. "let g() : u32 = apply2 { f = |a| -> a + 1, x = 5 }\n"
            .. "return { functions = { g } }",
        entry = "g", arity = 0,
        inputs = { {} },
    },
    {
        name = "closures",
        source = "let apply(f: (u32): u32, x: u32) : u32 = f(x)\n"
            .. "let twice(f: (u32): u32, x: u32) : u32 = f(f(x))\n"
            .. "let make_adder(n: u32) = |x: u32| -> n + x\n"
            .. "let run(n, x: u32) : u32 = do let add = make_adder(n) return apply(add, x) end\n"
            .. "let inline(x: u32) : u32 = twice(|y: u32| -> y + 1, x)\n"
            .. "let compose(a, b, x: u32) : u32 = do\n"
            .. "  let f = make_adder(a)\n  let g = make_adder(b)\n  return apply(f, apply(g, x))\nend\n"
            .. "let C = { v: u32, mk() = |x: u32| -> v + x }\n"
            .. "let snap(n: u32) : u32 = do\n"
            .. "  let c = C { v = n }\n  let f = c.mk()\n  c.v += 5\n  return f(100)\nend\n"
            .. "return { types = { C }, functions = { run, inline, compose, snap } }",
        entries = { { entry = "run", arity = 2 }, { entry = "inline", arity = 1 },
            { entry = "compose", arity = 3 }, { entry = "snap", arity = 1 } },
        inputs = { { 5, 7 }, { 0, 0 }, { 3 }, { 7 }, { 3, 4, 10 }, { 0, 0, 0 }, { 1 }, { 4294967295 } },
    },
    {
        name = "contextual",
        source = "let twice(f: (u32): u32, x: u32): u32 = f(f(x))\n"
            .. "let adder(n: u32): (u32): u32 = |x| -> x + n\n"
            .. "let inc: (u32): u32 = |x| -> x + 1\n"
            .. "let use(n, x: u32): u32 = do\n"
            .. "  let f = adder(n)\n  return twice(f, x) + inc(x)\nend\n"
            .. "let inline(x: u32): u32 = twice(|y| -> y * 2, x)\n"
            .. "let capture(x: u32): u32 = twice(|y| -> y + x, 1)\n"
            .. "return { functions = { use, inline, capture } }",
        entries = { { entry = "use", arity = 2 }, { entry = "inline", arity = 1 },
            { entry = "capture", arity = 1 } },
        inputs = { { 3, 4 }, { 0, 0 }, { 7, 5 }, { 5 }, { 0 }, { 10 } },
    },
    {
        name = "borrowed",
        source = "let Counter = {\n  value: u32,\n"
            .. "  bump(): u32 = do value += 1 return value end,\n}\n"
            .. "let local_bumps(n: u32): u32 = do\n"
            .. "  let c = Counter { value = n }\n"
            .. "  let f = |k: u32| -> c.bump() + k\n  return f(1) + f(2)\nend\n"
            .. "let method_view(n: u32): u32 = do\n"
            .. "  let c = Counter { value = n }\n  let g = c.bump\n"
            .. "  let h = |u: u32| -> g() + u\n  return h(10)\nend\n"
            .. "let read_through(n: u32): u32 = do\n"
            .. "  let c = Counter { value = n }\n  let peek = |u: u32| -> c.value + u\n"
            .. "  c.value += 5\n  return peek(100)\nend\n"
            .. "return { types = { Counter }, functions = { local_bumps, method_view, read_through } }",
        entries = { { entry = "local_bumps", arity = 1 }, { entry = "method_view", arity = 1 },
            { entry = "read_through", arity = 1 } },
        inputs = { { 0 }, { 5 }, { 1 }, { 100 }, { 4294967295 } },
    },
    {
        name = "partial",
        source = "let add = |a, b: u32| -> a + b\n"
            .. "let add5 = add(5)\n"
            .. "let use(x: u32): u32 = add5(x) + add(2)(3)\n"
            .. "return { functions = { use } }",
        entry = "use", arity = 1,
        inputs = { { 0 }, { 10 }, { 4294967290 } },
    },
    {
        name = "alias",
        source = "let inc(x: u32) : u32 = x + 1\nreturn { functions = { a = inc, b = inc } }",
        entries = { { entry = "a", arity = 1 }, { entry = "b", arity = 1 } },
        inputs = { { 0 }, { 5 } },
    },
    {
        name = "unitandbool",
        source = "let flag(x: u32) : bool = x != 0\n"
            .. "let both(a, b: u32) : bool = (a < b) and (b != 0)\n"
            .. "return { functions = { flag, both } }",
        entries = { { entry = "flag", arity = 1 }, { entry = "both", arity = 2 } },
        inputs = { { 0 }, { 1 }, { 5, 0 }, { 3, 9 }, { 9, 3 } },
    },
    {
        name = "sums",
        source = [==[
let Circle = { radius: u32 }
let Rect = { width: u32, height: u32 }
let Shape = oneof { circle: Circle, rect: Rect }
let area(s: Shape): u32 = s {
  circle = |c: Circle| -> c.radius * c.radius,
  rect = |r: Rect| -> r.width * r.height,
}
let wrap(n: u32): Shape = if n % 3 == 0 then Shape.rect { width = n, height = 2 } else Shape.circle { radius = n + 1 }
let via_shape(n: u32): u32 = area(wrap(n))
let direct(n: u32): u32 = area(Shape.circle { radius = n })
let Opt = oneof { none: unit, some: u32 }
let or_else(o: Opt, d: u32): u32 = o {
  none = |u: unit| -> d,
  some = |v: u32| -> v,
}
let via_option(n: u32): u32 = or_else(if n == 0 then Opt.none() else Opt.some(n * 2), 7)
return { types = { Circle, Rect, Shape }, functions = { via_shape, direct, via_option } }
]==],
        entries = { { entry = "via_shape", arity = 1 }, { entry = "direct", arity = 1 },
            { entry = "via_option", arity = 1 } },
        inputs = { { 0 }, { 1 }, { 2 }, { 3 }, { 4 }, { 100 }, { 4294967295 } },
    },
    {
        name = "known-match-lambdas",
        source = [[
let T=oneof {a:u32,b:u32}
let U=oneof {a:unit,b:unit}
let choose(x:u32):u32=T.a(x){a=|v:u32|->v+1,b=|v:u32|->1+true}
let unit_payload(x:u32):u32=U.a(){a=|u:unit|->x+2,b=|u|->missing_capture}
let reversed(x:u32):u32=T.b(x){a=|v:MissingType|->0,b=|v:u32|->v+3}
let Counter={value:u32}
let state=Counter{value=0}
let effect(x:u32):u32=do state.value+=1 return x end
let discarded(x:u32):u32=do
  state.value=0
  let unused=T.a(effect(x))
  return state.value
end
return {functions={choose,unit_payload,reversed,discarded}}
]],
        entries = {{entry="choose",arity=1},{entry="unit_payload",arity=1},
            {entry="reversed",arity=1},{entry="discarded",arity=1}},
        inputs = {{0},{7},{4294967295}},
    },
    {
        name = "immediate-lambdas",
        source = [[
let Box={n:u32}
let box=Box{n=0}
let type_now()=do box.n=box.n*10+1 return u32 end
let argument():u32=do box.n=box.n*10+2 return 7 end
let answer=(|x:type_now()|->x+1)(argument())
let order(x:u32):u32=box.n*100+answer
let direct(x:u32):u32=(|v:u32|->v+1)(x)
let narrow(x:u32):u32=do
 let n=255 let got=(|u:u8|->n+1)(n) return got+(n+1)
end
let copy(x:u32):u32=do
 let b=Box{n=x}
 let result=(|p:Box|->do p.n+=1 return p.n end)(b)
 return result*100+b.n
end
let work(n:u32):u32=do
 let b=Box{n=n}
 let bump():u32=do b.n+=1 return b.n end
 let result=(|u:unit|->bump())(unit())
 return result*100+b.n
end
let effects(x:u32):u32=work(3)
let partial(x:u32):u32=(|a,b:u32|->a+b)(3)(x)
let Op=oneof {step:unit,branch:unit,halt:unit}
let instruction(pc:u32):Op=[Op.step(),Op.branch(),Op.halt()][pc]
let vm(pc,n,a:u32):u32=instruction(pc){
 step=|u:unit|->vm(pc+1,n,a+3),
 branch=|u:unit|->if n==0 then vm(pc+1,n,a) else vm(0,n-1,a),
 halt=|u:unit|->a,
}
let folded(x:u32):u32=vm(0,10,7)
let H=oneof {a:unit,b:unit}
let R={n:u32, matched():u32=H.a(){a=|u:unit|->n,b=later()}}
let r=R{n=2}
let later():(unit):u32=do r.n+=10 return |u:unit|->0 end
let captured=r.matched()
let capture_order(x:u32):u32=r.n*100+captured
return {functions={order,direct,narrow,copy,effects,partial,folded,capture_order}}
]],
        entries = {{entry="order",arity=1},{entry="direct",arity=1},{entry="narrow",arity=1},
            {entry="copy",arity=1},{entry="effects",arity=1},{entry="partial",arity=1},
            {entry="folded",arity=1},{entry="capture_order",arity=1}},
        inputs = {{0},{7},{4294967295}},
    },
    {
        -- A record-valued conditional used to leak the arms' reads into the continuation.
        name = "recordbranch",
        source = [==[
let R = { width: u32, height: u32 }
let wrap(n: u32): R = if n == 0 then R { width = n + 2, height = 3 } else R { width = n, height = 1 }
let width_of(n: u32): u32 = wrap(n).width
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
let inc(x: u32): u32 = x + 1
let dec(x: u32): u32 = x - 1
let pick(c: bool): u32 = do
  let f = if c then inc else dec
  return f(10)
end
let twice(c: bool, x: u32): u32 = do
  let f = if c then |y: u32| -> y + x else |y: u32| -> y * 2
  return f(f(1))
end
let choose(c: bool, x: u32): u32 = do
  let f = if c then |y: u32| -> y + x else |y: u32| -> y * x
  return f(3) + f(4)
end
let with_zero(c: bool, x: u32): u32 = do
  let f = if c then inc else |y: u32| -> y * 0
  return f(x)
end
let pair(c: bool, x: u32): (u32, u32) = do
  let f = if c then inc else dec
  return f(x), f(f(x))
end
let length(c: bool, x: u32): u32 = (if c then |y: u32| -> y + x else |y: u32| -> y * x)(7)
-- A tagged callable that crosses a call boundary: the tag is only known at run time.
let mk(c: bool) = if c then inc else |y: u32| -> y * 3
let use(c: bool, x: u32): u32 = do
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
let C = { v: u32 }
let apply(f: (u32): u32, x: u32): u32 = f(x)
let run(x: u32): u32 = do
  let c = C { v = 10 }
  let g = |y: u32| -> y + c.v
  return apply(g, x)
end
let chained(x: u32): u32 = do
  let c = C { v = 3 }
  let g = |y: u32| -> y + c.v
  return apply(g, apply(g, x))
end
let mk(): (u32): u32 = |x: u32| -> x + 1
let pure(x: u32): u32 = do
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
let C = { v: u32, bump(): u32 = do v += 1 return v end }
let apply(f: (): u32, x: u32): u32 = f() + x
let run(x: u32): u32 = do
  let c = C { v = 10 }
  return apply(c.bump, x)
end
let twice(x: u32): u32 = do
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
    let r = ref(c)
    r.value += d
    let s = ref(c)
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
let Point = { x: u32, y: u32 }
let Opt = oneof { none: unit, some: u32 }
let point(x: u32): Point = Point { x = x, y = x + 1 }
let wrap(x: u32): Opt = if x == 0 then Opt.none() else Opt.some(x * 2)
let pair(x: u32): (Point, u32) = do return point(x), x end
let nested(x: u32): Point = Point { x = wrap(x) { none = |u: unit| -> 0, some = |v: u32| -> v }, y = x }
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
let first(): u32 = shared[0]
let sum(): u32 = shared[0] + shared[1] + shared[2]
let local_pick(i: u32): u32 = do
  let b: array(u32, 3) = [7, 8, 9]
  return b[i]
end
let store(i: u32, v: u32): u32 = do
  let b = [1, 2, 3]
  b[i] = v
  return b[0] + b[1] + b[2]
end
let grid_cell(r: u32, c: u32): u32 = do
  let g = [[1, 2], [3, 4]]
  return g[r][c]
end
let sum2(a: array(u32, 2)): u32 = a[0] + a[1]
let total(x: u32): u32 = do
  let b: array(u32, 2) = [x, x + 1]
  return sum2(b)
end
let doubled(x: u32): array(u32, 3) = do
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
        -- A call result that is an array or a record exists only as an SSA value until it is indexed
        -- or written; the spill into storage must be seen by the store and by a later read.
        name = "callresult",
        source = [==[
let make(x: u32): array(u32, 3) = [x, x + 1, x + 2]
let at_zero(x: u32): u32 = do let a = make(x) return a[0] end
let set_one(x: u32): u32 = do
  let a = make(x)
  a[1] = 9
  return a[0] + a[1] + a[2]
end
let R = { v: u32, w: u32 }
let wrap(x: u32): R = R { v = x, w = x + 1 }
let bump(x: u32): u32 = do
  let r = wrap(x)
  r.v = 9
  return r.v + r.w
end
let pick(a: array(u32, 3), i: u32): u32 = a[i]
let via_param(x: u32): u32 = do
  let a = make(x)
  return pick(a, 2)
end
return { types = { R }, functions = { at_zero, set_one, bump, via_param } }
]==],
        entries = {
            { entry = "at_zero", arity = 1, inputs = { { 0 }, { 5 }, { 4294967295 } } },
            { entry = "set_one", arity = 1, inputs = { { 0 }, { 5 } } },
            { entry = "bump", arity = 1, inputs = { { 0 }, { 5 } } },
            { entry = "via_param", arity = 1, inputs = { { 0 }, { 5 } } },
        },
    },
    {
        -- A top-level initializer is compile-time execution over concrete values, so it can read module
        -- storage; `wordlet_init` assigns each object its start value and a run-time read sees it.
        name = "moduleinit",
        source = [==[
let shared = [10, 20, 30]
let base = shared[2]
let P = { x: u32, y: u32 }
let point = P { x = 3, y = 4 }
let field = point.x + point.y
let pick(i: u32): u32 = shared[i]
let total(x: u32): u32 = x + base + field
let via_point(): u32 = point.x * point.y
return { types = { P }, functions = { pick, total, via_point } }
]==],
        entries = {
            { entry = "pick", arity = 1, inputs = { { 0 }, { 1 }, { 2 } } },
            { entry = "total", arity = 1, inputs = { { 0 }, { 5 }, { 4294967295 } } },
            { entry = "via_point", arity = 0, inputs = { {} } },
        },
    },
    {
        -- Initialization is eager and ordered, so a mutating initializer is supported: the
        -- interpreter and the generated `wordlet_init` observe the same sequence of reads and writes.
        name = "modulemut",
        source = [==[
let shared = [1, 2, 3]
let bump(): u32 = do shared[0] = 9 return shared[0] end
let base = shared[1]
let changed = bump()
let pick(i: u32): u32 = shared[i]
let total(x: u32): u32 = x + base + changed
return { functions = { pick, total } }
]==],
        entries = {
            { entry = "pick", arity = 1, inputs = { { 0 }, { 1 }, { 2 } } },
            { entry = "total", arity = 1, inputs = { { 0 }, { 5 } } },
        },
    },
    {
        -- A top-level result-list binding declares every binder; the generated C sees the same
        -- starting values from `wordlet_init`, including through module storage.
        name = "multibind",
        source = [==[
let divmod(a, b: u32): (u32, u32) = do return a / b, a % b end
let q, r = divmod(17, 5)
let P = { x: u32 }
let p1, p2 = P { x = q }, P { x = r }
let pick(i: u32): u32 = if i == 0 then q else r
let combine(x: u32): u32 = x + q * 100 + r + p1.x * 10 + p2.x
return { types = { P }, functions = { pick, combine } }
]==],
        entries = {
            { entry = "pick", arity = 1, inputs = { { 0 }, { 1 } } },
            { entry = "combine", arity = 1, inputs = { { 0 }, { 7 } } },
        },
    },
    {
        -- `Builder:intern` makes the IR a DAG. The emitter names a node used more than once and
        -- declares it in the innermost statement list containing every use, which covers arms and loops.
        name = "cse",
        source = [==[
let R = { v: u32 }
let pick(c: bool, x: u32): u32 = do
  let r = R { v = 0 }
  if c then
    r.v = x ~ (x << 3)
  else
    r.v = (x ~ (x << 3)) + 1
  end
  return r.v
end
let step(n: u32, x: u32): u32 = do
  if n == 0 then return x ~ (x << 3) end
  let y = x ~ (x << 3)
  return step(n - 1, y)
end
let mixed(c: bool, n: u32, x: u32): u32 = do
  let a = x ~ (x << 3)
  let b = if c then a + n else a - n
  return (x ~ (x << 3)) + b
end
return { types = { R }, functions = { pick, step, mixed } }
]==],
        entries = {
            { entry = "pick", arity = 2, inputs = { { true, 0 }, { false, 5 }, { true, 4294967295 } } },
            { entry = "step", arity = 2, inputs = { { 0, 7 }, { 3, 7 }, { 5, 0 } } },
            { entry = "mixed", arity = 3, inputs = { { true, 2, 7 }, { false, 2, 7 } } },
        },
    },
    {
        -- Narrower integers: arithmetic wraps at the width the type names, widening is implicit, and
        -- a run-time narrowing conversion is checked, which is why each entry has its own inputs.
        name = "widths",
        source = [==[
let wrap8(n: u32): u32 = do
  let a: u8 = u8(n)
  let b = a + 200
  return u32(b)
end
let mix8(n: u32): u32 = do
  let a: u8 = u8(n)
  return u32(a * 3) + u32(a / 2) + u32(a % 7)
end
let wrap16(n: u32): u32 = do
  let a: u16 = u16(n)
  let b = a * 3
  return u32(b)
end
let chain(n: u32): u32 = do
  let a: u8 = u8(n)
  let b: u16 = a
  let c: u32 = b
  return c
end
let bits(n: u32): u32 = do
  let a: u8 = u8(n)
  return u32(a & 15) + u32(a | 16) + u32(a ^ 255)
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
let bits(n: u32): u32 = do
  let a: i32 = i32(n)
  return u32(a & i32(255)) + u32(a | i32(16)) + u32(a ^ i32(255))
end
let negate(n: u32): u32 = do
  let a: i32 = i32(n)
  return u32(-a)
end
-- A converted operand is already i32, so 3 adopts i32 rather than the two sides being read as two
-- literals that cannot be widened across signedness, and a signed power stays exact at 32 bits.
let add_lit(n: u32): i32 = i32(n) + 3
let add_left(n: u32): i32 = 3 + i32(n)
let power(n: u32): i32 = i32(n) ^ 31
return { types = {  }, functions = { round, quotient, shift, bits, negate, add_lit, add_left, power } }
]==],
        entries = {
            { entry = "round", arity = 1, inputs = { { 0 }, { 5 }, { 4294967295 } } },
            { entry = "quotient", arity = 1, inputs = { { 0 }, { 5 }, { 4294967294 }, { 7 } } },
            { entry = "shift", arity = 1, inputs = { { 0 }, { 1 }, { 4294967295 }, { 2147483648 } } },
            { entry = "bits", arity = 1, inputs = { { 0 }, { 130 }, { 4294967295 } } },
            { entry = "negate", arity = 1, inputs = { { 0 }, { 1 }, { 2147483648 } } },
            { entry = "add_lit", arity = 1, inputs = { { 0 }, { 2 }, { 4294967295 } } },
            { entry = "add_left", arity = 1, inputs = { { 0 }, { 2 }, { 4294967295 } } },
            { entry = "power", arity = 1, inputs = { { 0 }, { 1 }, { 2 }, { 3 } } },
        },
    },
    {
        -- 64-bit integers: literals that do not fit a word, widening and narrowing, products that
        -- need both words, division and remainder of a signed value, and a shift into the high word.
        name = "wide",
        source = [==[
let low(): u32 = u32(0xFFFFFFFFFFFFFFFF % 4294967296)
let high(): u32 = u32(0xFFFFFFFFFFFFFFFF / 4294967296)
let square_low(n: u32): u32 = u32(u64(n) * u64(n) % 4294967296)
let square_high(n: u32): u32 = u32(u64(n) * u64(n) / 4294967296)
let cube_low(n: u32): u32 = u32(u64(n) * u64(n) * u64(n) % 4294967296)
let shift_high(n: u32): u32 = u32((u64(1) << (n % 64)) / 4294967296)
let signed_quotient(n: u32): u32 = u32(i64(n) / i64(3))
let signed_remainder(n: u32): u32 = u32(i64(n) % i64(3))
let signed_shift(n: u32): u32 = u32((i64(4294967296) + i64(n)) >> i64(1))
let big_literal(n: u32): u32 = u32((18446744073709551615 + u64(n)) % 4294967296)
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
    {
        name = "strings",
        source = [[
let length_of(): u32 = "hello".length
let empty_length(): u32 = "".length
let first_byte(): u32 = u32("A"[0])
let last_byte(): u32 = u32("abc"[2])
let same(): bool = "hello" == "hello"
let different(): bool = "hello" == "world"
let escaped(): u32 = "a\tb".length
let nul(): u32 = u32("a\0b"[1])
let sum(s: slice(u32)): u32 = s[0] + s[1] + s[2]
let through_call(): u32 = do
  let arr = [10, 20, 30]
  return sum(slice(arr))
end
let whole(): u32 = do
  let arr = [4, 5, 6]
  let view = slice(arr)
  return view.length * 100 + view[1]
end
let size_at(s: string): u32 = s.length
let byte_string(): u32 = size_at("four")
return { functions = { length_of, empty_length, first_byte, last_byte, same, different, escaped,
    nul, through_call, whole, byte_string } }
]],
        entries = {
            { entry = "length_of", arity = 0, inputs = { {} } },
            { entry = "empty_length", arity = 0, inputs = { {} } },
            { entry = "first_byte", arity = 0, inputs = { {} } },
            { entry = "last_byte", arity = 0, inputs = { {} } },
            { entry = "same", arity = 0, inputs = { {} } },
            { entry = "different", arity = 0, inputs = { {} } },
            { entry = "escaped", arity = 0, inputs = { {} } },
            { entry = "nul", arity = 0, inputs = { {} } },
            { entry = "through_call", arity = 0, inputs = { {} } },
            { entry = "whole", arity = 0, inputs = { {} } },
            { entry = "byte_string", arity = 0, inputs = { {} } },
        },
    },
    {
        name = "stringparam",
        source = [[
let length_of(s: string): u32 = s.length
let byte_at(s: string, i: u32): u32 = u32(s[i])
let same(a: string, b: string): bool = a == b
let echo(s: string): string = s
return { functions = { length_of, byte_at, same, echo } }
]],
        entries = {
            { entry = "length_of", arity = 1, inputs = { { "" }, { "a" }, { "hello" } } },
            { entry = "byte_at", arity = 2, inputs = { { "A", 0 }, { "hello", 4 }, { "\255", 0 } } },
            { entry = "same", arity = 2,
                inputs = { { "ab", "ab" }, { "ab", "ac" }, { "", "" } } },
            { entry = "echo", arity = 1, inputs = { { "" }, { "round trip" } } },
        },
    },
    {
        name = "f64",
        source = "let half(x: f64): f64 = x / 2.0\n"
            .. "let negate(x: f64): f64 = -x\n"
            .. "let scaled(x: f64): f64 = half(x) * 2.0 + 1.0\n"
            .. "let ordered(a: f64, b: f64): bool = a < b\n"
            .. "let equal(a: f64, b: f64): bool = a == b\n"
            .. "let truncate(x: f64): u32 = u32(x)\n"
            .. "let widen(n: u32): f64 = f64(n)\n"
            .. "let from_u64(): f64 = f64(18446744073709551615)\n"
            .. "let nan(): f64 = 0.0 / 0.0\n"
            .. "let infinity(): f64 = 1.0 / 0.0\n"
            .. "let nan_eq(): bool = (0.0 / 0.0) == (0.0 / 0.0)\n"
            .. "let nan_ne(): bool = (0.0 / 0.0) != (0.0 / 0.0)\n"
            .. "let folded(): f64 = 2.0 * 3\n"
            .. "let thirds(): f64 = 1.0 / 3.0\n"
            .. "return { functions = { half, negate, scaled, ordered, equal, truncate, widen, from_u64,\n"
            .. "    nan, infinity, nan_eq, nan_ne, folded, thirds } }",
        entries = {
            { entry = "half", arity = 1, inputs = { { 2.5 }, { -2.5 }, { 1e300 }, { 0.5 } } },
            { entry = "negate", arity = 1, inputs = { { 2.5 }, { -0.5 } } },
            { entry = "scaled", arity = 1, inputs = { { 2.5 }, { 0.25 } } },
            { entry = "ordered", arity = 2, inputs = { { 1.5, 2.5 }, { 2.5, 1.5 }, { 1.5, 1.5 } } },
            { entry = "equal", arity = 2, inputs = { { 1.5, 1.5 }, { 1.5, 2.5 } } },
            { entry = "truncate", arity = 1, inputs = { { 2.75 }, { 0 }, { 4294967295.0 } } },
            { entry = "widen", arity = 1, inputs = { { 1 }, { 4294967295 } } },
            { entry = "from_u64", arity = 0, inputs = { {} } },
            { entry = "nan", arity = 0, inputs = { {} } },
            { entry = "infinity", arity = 0, inputs = { {} } },
            { entry = "nan_eq", arity = 0, inputs = { {} } },
            { entry = "nan_ne", arity = 0, inputs = { {} } },
            { entry = "folded", arity = 0, inputs = { {} } },
            { entry = "thirds", arity = 0, inputs = { {} } },
        },
    },
    {
        name = "defer",
        -- Every entry resets the counter first, so the case does not depend on call order.
        source = [==[
let Counter = { n: u32 }
let counter = Counter { n = 0 }

let push(v: u32): u32 = do
  let c = ref(counter)
  c.n = c.n * 10 + v
  return c.n
end

let reset(): u32 = do
  let c = ref(counter)
  c.n = 0
  return 0
end

let body(): u32 = do
  defer push(1)
  defer push(2)
  return 0
end

let ordered(): u32 = do
  reset()
  let before = body()
  return (before + 1) * 1000 + ref(counter).n
end

let arm(): u32 = do
  defer push(7)
  if ref(counter).n == 0 then return 1 end
  return 2
end

let via_arm(): u32 = do
  reset()
  let r = arm()
  return r * 10 + ref(counter).n
end

let countdown(n: u32, acc: u32): u32 = do
  if n == 0 then return acc end
  defer push(n)
  return countdown(n - 1, acc * 10 + n)
end

let tailed(): u32 = do
  reset()
  let acc = countdown(3, 0)
  return acc * 1000 + ref(counter).n
end

let counted(n: u32): u32 = do
  reset()
  return countdown(n, 0)
end
return { functions = { ordered, via_arm, tailed, counted, countdown } }
]==],
        entries = {
            { entry = "ordered", arity = 0, inputs = { {} } },
            { entry = "via_arm", arity = 0, inputs = { {} } },
            { entry = "tailed", arity = 0, inputs = { {} } },
            { entry = "counted", arity = 1, inputs = { { 0 }, { 1 }, { 3 }, { 5 } } },
        },
    },
    {
        name = "recursionmix",
        source = "let f(n: u32): u32 = do\n"
            .. "  if n == 0 then return 0 end\n"
            .. "  if n == 1 then return 100 + f(n - 1) end\n"
            .. "  return f(n - 1)\n"
            .. "end\n"
            .. "let g(n: u32): u32 = if n == 0 then 0 else n + g(n - 1)\n"
            .. "return { functions = { f, g } }",
        entries = {
            { entry = "f", arity = 1, inputs = { { 0 }, { 1 }, { 3 }, { 100 } } },
            -- The reference interpreter is bounded at 1024 nested static evaluations, well below
            -- the host stack limit, so this stays inside that budget; a deeper program reports a
            -- `resource` diagnostic instead of overflowing the Lua stack.
            { entry = "g", arity = 1, inputs = { { 0 }, { 1 }, { 100 }, { 1000 } } },
        },
    },
    {
        name = "literals",
        source = [==[
let banner = [=[
ab
cd
]=]
let banner_length(): u32 = banner.length
let banner_byte(i: u32): u32 = u32(banner[i])
let binary(): u32 = 0b1010_1010
let separated(): u32 = 1_000_000
let hexsep(): u32 = 0xffff_ffff
let byte_eq(): bool = 'a' == 97
let byte_nl(): u32 = u32('\n')
let byte_adapt(x: u8): u8 = 'z' - x
let byte_match(s: string): u32 = if s[0] == 'a' then 1 else 0
let raw_quote(): u32 = [=[a "quoted" word]=].length
let nested(): u32 = [[1, 2], [3, 4]][1][0]
return { functions = { banner_length, banner_byte, binary, separated, hexsep, byte_eq,
    byte_nl, byte_adapt, byte_match, raw_quote, nested } }
]==],
        entries = {
            { entry = "banner_length", arity = 0, inputs = { {} } },
            { entry = "banner_byte", arity = 1, inputs = { { 0 }, { 3 }, { 5 } } },
            { entry = "binary", arity = 0, inputs = { {} } },
            { entry = "separated", arity = 0, inputs = { {} } },
            { entry = "hexsep", arity = 0, inputs = { {} } },
            { entry = "byte_eq", arity = 0, inputs = { {} } },
            { entry = "byte_nl", arity = 0, inputs = { {} } },
            { entry = "byte_adapt", arity = 1, inputs = { { 0 }, { 2 }, { 122 } } },
            -- The empty input is left out: a known index into an empty view rejects while compiling.
            { entry = "byte_match", arity = 1, inputs = { { "abc" }, { "xyz" }, { "a" } } },
            { entry = "raw_quote", arity = 0, inputs = { {} } },
            { entry = "nested", arity = 0, inputs = { {} } },
        },
    },
}

-- A `string` argument is a slice, so it arrives as the same struct any other view uses: a pointer
-- to its bytes and its length. The bytes live in a compound literal with automatic storage, so
-- they last for the call.
-- A double written exactly. A hex float literal denotes the same bits in C11, and an infinity has no
-- literal at all, so it is named from <math.h>; a NaN is tested with `isnan` rather than compared.
local function cFloat(n)
    if n == math.huge then return "INFINITY" end
    if n == -math.huge then return "-INFINITY" end
    return string.format("%a", n)
end

local function cLiteral(value, sliceType)
    -- A Lua number is a double, so a fractional one is an f64 argument written exactly and a whole one
    -- is a u32. An f64 parameter takes the integer constant too, by conversion.
    if type(value) == "number" then
        if value ~= value then return "NAN" end
        -- The same rule `interpret` uses for an argument: a whole number that fits a u32 is one, and
        -- anything else is a double.
        if value % 1 ~= 0 or value < 0 or value > 4294967295 then return cFloat(value) end
        return "UINT32_C(" .. value .. ")"
    end
    if type(value) == "boolean" then return value and "true" or "false" end
    if type(value) == "string" and sliceType then
        local items = {}
        for index = 1, #value do items[#items + 1] = tostring(value:byte(index)) end
        if #items == 0 then items[1] = "0" end
        return "((" .. sliceType .. "){ (uint8_t *)(const uint8_t[]){ " .. table.concat(items, ", ")
            .. " }, UINT32_C(" .. #value .. ") })"
    end
    return nil
end

local function runCase(case, residualInlineBudget)
    local artifact = wordlet.compile{ source = case.source, name = case.name .. ".let",
        residualInlineBudget = residualInlineBudget }
    local unit = artifact:unit()
    local cPath, exePath = directory .. "/" .. case.name .. ".c", directory .. "/" .. case.name
    write(cPath, unit)

    local checksList = {}
    for _, target in ipairs(case.entries or { { entry = case.entry, arity = case.arity } }) do
        -- An entry may carry its own inputs when the shared ones are not valid for it, which is what
        -- an entry with a constrained argument needs.
        for inputIndex, input in ipairs(target.inputs or case.inputs) do
          if #input >= target.arity then
            local args = {}
            for index = 1, target.arity do args[index] = input[index] end
            local expected = wordlet.interpret{ source = case.source, name = case.name .. ".let",
                entry = target.entry, args = args }
            if target.expected then
                check(#expected == 1 and expected[1] == target.expected[inputIndex],
                    "interpreter disagrees with independent oracle for " .. target.entry)
            end
            local literalArgs = {}
            -- The slice layout is numbered by first use, so the argument type is read from the unit.
            local sliceType = unit:match("(wordletslice_%d+)")
            for index, value in ipairs(args) do literalArgs[index] = cLiteral(value, sliceType) end
            -- Export names are escaped: underscore becomes _5F, so the C symbol is not the source name.
            local call = C.functionName(target.entry) .. "(" .. table.concat(literalArgs, ", ") .. ")"
            local before = #checksList
            -- A double is compared through the return type rather than through the Lua value, because a
            -- Lua number cannot say whether it means an integer or a float.
            local returns = #expected == 1 and resultType(unit, C.functionName(target.entry)) or nil
            local scalar = #expected == 1 and cLiteral(expected[1]) ~= nil
            if #expected == 1 and returns == "double" then
                if expected[1] ~= expected[1] then
                    checksList[#checksList + 1] = "    assert(isnan(" .. call .. "));"
                else
                    checksList[#checksList + 1] = "    assert((" .. call .. ") == " .. cFloat(expected[1]) .. ");"
                end
            elseif scalar then
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

    local main = { "#include <assert.h>", "#include <math.h>", "#include <stdint.h>", "#include <stdbool.h>", "",
        unit, "", "int main(void) {" }
    -- Module-level storage is assigned by an explicit host call, not implicitly.
    if unit:find("void wordlet_init(void)", 1, true) then main[#main + 1] = "    wordlet_init();" end
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

-- Exercise the same semantics both with host-only helper inlining and with contextual copies.
for _, budget in ipairs({0, 256}) do
    for _, case in ipairs(CASES) do runCase(case, budget) end
end

-- A residual instance that nothing calls or points at is dropped before ownership is computed, so a
-- private function always has a caller and plain internal linkage satisfies -Werror.
do
    local closures
    for _, case in ipairs(CASES) do if case.name == "closures" then closures = case.source end end
    check(closures ~= nil, "the closures case is missing")
    local generated = wordlet.compile{ source = closures, name = "closures.let" }:unit()
    local counts = {}
    for name in generated:gmatch("(wordletfn_%d+)") do counts[name] = (counts[name] or 0) + 1 end
    local dead = 0
    for _, count in pairs(counts) do if count < 3 then dead = dead + 1 end end
    check(dead == 0, "an unreferenced residual instance was emitted: " .. dead)
    check(generated:find("#define WORDLET_PRIVATE static inline __attribute__((always_inline))", 1, true) ~= nil,
        "a private function is asked to inline by default")
    local plain = wordlet.compile{ source = closures, name = "closures.let", inline = false }:unit()
    check(plain:find("WORDLET_PRIVATE", 1, true) == nil and plain:find("static ", 1, true) ~= nil,
        "inline = false gives a private function plain internal linkage")
end

-- `Builder:intern` shares structurally equal expressions, so a chain that rebuilds each value from
-- the previous one is a DAG. Naming the shared nodes keeps the generated C linear instead of
-- exponential; this guards that and runs the result.
do
    local lines = { "let f(s: u32): u32 = do" }
    local previous = "s"
    for index = 1, 14 do
        lines[#lines + 1] = ("  let a%d = (%s ~ (%s << 3))"):format(index, previous, previous)
        previous = "a" .. index
    end
    lines[#lines + 1] = ("  return %s"):format(previous)
    lines[#lines + 1] = "end"
    lines[#lines + 1] = "return { functions = { f } }"
    local program = table.concat(lines, "\n")
    local generated = wordlet.compile{ source = program, name = "cse.let" }:unit()
    check(#generated < 20000, "shared expressions were expanded, not named: " .. #generated .. " bytes")
    local expected = wordlet.interpret{ source = program, name = "cse.let", entry = "f", args = { 1 } }[1]
    local path = directory .. "/cse.c"
    write(path, generated .. "\n\n#include <assert.h>\nint main(void) {\n    assert(wordlet_f(UINT32_C(1)) == UINT32_C("
        .. expected .. "));\n    return 0;\n}\n")
    local exe = directory .. "/cse"
    check(shell("timeout --kill-after=2s 30s " .. CC .. " -std=c11 -Wall -Wextra -Werror -O2 -o '"
        .. exe .. "' '" .. path .. "' 2> " .. directory .. "/cseerr.txt") == 0,
        "shared-expression C failed to compile:\n" .. read(directory .. "/cseerr.txt"))
    check(shell("timeout --kill-after=2s 10s '" .. exe .. "'") == 0,
        "shared-expression C produced the wrong value")
end

-- Each aggregate is named once: a forward `typedef struct X X;` and then a plain `struct X {...};`.
-- That is valid C99 as well as C11, so a program exercising every aggregate shape must compile under
-- `-std=c99 -pedantic` without a repeated-typedef warning. The program has no recursion, so the
-- forced-inlining attribute is never asked to inline a recursive function.
do
    local source = table.concat({
        "let Point = { x: u32, y: u32 }",
        "let Shape = oneof { dot: Point, empty: unit }",
        "let area(s: Shape): u32 = s {",
        "  dot = |p: Point| -> p.x * p.y,",
        "  empty = |u: unit| -> 0,",
        "}",
        "let first(a: array(u32, 3)): u32 = a[0]",
        "let at(s: slice(u32), i: u32): u32 = s[i]",
        "let apply(f: (u32): u32, x: u32): u32 = f(x)",
        "let pair(a: u32, b: u32): (u32, u32) = do return a, b end",
        "let inc(x: u32): u32 = x + 1",
        "let dec(x: u32): u32 = x - 1",
        "let choose(c: bool, x: u32): u32 = (if c then inc else dec)(x)",
        "return { types = { Point, Shape }, functions = { area, first, at, apply, pair, choose } }",
    }, "\n")
    local generated = wordlet.compile{ source = source, name = "c99.let" }:unit()
    check(not generated:find("typedef struct [%w_]+ {"),
        "a struct body must not repeat the typedef that already declared its tag")
    local path = directory .. "/c99.c"
    write(path, generated)
    check(shell("timeout --kill-after=2s 30s " .. CC .. " -std=c99 -pedantic -Wall -Wextra -Werror"
        .. " -O2 -c -o /dev/null '" .. path .. "' 2> " .. directory .. "/c99err.txt") == 0,
        "emitted C is not C99-pedantic clean:\n" .. read(directory .. "/c99err.txt"))
end

-- A self-tail call must not consume C stack. Without the loop rewrite this overflows; with it,
-- the call is a back edge and the depth is constant. This runs only in C because the reference
-- interpreter would recurse in Lua.
do
    local source = "let count_down(n: u32) : u32 = if n == 0 then 7 else count_down(n - 1)\n"
        .. "let sum_to(n, acc: u32) : u32 = if n == 0 then acc else sum_to(n - 1, acc + n)\n"
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
    local source = "let apply(f: (u32): u32, x: u32): u32 = f(x)\n"
        .. "let twice_apply(f: (u32): u32, x: u32): u32 = apply(f, apply(f, x))\n"
        .. "let compose(f: (u32): u32, g: (u32): u32, x: u32): u32 = f(g(x))\n"
        .. "let invoke(f: (u32): (), x: u32): u32 = do f(x) return x end\n"
        .. "let internal(x: u32): u32 = apply(|y: u32| -> y + 1, x)\n"
        .. "return { functions = { apply, twice_apply, compose, invoke, internal } }"
    local generated = wordlet.compile{ source = source, name = "callbacks.let" }:unit()
    local path = directory .. "/callbacks.c"
    write(path, generated .. [[

#include <assert.h>
#include <stddef.h>
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
    local source = "let Counter = { value: u32, bump(): u32 = do value += 1 return value end }\n"
        .. "let shared = Counter { value = 100 }\n"
        .. "let bump_twice(x: u32): u32 = do shared.bump() shared.bump() return shared.value + x end\n"
        .. "let bump_field(a: u32): u32 = do shared.value += a return shared.value end\n"
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
    local source = "let Holder = { f: (u32): u32 }\n"
        .. "let use(n: u32): u32 = do\n  let h = Holder { f = |x: u32| -> x + n }\n  return h.f(1)\nend\n"
        .. "let chase(n: u32): u32 = do\n  let h = Holder { f = |x: u32| -> x * 2 }\n"
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
let Circle = { radius: u32 }
let Rect = { width: u32, height: u32 }
let Shape = oneof { circle: Circle, rect: Rect }
let area(s: Shape): u32 = s {
  circle = |c: Circle| -> c.radius * c.radius,
  rect = |r: Rect| -> r.width * r.height,
}
let rect_of(w: u32): Shape = Shape.rect { width = w, height = 2 }
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

-- A unit parameter is erased rather than represented: a unit alternative's handler takes no C
-- argument, and the generated code must still compile under -Werror.
do
    local source = [==[
let Opt = oneof { none: unit, some: u32 }
let or_else(o: Opt, d: u32): u32 = o {
  none = |u: unit| -> d,
  some = |v: u32| -> v,
}
let unwrap_or(n: u32, d: u32): u32 = or_else(if n == 0 then Opt.none() else Opt.some(n), d)
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
        "unit-parameter C failed to compile:\n" .. read(directory .. "/opterr.txt"))
    check(shell("timeout --kill-after=2s 10s '" .. exe .. "'") == 0,
        "a unit alternative did not erase cleanly at the ABI")
end

-- A tagged callable as a host-visible value: the tag is a plain word and the payload union holds
-- that arm environment, so a host can hold one and pass it back.
do
    local source = [==[
let inc(x: u32): u32 = x + 1
let dec(x: u32): u32 = x - 1
let mk(c: bool) = if c then inc else dec
let use(c: bool, x: u32): u32 = do
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
let C = { v: u32 }
let mk(): (u32): u32 = |x: u32| -> x + 1
let pure(x: u32): u32 = do
  let f = mk()
  return f(f(x))
end
let apply(f: (u32): u32, x: u32): u32 = f(x)
let run(x: u32): u32 = do
  let c = C { v = 10 }
  let g = |y: u32| -> y + c.v
  return apply(g, x)
end
return { types = { C }, functions = { mk, pure, run } }
]==]
    local generated = wordlet.compile{ source = source, name = "pure.let" }:unit()
    local path = directory .. "/pure.c"
    write(path, generated .. [[

#include <assert.h>
#include <stddef.h>
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
let Counter = { value: u32 }
let shared = Counter { value = 5 }
let read_shared(x: u32): u32 = ref(shared).value + x
-- A call with a literal argument is still a run-time read of module storage, so it must observe a
-- mutation the host made after `wordlet_init` rather than a snapshot folded while compiling.
let peek(): u32 = read_shared(1)
let via(r: ref(Counter)): u32 = r.value
let via_set(r: ref(Counter), v: u32): u32 = do
  r.value = v
  return r.value
end
let bump_shared(x: u32): u32 = do
  let r = ref(shared)
  r.value += 1
  return r.value + x
end
let Node = { value: u32, next: Link }
let Link = oneof { none: unit, some: ref(Node) }
let n1 = Node { value = 10, next = Link.none() }
let n0 = Node { value = 1, next = Link.some(ref(n1)) }
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
return { types = { Counter, Node, Link }, functions = { read_shared, peek, via, via_set, bump_shared, following, bump_following } }
]==]
    local artifact = wordlet.compile{ source = source, name = "refmod.let" }
    local generated = artifact:unit()
    -- Module storages are numbered in first-demand order, so find `shared` by its source name.
    local sharedPointer
    for _, entry in ipairs(artifact.layouts.modules.order) do
        if entry.source == "shared" then sharedPointer = "&" .. entry.name end
    end
    check(sharedPointer ~= nil, "the shared module storage was not emitted")
    local path = directory .. "/refmod.c"
    write(path, generated .. ([[

#include <assert.h>
int main(void) {
    wordlet_init();
    assert(wordlet_read_5Fshared(UINT32_C(1)) == UINT32_C(6));
    assert(wordlet_bump_5Fshared(UINT32_C(1)) == UINT32_C(7));
    /* the bump stores the incremented value and returns it plus its argument */
    assert(wordlet_read_5Fshared(UINT32_C(0)) == UINT32_C(6));
    /* shared.value is 6 now, so a literal-argument call must answer 7 rather than the start value. */
    assert(wordlet_peek() == UINT32_C(7));
    /* a host may pass a pointer for a reference parameter */
    assert(wordlet_via(%s) == UINT32_C(6));
    assert(wordlet_via_5Fset(%s, UINT32_C(20)) == UINT32_C(20));
    assert(wordlet_read_5Fshared(UINT32_C(0)) == UINT32_C(20));
    /* a point in a stored structure, reached by a reference and mutated through it */
    assert(wordlet_following() == UINT32_C(10));
    assert(wordlet_bump_5Ffollowing() == UINT32_C(15));
    assert(wordlet_following() == UINT32_C(15));
    return 0;
}
]]):format(sharedPointer, sharedPointer))
    local exe = directory .. "/refmod"
    check(shell("timeout --kill-after=2s 30s " .. CC .. " -std=c11 -Wall -Wextra -Werror -O2 -o '"
        .. exe .. "' '" .. path .. "' 2> " .. directory .. "/refmoderr.txt") == 0,
        "reference and recursion C failed to compile:\n" .. read(directory .. "/refmoderr.txt"))
    check(shell("timeout --kill-after=2s 10s '" .. exe .. "'") == 0,
        "a reference over module storage or a recursive structure did not run correctly")
end

-- A host function is declared, never defined: the artifact carries a prototype and the call is direct.
-- The host links its own definition, so this is C-only, and the reference interpreter has no binding
-- to call, which is why a constant argument does not make a foreign call foldable.
do
    local source = [==[
extern let host_add(a: u32, b: u32) : u32
extern let host_scale(a: u32) : u32
extern let host_sink(a: u32) : unit

let combined(x: u32): u32 = host_add(x, host_scale(x))
let ignored(x: u32): u32 = do
  host_sink(x)
  return host_scale(x)
end
return { functions = { combined, ignored } }
]==]
    local generated = wordlet.compile{ source = source, name = "foreign.let" }:unit()
    check(generated:find("uint32_t host_scale(uint32_t a1);", 1, true) ~= nil,
        "a foreign word is declared, not defined")
    check(generated:find("WORDLET_PRIVATE uint32_t host_scale", 1, true) == nil,
        "a foreign prototype has external linkage")
    local path = directory .. "/foreign.c"
    write(path, generated .. [[

#include <assert.h>
uint32_t host_scale(uint32_t a) { return a * 10; }
uint32_t host_add(uint32_t a, uint32_t b) { return a + b; }
static uint32_t sunk;
void host_sink(uint32_t a) { sunk = a; }
int main(void) {
    assert(wordlet_combined(UINT32_C(3)) == UINT32_C(33));
    assert(wordlet_ignored(UINT32_C(4)) == UINT32_C(40));
    assert(sunk == UINT32_C(4));
    return 0;
}
]])
    check(shell("timeout --kill-after=2s 30s " .. CC .. " -std=c11 -Wall -Wextra -Werror -O2 -o '"
        .. directory .. "/foreign' '" .. path .. "' 2> " .. directory .. "/foreignerr.txt") == 0,
        "foreign declaration C failed to compile:\n" .. read(directory .. "/foreignerr.txt"))
    check(shell("timeout --kill-after=2s 10s '" .. directory .. "/foreign'") == 0,
        "a declared host function did not run correctly")
end

-- A raw pointer is an address the compiler does not track, and a host region is acquired and released
-- by an ordinary word that takes a body. When the body is known that word inlines away entirely, so
-- what survives in the generated code is the acquire, the body, and the release, in that order.
do
    local source = [==[
extern let host_region(bytes: u32) : ptr(u8)
extern let host_release(p: ptr(u8)) : unit
extern let host_null() : ptr(u8)

let with_region(R: type, bytes: u32, body: (ptr(u8)): R) : R = do
  let region = host_region(bytes)
  let result = body(region)
  host_release(region)
  return result
end

let sum() : u32 = with_region(u32, 8, |p: ptr(u8)| -> do
  p[0] = 7
  p[1] = 35
  return u32(p[0]) + u32(p[1])
end)

let missing() : bool = host_null() == null(u8)
let present() : bool = host_region(4) == null(u8)

-- A pointer to a record selects a field through it, and a pointer is an indirection boundary, so a
-- type may mention itself through one and still have a finite layout.
let Point = { x: u32, y: u32 }
extern let host_point() : ptr(Point)
-- `null(T)` names any element type, including a user record: the pointer is the runtime value, so
-- what must have a representation is `ptr(T)`, not `T` itself.
let nothing() : ptr(Point) = null(Point)
let total() : u32 = host_point().x + host_point().y
let raised() : u32 = do
  host_point().x += 10
  return host_point().x
end

let Node = { value: u32, next: ptr(Node) }
extern let host_node() : ptr(Node)
-- A recursive named target is representable as a pointer even though the named cell itself is not a
-- runtime value, so the null pointer to it is accepted.
let none() : ptr(Node) = null(Node)
let chain() : u32 = do
  let head = host_node()
  return head.value + head.next.value
end

-- `ptr(place)` to storage the program already has. The array index is still checked; the pointer
-- index that follows it is not, which is the whole difference between the two.
let pool = [7, 8, 9]
let at(i: u32) : u32 = ptr(pool[i])[0]
let set(i: u32, v: u32) : u32 = do
  ptr(pool[i])[0] = v
  return ptr(pool[i])[0]
end
return { functions = { sum, missing, present, at, set, total, raised, chain, nothing, none } }
]==]
    local generated = wordlet.compile{ source = source, name = "ptr.let" }:unit()
    check(generated:find("uint8_t * host_region(uint32_t", 1, true) ~= nil,
        "a foreign declaration returning a pointer is declared, not defined")
    -- The combinator is neither called nor emitted: a known body makes it straight-line code.
    check(generated:find("with_5Fregion", 1, true) == nil,
        "a known body inlines the combinator away, leaving no call and no helper")
    -- A known body is specialized rather than erased, so the whole unit holds no invocation pointer at
    -- all: the call site is a direct call to a per-invocation copy of the combinator.
    check(generated:find("wordletview", 1, true) == nil,
        "a known body needs no invocation pointer")
    check(select(2, generated:gsub("with_5Fregion", "")) == 0,
        "no generic instantiation of the combinator survives")
    local acquire, release = generated:find("host_region(", 1, true),
        generated:find("host_release(", 1, true)
    check(acquire ~= nil and release ~= nil and acquire < release,
        "the region is acquired before the body and released after it")
    local path = directory .. "/ptr.c"
    -- The layouts are numbered by first use, so the host's own signatures are read from the artifact
    -- rather than guessed: `ptr(Point)` is a `Point *`, and a pointer to a record is that record's type.
    local pointType = generated:match("(wordletrecord_%d+) %* host_point")
    local nodeType = generated:match("(wordletrecord_%d+) %* host_node")
    check(pointType ~= nil and nodeType ~= nil, "the pointer targets have named layouts")
    check(generated:match("(wordletrecord_%d+) %* wordlet_none") == nodeType,
        "null(Node) resolves a recursive named target to the node layout")
    write(path, generated .. ([[

#include <assert.h>
#include <stddef.h>
#include <string.h>
static unsigned char arena[16];
static unsigned char slot[64];
static unsigned releases;
uint8_t *host_region(uint32_t bytes) {
    releases = 0;
    memset(arena, 0, sizeof arena);
    (void)bytes;
    return arena;
}
void host_release(uint8_t *p) { releases += 1; (void)p; }
uint8_t *host_null(void) { return NULL; }
%s *host_point(void) { return (%s *)slot; }
%s *host_node(void) { return (%s *)slot; }
int main(void) {
    wordlet_init();
    assert(wordlet_sum() == UINT32_C(42));
    assert(arena[0] == 7 && arena[1] == 35);
    assert(releases == 1);
    assert(wordlet_missing() == true);
    assert(wordlet_present() == false);
    assert(wordlet_at(UINT32_C(0)) == UINT32_C(7));
    assert(wordlet_set(UINT32_C(2), UINT32_C(77)) == UINT32_C(77));
    memset(slot, 0, sizeof slot);
    { %s *p = (%s *)slot; p->f_x = 3; p->f_y = 4; }
    assert(wordlet_total() == UINT32_C(7));
    assert(wordlet_raised() == UINT32_C(13));
    memset(slot, 0, sizeof slot);
    { %s *n = (%s *)slot;
      %s *next = (%s *)((unsigned char *)slot + 32);
      n->f_value = 5; n->f_next = next; next->f_value = 6; }
    assert(wordlet_chain() == UINT32_C(11));
    assert(wordlet_nothing() == NULL);
    assert(wordlet_none() == NULL);
    return 0;
}
]]):format(pointType, pointType, nodeType, nodeType, pointType, pointType,
        nodeType, nodeType, nodeType, nodeType))
    check(shell("timeout --kill-after=2s 30s " .. CC .. " -std=c11 -Wall -Wextra -Werror -O2 -o '"
        .. directory .. "/ptr' '" .. path .. "' 2> " .. directory .. "/ptrerr.txt") == 0,
        "pointer C failed to compile:\n" .. read(directory .. "/ptrerr.txt"))
    check(shell("timeout --kill-after=2s 10s '" .. directory .. "/ptr'") == 0,
        "a pointer or a scoped region did not run correctly")
end

-- A bare `return` and `unit()` are one unit result, which the ABI erases to `void`. The slot stays
-- logical, so a unit in a multiple-result vector keeps its position while the C result drops it.
do
    local source = [==[
extern let sink(x: u32) : unit
let announce(x: u32) : unit = do sink(x) return end
let explicit(x: u32) : unit = do sink(x) return; end
let value(x: u32) : unit = do sink(x) return unit() end
let pair(x: u32) : (unit, u32) = do return unit(), x end
let use(x: u32) : u32 = do let u, y = pair(x) return y end
return { functions = { announce, explicit, value, pair, use } }
]==]
    local generated = wordlet.compile{ source = source, name = "unit.let" }:unit()
    check(generated:find("void wordlet_announce", 1, true) ~= nil, "a bare unit return erases to void")
    check(generated:find("void wordlet_explicit", 1, true) ~= nil, "return; erases to void")
    check(generated:find("void wordlet_value", 1, true) ~= nil, "unit() erases to void")
    check(generated:find("uint32_t wordlet_pair", 1, true) ~= nil,
        "a unit slot erases from a multiple-result vector")
    local path = directory .. "/unit.c"
    write(path, generated .. [[

#include <assert.h>
static uint32_t calls;
void sink(uint32_t x) { calls += x; }
int main(void) {
    wordlet_announce(UINT32_C(1));
    wordlet_explicit(UINT32_C(2));
    wordlet_value(UINT32_C(4));
    assert(calls == UINT32_C(7));
    assert(wordlet_use(UINT32_C(9)) == UINT32_C(9));
    assert(wordlet_pair(UINT32_C(5)) == UINT32_C(5));
    return 0;
}
]])
    check(shell("timeout --kill-after=2s 30s " .. CC .. " -std=c11 -Wall -Wextra -Werror -O2 -o '"
        .. directory .. "/unit' '" .. path .. "' 2> " .. directory .. "/uniterr.txt") == 0,
        "unit C failed to compile:\n" .. read(directory .. "/uniterr.txt"))
    check(shell("timeout --kill-after=2s 10s '" .. directory .. "/unit'") == 0,
        "a unit result did not erase and run correctly")
end

-- A residual match may yield a result vector, one slot per result, and a pointer may index record
-- and sum storage. Both were assumptions the lowering and the verifier made too narrowly.
do
    local source = [==[
let Op = oneof { a: unit, b: unit, n: u32 }
let classify(k: u32): Op =
  if k == 0 then Op.a()
  else if k == 1 then Op.b()
  else Op.n(k)

let pick(op: Op, x: u32): (u32, u32) = op {
  a = |u: unit| -> do return x + 1, x + 2 end,
  b = |u: unit| -> do return x + 3, x + 4 end,
  n = |v: u32| -> do return v, x end,
}
let total(k: u32, x: u32): u32 = do let p, q = pick(classify(k), x) return p + q end

let Point = { x: u32, y: u32 }
extern let host_points() : ptr(Point)
let point_at(i: u32): u32 = do
  let p = host_points()[i]
  return p.x + p.y
end

let program = [Op.n(7), Op.a()]
let code_at(i: u32): u32 = do
  let op = ptr(program[0])[i]
  return op {
    a = |u: unit| -> 1,
    b = |u: unit| -> 2,
    n = |v: u32| -> v,
  }
end
return { types = { Point, Op }, functions = { total, point_at, code_at } }
]==]
    local generated = wordlet.compile{ source = source, name = "matchptr.let" }:unit()
    check(generated:find("switch (", 1, true) ~= nil,
        "an opaque match lowers to a switch, not a chain of compares")
    check(generated:find("default: {", 1, true) ~= nil,
        "the switch is total: the last alternative is the default")
    local pointType = generated:match("(wordletrecord_%d+) %* host_points")
    check(pointType ~= nil, "the pointer target has a named layout")
    local path = directory .. "/matchptr.c"
    write(path, generated .. ([[

#include <assert.h>
static %s points[2];
%s *host_points(void) { return points; }
int main(void) {
    wordlet_init();
    points[0].f_x = 3; points[0].f_y = 4;
    points[1].f_x = 10; points[1].f_y = 20;
    assert(wordlet_point_5Fat(UINT32_C(0)) == UINT32_C(7));
    assert(wordlet_point_5Fat(UINT32_C(1)) == UINT32_C(30));
    assert(wordlet_code_5Fat(UINT32_C(0)) == UINT32_C(7));
    assert(wordlet_code_5Fat(UINT32_C(1)) == UINT32_C(1));
    assert(wordlet_total(UINT32_C(0), UINT32_C(10)) == UINT32_C(23));
    assert(wordlet_total(UINT32_C(1), UINT32_C(10)) == UINT32_C(27));
    assert(wordlet_total(UINT32_C(9), UINT32_C(10)) == UINT32_C(19));
    return 0;
}
]]):format(pointType, pointType))
    check(shell("timeout --kill-after=2s 30s " .. CC .. " -std=c11 -Wall -Wextra -Werror -O2 -o '"
        .. directory .. "/matchptr' '" .. path .. "' 2> " .. directory .. "/matchptrerr.txt") == 0,
        "match/pointer C failed to compile:\n" .. read(directory .. "/matchptrerr.txt"))
    check(shell("timeout --kill-after=2s 10s '" .. directory .. "/matchptr'") == 0,
        "a multi-result match or a pointer index did not run correctly")
end

-- Host data uses the schema written on the foreign result; a typed raw pointer borrows the
-- addressed record's place but adds no ownership guarantee or runtime method table.
do
    local source = [=[
let counter = { n: u32, bump(): u32 = do n += 1 return n end }
let shared = counter { n = 0 }
extern let host_counter(): counter
let run(x: u32): u32 = do
    shared.n = x
    let c = host_counter()
    let first = c.bump()
    let p: ptr(counter) = ptr(shared)
    return first * 10 + p[0].bump()
end
return { functions = { run } }
]=]
    local generated = wordlet.compile{ source = source, name = "hostinterface.let" }:unit()
    local record = generated:match("(wordletrecord_%d+) host_counter%(")
    check(record ~= nil, "foreign record result has a concrete C layout")
    local path = directory .. "/hostinterface.c"
    write(path, generated .. ([[
#include <assert.h>
%s host_counter(void) { %s c = { .f_n = UINT32_C(9) }; return c; }
int main(void) {
    wordlet_init();
    assert(wordlet_run(UINT32_C(0)) == UINT32_C(101));
    assert(wordlet_run(UINT32_C(3)) == UINT32_C(104));
    return 0;
}
]]):format(record, record))
    check(shell("timeout --kill-after=2s 30s " .. CC .. " -std=c11 -Wall -Wextra -Werror -O2 -o '"
        .. directory .. "/hostinterface' '" .. path .. "' 2> " .. directory .. "/hostinterfaceerr.txt") == 0,
        "schema-directed foreign/pointer C failed to compile:\n" .. read(directory .. "/hostinterfaceerr.txt"))
    check(shell("timeout --kill-after=2s 10s '" .. directory .. "/hostinterface'") == 0,
        "schema-directed foreign result or pointer did not reach the actual receiver")
end

-- The hot-state interpreter example: the machine is the loop's parameters and the handlers return
-- the transition, so dispatch copies no aggregate and is one back edge. It indexes through a `ptr`,
-- so only compiled code can run it.
do
    local path = (source:match("^(.*[/\\])") or "./") .. "../examples/interpreter.let"
    local file = assert(io.open(path, "rb"))
    local source = assert(file:read("*a"))
    assert(file:close())
    local generated = wordlet.compile{ source = source, name = "interpreter.let" }:unit()
    check(generated:find("for (;;)", 1, true) ~= nil, "the interpreter loop is a back edge")
    local cPath = directory .. "/interpreter.c"
    write(cPath, generated .. "\n#include <assert.h>\nint main(void) { assert(wordlet_main() == UINT32_C(7)); return 0; }\n")
    check(shell("timeout --kill-after=2s 30s " .. CC .. " -std=c11 -Wall -Wextra -Werror -O2 -o '"
        .. directory .. "/interpreter' '" .. cPath .. "' 2> " .. directory .. "/interpretererr.txt") == 0,
        "interpreter C failed to compile:\n" .. read(directory .. "/interpretererr.txt"))
    check(shell("timeout --kill-after=2s 10s '" .. directory .. "/interpreter'") == 0,
        "the hot-state interpreter did not run correctly")
end

-- A pointer is not a reference, in either direction: it cannot satisfy a `ref` requirement, and
-- `ref(p)` cannot turn one back into a checked borrow.
do
    local shared = "extern let host_null() : ptr(u8)\n"
    local ok, err = pcall(function()
        return wordlet.compile{ source = shared
            .. "let takes(r: ref(u8)): u32 = 0\nlet use(): u32 = takes(host_null())\n"
            .. "return { functions = { use } }", name = "ptrref.let" }
    end)
    check(not ok and D.is(err) and err.code == "type-mismatch",
        "a pointer does not satisfy a reference requirement")
    local ok2, err2 = pcall(function()
        return wordlet.compile{ source = shared
            .. "let use(): u32 = do\n  let r = ref(host_null())\n  return 1\nend\n"
            .. "return { functions = { use } }", name = "ptrref2.let" }
    end)
    check(not ok2 and D.is(err2) and err2.code == "ref-target",
        "a pointer cannot be turned back into a reference")
end

-- A pool of nodes in module storage, reached by a reference to an element, and the bounds guard a
-- run-time index needs. Both are runtime-only, so this is C-only.
do
    local source = [==[
let Counter = { value: u32 }
let pool = [Counter { value = 1 }, Counter { value = 2 }, Counter { value = 3 }]
let bump(i: u32, d: u32): u32 = do
  let r = ref(pool[i])
  r.value += d
  return r.value
end
let read(i: u32): u32 = ref(pool[i]).value
let pick(i: u32): u32 = do
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
let narrow(n: u32): u8 = u8(n)
let read(n: u32): u32 = u32(narrow(n))
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

-- bool and unit equality are documented (syntax.md section 7) and used to reject. bool compares by
-- value; unit has one value, so its answer is known. Ordering is still not offered for either.
do
    local source = "let bool_eq(a: bool, b: bool): bool = a == b\n"
        .. "let bool_ne(a: bool, b: bool): bool = a != b\n"
        .. "let unit_eq(): bool = unit() == unit()\n"
        .. "let unit_ne(): bool = unit() != unit()\n"
        .. "let use(a: bool, b: bool): u32 = do\n"
        .. "  if bool_eq(a, b) then return 1 end\n"
        .. "  if bool_ne(a, b) then return 2 end\n"
        .. "  return 3\nend\n"
        .. "return { functions = { use, unit_eq, unit_ne } }"
    local generated = wordlet.compile{ source = source, name = "boolunit.let" }:unit()
    local path = directory .. "/boolunit.c"
    write(path, generated .. [[

#include <assert.h>
int main(void) {
    assert(wordlet_use(true, true) == UINT32_C(1));
    assert(wordlet_use(true, false) == UINT32_C(2));
    assert(wordlet_use(false, false) == UINT32_C(1));
    assert(wordlet_unit_5Feq() == true);
    assert(wordlet_unit_5Fne() == false);
    return 0;
}
]])
    local exe = directory .. "/boolunit"
    check(shell("timeout --kill-after=2s 30s " .. CC .. " -std=c11 -Wall -Wextra -Werror -O2 -o '"
        .. exe .. "' '" .. path .. "' 2> " .. directory .. "/buerror.txt") == 0,
        "bool/unit equality C failed to compile:\n" .. read(directory .. "/buerror.txt"))
    check(shell("timeout --kill-after=2s 10s '" .. exe .. "'") == 0,
        "bool/unit equality produced the wrong value")
    local ok, err = pcall(function()
        return wordlet.compile{ source = "let f(a: bool, b: bool): bool = a < b\n"
            .. "return { functions = { f } }", name = "boolorder.let" }
    end)
    check(not ok and D.is(err) and err.code == "type-mismatch", "ordering bool is still rejected")
end

-- A non-tail self-call leaves a genuinely recursive function, which GCC refuses to force-inline.
-- The function keeps plain `static` linkage so the program compiles under -Werror and still runs.
do
    local source = "let sum_from(n: u32): u32 = do\n"
        .. "  if n == 0 then return 0 end\n"
        .. "  let rest = sum_from(n - 1)\n"
        .. "  return n + rest\nend\n"
        .. "let sum(n: u32): u32 = sum_from(n)\n"
        .. "return { functions = { sum } }"
    local generated = wordlet.compile{ source = source, name = "recur.let" }:unit()
    check(generated:find("static uint32_t wordletfn_", 1, true) ~= nil,
        "a non-tail self-recursive private function must not be force-inlined")
    local path = directory .. "/recur.c"
    write(path, generated .. "\n#include <assert.h>\n"
        .. "int main(void) { assert(wordlet_sum(UINT32_C(10)) == UINT32_C(55)); return 0; }\n")
    local exe = directory .. "/recur"
    check(shell("timeout --kill-after=2s 30s " .. CC .. " -std=c11 -Wall -Wextra -Werror -O2 -o '"
        .. exe .. "' '" .. path .. "' 2> " .. directory .. "/recurerr.txt") == 0,
        "non-tail self-recursion C failed to compile:\n" .. read(directory .. "/recurerr.txt"))
    check(shell("timeout --kill-after=2s 10s '" .. exe .. "'") == 0,
        "a non-tail self-recursive function did not run correctly")
end

-- A definition used once is lowered at its use: no `(void)` cast, a returned call inlined, and a
-- record conditional stores its construction instead of reading each field back and rebuilding it.
do
    local source = "let inc(x: u32): u32 = x + 1\n"
        .. "let use(x: u32): u32 = inc(x)\n"
        .. "let Point = { x: u32, y: u32 }\n"
        .. "let make(c: bool, x: u32): Point = if c then Point { x = x, y = 0 } else Point { x = 0, y = x }\n"
        .. "return { types = { Point }, functions = { use, make } }"
    local generated = wordlet.compile{ source = source, name = "clean.let" }:unit()
    check(not generated:find("(void)", 1, true), "a used call result must not need a `(void)` cast")
    check(generated:find("return wordletfn_", 1, true) ~= nil,
        "a call returned immediately must inline into the return")
    check(not generated:find("%u+32_t v%d+ = s%d+%.f_"),
        "a record arm must store its construction, not read its fields back")
end

-- An array is materialised on demand too: a read-only by-value parameter reads the C parameter
-- directly, a nested literal builds one Make instead of spilling and copying each inner array, and a
-- conditional whose arms agree on one known value needs neither a join slot nor an `If`.
do
    local source = "let sum2(a: array(u32, 2)): u32 = a[0] + a[1]\n"
        .. "let agree(c: bool): u32 = if c then 7 else 7\n"
        .. "let nested(): u32 = do\n  let a = [1, 2]\n  let c = [a, a]\n"
        .. "  return c[0][0] + c[1][1]\nend\n"
        .. "return { functions = { sum2, agree, nested } }"
    local generated = wordlet.compile{ source = source, name = "arraysclean.let" }:unit()
    check(not generated:find("wordletarray_1 s%d+ = v1;"),
        "a read-only array parameter must not copy the parameter")
    check(generated:find("v1.f_data[UINT32_C(0)]", 1, true) ~= nil,
        "a read-only array parameter indexes the parameter directly")
    check(generated:find("wordlet_agree(bool v1) {\n    return UINT32_C(7);", 1, true) ~= nil,
        "a conditional whose arms agree folds to the value")
    check(not generated:find("wordletarray_1 v%d+ = s%d+;"),
        "a nested array literal must not copy an inner array out of storage")
end

-- A captured local array is a mutable instance, so the closure borrows it as a place rather than
-- taking a by-value copy. A mutation through the closure is therefore visible afterward.
do
    local source = "let f(): u32 = do\n  let a = [1, 2, 3]\n"
        .. "  let g = |i: u32| -> do a[i] = 9 return a[i] end\n"
        .. "  let x = g(0)\n  return x * 100 + a[0]\nend\n"
        .. "return { functions = { f } }"
    local generated = wordlet.compile{ source = source, name = "borrowarray.let" }:unit()
    check(generated:find("wordletarray_1 *s", 1, true) ~= nil,
        "a captured array is borrowed as a place, not passed by value")
    local path = directory .. "/borrowarray.c"
    write(path, generated .. "\n#include <assert.h>\n"
        .. "int main(void) { assert(wordlet_f() == UINT32_C(909)); return 0; }\n")
    local exe = directory .. "/borrowarray"
    check(shell("timeout --kill-after=2s 30s " .. CC .. " -std=c11 -Wall -Wextra -Werror -O2 -o '"
        .. exe .. "' '" .. path .. "' 2> " .. directory .. "/borrowerr.txt") == 0,
        "borrowed array capture C failed to compile:\n" .. read(directory .. "/borrowerr.txt"))
    check(shell("timeout --kill-after=2s 10s '" .. exe .. "'") == 0,
        "a captured array must be borrowed, so its mutation is visible")
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
