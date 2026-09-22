-- The LuaJIT FFI front end: compile `.let` code with the C backend, build it with the system compiler,
-- and load it, so the exported words are callable Lua functions. Needs a C11 compiler through `CC`.
local source = debug.getinfo(1, "S").source:sub(2)
local here = source:match("^(.*[/\\])") or "./"
package.path = here .. "../?.lua;" .. here .. "../?/init.lua;" .. package.path

local ffi = require("ffi")
local let = require("wordlet.jit")

local checks = 0
local function check(ok, message) assert(ok, message); checks = checks + 1 end

-- `loadstring`: compile a `.let` string and call its exported words.
local app = let.loadstring[[
let add(a, b: U32): U32 = a + b
let main(): U32 = add(20, 22)
return { functions = { add, main } }
]]
check(app.add(2, 3) == 5, "loadstring exports are callable")
check(app.main() == 42, "an exported main is callable")

-- An implicit `main` needs no export configuration.
check(let.run[[
let double(x: U32): U32 = x * 2
let main(): U32 = double(21)
]] == 42, "run calls an implicit main")

-- `loadfile` resolves the module's own `use` imports next to it.
local modules = let.loadfile(here .. "../examples/modules.let")
check(modules.twice(4) == 8, "loadfile resolves a use import")
check(modules.bumped(4) == 9, "a used module's private name stays private")

-- Several artifacts coexist: each export is namespaced and its types are declared separately.
local one = let.loadstring[[let f(): U32 = 1
return { functions = { f } }]]
local two = let.loadstring[[let f(): U32 = 2
return { functions = { f } }]]
check(one.f() == 1 and two.f() == 2, "two artifacts load side by side")

-- A record crosses the boundary as its C layout.
local point = let.loadstring[[
let P = { x: U32, y: U32 }
let make(x, y: U32): P = P { x = x, y = y }
return { types = { P }, functions = { make } }
]]
local p = point.make(3, 4)
check(p.f_x == 3 and p.f_y == 4, "a record crosses the FFI boundary")

-- The searcher is what `require` uses; test it directly rather than mutating package.loaders.
let.path = here .. "../examples/?.let"
check(let.resolve("arithmetic") ~= nil, "resolve finds a .let module")
local loader = let.searcher("arithmetic")
check(type(loader) == "function", "the searcher returns a loader")
check(loader().transform(5) == 23, "the loader returns the module's exports")
check(type(let.searcher("no_such_module")) == "string", "a missing module reports no match")

-- A source rejection is a Wordlet diagnostic, not a C error.
check(not pcall(let.loadstring, "let f(x: U32): U32 = y\nreturn { functions = { f } }"),
    "a source rejection surfaces")

print(("PASS: LuaJIT FFI front end (%d checks)"):format(checks))
