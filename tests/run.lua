-- Standalone bootstrap checks. Requires LuaJIT and POSIX cp/mkdir/timeout.
local source = debug.getinfo(1, "S").source:sub(2)
local root = (source:match("^(.*[/])") or "./") .. "../"
package.path = root .. "?.lua;" .. package.path
local function q(s) return "'" .. s:gsub("'", "'\\''") .. "'" end
local function read(path)
    local f = assert(io.open(path, "rb")); local s = assert(f:read("*a")); assert(f:close()); return s
end
local function write(path, text)
    local f = assert(io.open(path, "wb")); assert(f:write(text)); assert(f:close())
end
local function command(cmd, success)
    local result = os.execute(cmd)
    assert((result == 0 or result == true) == (success ~= false), cmd .. " (status " .. tostring(result) .. ")")
end
local kit = require("wordletkit")
local here = source:match("^(.*[/])") or "./"
dofile(here .. "schemas.lua")
dofile(here .. "u64.lua")
dofile(here .. "parse.lua")
dofile(here .. "eval.lua")
dofile(here .. "c.lua")
dofile(here .. "sha256.lua")
dofile(here .. "jit.lua")
local L, c = kit.List, kit.ASDL.NewContext()
c:Define([[
module T { Value = U32 | Bool
  Pair = (Value first, Value second) unique
  Node = Leaf(Value value) | Branch(Node left, Node right)
}
]])
assert(c.T.Pair(c.T.U32, c.T.Bool) == c.T.Pair(c.T.U32, c.T.Bool))
assert(c.T.Pair(c.T.U32, c.T.Bool) ~= c.T.Pair(c.T.Bool, c.T.U32))
assert(c.T.Leaf(c.T.U32) ~= c.T.Leaf(c.T.U32))
assert(not pcall(c.T.Pair, "U32", c.T.Bool))
assert(L{1, 2}:map("==", 1)[1] == true)
assert(L{1, 2}:map("~=", 1)[1] == false)
assert(L{1, 2}:map("~=", 1)[2] == true)
c.T.Leaf.probe = function() return "child" end
c.T.Node.probe = function() return "parent" end
assert(c.T.Leaf(c.T.U32):probe() == "parent")
assert(c.T.Pair.kind == nil and c.T.Leaf.kind == "Leaf")
local u = kit.U32
assert(u.add(4294967295,1)==0 and u.sub(0,1)==4294967295)
assert(u.mul(4294967295,4294967295)==1 and u.neg(1)==4294967295)
assert(u.pow(0,0)==1 and u.pow(2,32)==0)
assert(u.div(4294967295,3)==1431655765 and u.mod(4294967295,3)==0)
assert(u.bnot(0)==4294967295 and u.bxor(4294967295,4294967295)==0)
assert(u.shl(1,31)==2147483648 and u.shl(1,32)==0 and u.shr(4294967295,32)==0)
assert(u.shr(4294967295,1)==2147483647)
assert(not pcall(u.check,-1) and not pcall(u.check,1.5) and not pcall(u.check,4294967296))
assert(not pcall(u.div,1,0) and not pcall(u.mod,1,0))
local function serial_mul(a,b)
    local r=0
    for i=1,32 do
        if b%2==1 then r=(r+a)%4294967296 end
        a=(a+a)%4294967296; b=math.floor(b/2)
    end
    return r
end
for _,a in ipairs({0,1,65535,65536,2147483648,4294967295}) do
    for _,b in ipairs({0,1,3,65537,2147483647,4294967295}) do assert(u.mul(a,b)==serial_mul(a,b)) end
end

local temp = os.tmpname(); os.remove(temp)
command("mkdir -p -- " .. q(temp))
local lua = q(os.getenv("LUAJIT") or "luajit")
-- The generated ASDL schema and language-reference modules must match their sources.
command("cd " .. q(root) .. " && timeout 10s " .. lua .. " tools/embed.lua --check")
local function run(body)
    command("cd " .. q(temp) .. " && timeout 10s " .. lua .. " -e " .. q(body))
end
local ok, err = xpcall(function()
    -- Whitelist the standalone tree, not its enclosing checkout or future .git.
    command("mkdir -p -- " .. q(temp .. "/project with ' quote"))
    local project = temp .. "/project with ' quote"
    for _, path in ipairs({"vendor", "tools", "tests", "wordletkit", "wordlet", "examples", "wordletkit.lua", "bundle-manifest.lua",
        "README.md", "AGENTS.md", "architecture.md", "syntax.md", "interfaces.md", "ast.asdl", "ir.asdl",
        "ASDL.md", "U32.md", "U64.md", "THIRD_PARTY.md", "VALIDATION.md", "LICENSE", ".gitignore"}) do        command("cp -R -- " .. q(root .. path) .. " " .. q(project .. "/"))
    end
    local bundle = project .. "/dist/wordlet.lua"
    command("cd " .. q(temp) .. " && timeout 10s " .. lua .. " " .. q(project .. "/tools/bundle.lua"))
    local first = read(bundle)
    command("cd " .. q(temp) .. " && timeout 10s " .. lua .. " " .. q(project .. "/tools/bundle.lua"))
    assert(first == read(bundle), "bundle must be deterministic")
    assert(first:find("MIT License", 1, true) and first:find("Stanford University", 1, true),
        "bundle must embed the project and vendored license notices")
    write(temp .. "/isolated.lua", first)
    -- The shipped bundle is the compiler itself: compile and interpret a program with no source tree.
    local program = [==[let affine(a, b, x: U32) : U32 = a * x + b
return { functions = { affine } }]==]
    write(temp .. "/program.let", program)
    run([[package.path=''; package.cpath=''; local w=assert(loadfile('isolated.lua'))();
        local r=w.interpret{source=io.open('program.let'):read('*a'), entry='affine', args={3,7,4}};
        assert(r[1]==19); local c=w.compile_file('program.let'):unit();
        assert(c:find('wordlet_affine',1,true)~=nil);
        assert(type(w.syntax)=='string' and w.syntax:find('Wordlet',1,true)~=nil,
            'the bundle must carry the syntax reference')]])
    -- Real require mode from a different cwd, with no source search path.
    run([[package.path='./?.lua'; package.cpath=''; local w=require('isolated');
        assert(type(w.compile)=='function' and type(w.interpret)=='function');
        assert(type(w.syntax)=='string' and w.syntax:find('Wordlet',1,true)~=nil)]])

    write(temp .. "/entry.lua", [[return {legacy=require('legacy'), retry=function() return require('unstable') end,
        cycle=function() return require('cycle_a') end, missing=function() return require('unlisted') end}]])
    write(temp .. "/legacy.lua", [[package.loaded[...] = {answer=42}]])
    write(temp .. "/unstable.lua", [[_G.bootstrap_attempt=(_G.bootstrap_attempt or 0)+1
        if _G.bootstrap_attempt==1 then error('first attempt') end; return 42]])
    write(temp .. "/a.lua", [[return require('cycle_b')]])
    write(temp .. "/b.lua", [[return require('cycle_a')]])
    write(temp .. "/cli.lua", [[return function(api,args) assert(api.legacy.answer==42); io.write(args[1]); return 0 end]])
    write(temp .. "/manifest.lua", [[return {entry='entry', cli='cli', output='fixture.lua', modules={
        entry='entry.lua',legacy='legacy.lua',unstable='unstable.lua',cycle_a='a.lua',cycle_b='b.lua',cli='cli.lua'}}]])
    local builder = project .. "/tools/bundle.lua"
    command("cd " .. q(temp) .. " && timeout 10s " .. lua .. " " .. q(builder) .. " manifest.lua")
    run([[package.path=''; package.cpath=''; package.loaded.legacy={untouched=true};
        local a=assert(loadfile('fixture.lua'))(); assert(a.legacy.answer==42 and package.loaded.legacy.untouched);
        assert(not pcall(a.retry)); assert(a.retry()==42);
        for i=1,2 do local ok,e=pcall(a.cycle); assert(not ok and e:find('cyclic bundled require',1,true)) end;
        package.preload.unlisted=function() return 99 end;
        local ok,e=pcall(a.missing); assert(not ok and e:find('unlisted bundled dependency',1,true))]])
    command("cd " .. q(temp) .. " && timeout 10s " .. lua .. " fixture.lua CLI_OK > cli.out")
    assert(read(temp .. "/cli.out") == "CLI_OK")
    command("cd " .. q(temp) .. " && timeout 10s " .. lua .. " " .. q(builder) .. " manifest.lua /dev/null/out.lua > bad.out 2>&1", false)
    write(temp .. "/bad.lua", [[return {entry='missing',output='out.lua',modules={missing='absent.lua'}}]])
    command("cd " .. q(temp) .. " && timeout 10s " .. lua .. " " .. q(builder) .. " bad.lua > bad.out 2>&1", false)
    write(temp .. "/syntax.lua", "return (")
    write(temp .. "/bad.lua", [[return {entry='bad',output='out.lua',modules={bad='syntax.lua'}}]])
    command("cd " .. q(temp) .. " && timeout 10s " .. lua .. " " .. q(builder) .. " bad.lua > bad.out 2>&1", false)
end, debug.traceback)
command("rm -rf -- " .. q(temp))
if not ok then error(err, 0) end
print("PASS: ASDL/List/U32, isolated relocation, deterministic bundle, embedding, CLI, loader errors and write failures")
