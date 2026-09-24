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
local here = source:match("^(.*[/])") or "./"
dofile(here .. "schemas.lua")
dofile(here .. "machine.lua")
dofile(here .. "walk.lua")
dofile(here .. "u64.lua")
dofile(here .. "parse.lua")
dofile(here .. "eval.lua")
dofile(here .. "c.lua")
dofile(here .. "sha256.lua")
dofile(here .. "jit.lua")

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
        "README.md", "AGENTS.md", "architecture.md", "syntax.md", "GUIDE.md", "interfaces.md", "ast.asdl", "ir.asdl",
        "ASDL.md", "U32.md", "U64.md", "THIRD_PARTY.md", "VALIDATION.md", "LICENSE", ".gitignore"}) do        command("cp -R -- " .. q(root .. path) .. " " .. q(project .. "/"))
    end
    local bundle = project .. "/dist/wordlet.lua"
    command("cd " .. q(temp) .. " && timeout 10s " .. lua .. " " .. q(project .. "/tools/bundle.lua"))
    local first = read(bundle)
    command("cd " .. q(temp) .. " && timeout 10s " .. lua .. " " .. q(project .. "/tools/bundle.lua"))
    assert(first == read(bundle), "bundle must be deterministic")
    assert(first:find("MIT License", 1, true) and first:find("Stanford University", 1, true),
        "bundle must embed the project and vendored license notices")
    assert(first:find("Wordlet syntax and semantic contract, bundled from syntax.md", 1, true),
        "bundle must embed the syntax document")
    assert(first:find("Wordlet design and naming guide, bundled from GUIDE.md", 1, true),
        "bundle must embed the design guide")
    assert(first:find("Wordlet syntax and semantic contract", 1, true) < first:find("local host_require", 1, true),
        "the syntax document must lead the generated file")
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
            'the bundle must carry the syntax reference');
        assert(type(w.guide)=='string' and w.guide:find('Wordlet',1,true)~=nil,
            'the bundle must carry the design guide')]])
    -- Real require mode from a different cwd, with no source search path.
    run([[package.path='./?.lua'; package.cpath=''; local w=require('isolated');
        assert(type(w.compile)=='function' and type(w.interpret)=='function');
        assert(type(w.syntax)=='string' and w.syntax:find('Wordlet',1,true)~=nil);
        assert(type(w.guide)=='string' and w.guide:find('Wordlet',1,true)~=nil)]])
end, debug.traceback)
command("rm -rf -- " .. q(temp))
if not ok then error(err, 0) end
print("PASS: isolated relocation, deterministic bundle and embedding")
