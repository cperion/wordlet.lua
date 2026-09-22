-- SHA-256 acceptance test: a real program with an external ground truth.
--
-- The reference interpreter and the generated C must both reproduce the published NIST vector for the
-- one-block message "abc", and must agree with each other for runtime-seeded blocks. The C is compiled
-- under `-Wall -Wextra -Werror -O2`, so the emitted code is also checked for unused locals and params.
local source = debug.getinfo(1, "S").source:sub(2)
local here = source:match("^(.*[/\\])") or "./"
package.path = here .. "../?.lua;" .. here .. "../?/init.lua;" .. package.path

local wordlet = require("wordlet")
local C = require("wordlet.cabi")

local checks = 0
local function check(ok, message) assert(ok, message) checks = checks + 1 end

local CC = os.getenv("CC") or "cc"
local timeout = os.getenv("WORDLET_TIMEOUT") or "20s"
local directory = os.tmpname()
os.remove(directory)
assert(os.execute("mkdir -p -- '" .. directory .. "'") ~= nil)

local function write(path, text)
    local file = assert(io.open(path, "wb")); assert(file:write(text)); assert(file:close())
end
local function read(path)
    local file = assert(io.open(path, "rb")); local text = assert(file:read("*a")); assert(file:close()); return text
end
-- LuaJIT follows Lua 5.1: os.execute returns the raw status, so success is 0 rather than true.
local function shell(command)
    local first, how = os.execute(command)
    if first == true or first == 0 then return 0 end
    if first == nil then return how end
    return first
end
local function cField(name) return "f_" .. C.escape(name) end

local program = here .. "../examples/sha256.let"
local text = read(program)

-- The published digest of "abc", one word per state component.
local EXPECTED = { 0xba7816bf, 0x8f01cfea, 0x414140de, 0x5dae2223,
                   0xb00361a3, 0x96177a9c, 0xb410ff61, 0xf20015ad }
local FIELDS = { "a", "b", "c", "d", "e", "f", "g", "h" }

-- 1. The reference interpreter reproduces the published vector.
local digest = wordlet.interpret{ source = text, name = "sha256.let", entry = "abc", args = {} }[1]
for index, want in ipairs(EXPECTED) do
    check(digest[FIELDS[index]] == want, "abc() component " .. FIELDS[index])
end

-- 2. The generated C reproduces the vector and agrees with the interpreter on runtime-seeded blocks.
local seeds = { 0, 1, 0xFFFFFFFF, 0x12345678 }
local artifact = wordlet.compile_file(program)
local unit = artifact:unit()
local abcName = C.functionName("abc")
local seedName = C.functionName("digest_seed")
local abcType = unit:match("([%a_][%w_]*)%s+" .. abcName .. "%s*%(")
local seedType = unit:match("([%a_][%w_]*)%s+" .. seedName .. "%s*%(")
check(abcType ~= nil, "cannot find the C result type of abc")
check(seedType ~= nil, "cannot find the C result type of digest_seed")

local assertion = {}
assertion[#assertion + 1] = "    { " .. abcType .. " r = " .. abcName .. "();"
for index, want in ipairs(EXPECTED) do
    assertion[#assertion + 1] = "      assert(r." .. cField(FIELDS[index]) .. " == UINT32_C(" .. want .. "));"
end
assertion[#assertion + 1] = "    }"
for _, seed in ipairs(seeds) do
    local got = wordlet.interpret{ source = text, name = "sha256.let", entry = "digest_seed", args = { seed } }[1]
    assertion[#assertion + 1] = "    { " .. seedType .. " r = " .. seedName .. "(UINT32_C(" .. seed .. "));"
    for _, field in ipairs(FIELDS) do
        assertion[#assertion + 1] = "      assert(r." .. cField(field) .. " == UINT32_C(" .. got[field] .. "));"
    end
    assertion[#assertion + 1] = "    }"
end

local main = { "#include <assert.h>", "#include <stdint.h>", "#include <stdbool.h>", "", unit, "",
    "int main(void) {" }
-- Module-level storage is initialised by an explicit host call, not implicitly.
if unit:find("void wordlet_init(void)", 1, true) then main[#main + 1] = "    wordlet_init();" end
for _, line in ipairs(assertion) do main[#main + 1] = line end
main[#main + 1] = "    return 0;"
main[#main + 1] = "}"
write(directory .. "/sha256.c", table.concat(main, "\n"))

local exe = directory .. "/sha256"
local flags = "-std=c11 -Wall -Wextra -Werror -O2"
local compile = ("timeout --kill-after=2s %s %s %s -o '%s' '%s'"):format(timeout, CC, flags, exe, directory .. "/sha256.c")
local status = shell(compile .. " 2> " .. directory .. "/err.txt")
check(status == 0, "C compilation failed for sha256:\n" .. read(directory .. "/err.txt"))
check(shell("timeout --kill-after=2s 10s '" .. exe .. "'") == 0,
    "generated SHA-256 failed its assertions")
shell("rm -rf -- '" .. directory .. "'")

print(("PASS: SHA-256 real-program acceptance (%d checks: NIST vector and %d runtime seeds)")
    :format(checks, #seeds))
