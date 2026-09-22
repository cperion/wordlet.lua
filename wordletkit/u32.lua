-- Concrete/reference U32 operations. No compiler, global patches or VM hooks.
local bit = require("bit")
local M = {}
local MOD, LIMB = 4294967296, 65536
local function uint(x)
    assert(type(x) == "number" and x >= 0 and x < MOD and x == math.floor(x), "expected U32")
    return x
end
local function unsigned(x) return x < 0 and x + MOD or x end
local function pair(a, b) return uint(a), uint(b) end
M.check = uint
function M.add(a, b) a,b=pair(a,b); return (a+b)%MOD end
function M.sub(a, b) a,b=pair(a,b); return (a-b)%MOD end
function M.neg(a) return (-uint(a))%MOD end
function M.mul(a, b)
    a,b=pair(a,b)
    local al, bl = a%LIMB, b%LIMB
    local cross = (math.floor(a/LIMB)*bl + al*math.floor(b/LIMB))%LIMB
    return (al*bl + cross*LIMB)%MOD
end
function M.div(a, b) a,b=pair(a,b); assert(b~=0, "division-zero"); return math.floor(a/b) end
function M.mod(a, b) a,b=pair(a,b); assert(b~=0, "division-zero"); return a%b end
function M.pow(a, b)
    a,b=pair(a,b)
    local result = 1
    while b > 0 do
        if b%2 == 1 then result=M.mul(result,a) end
        b=math.floor(b/2)
        if b > 0 then a=M.mul(a,a) end
    end
    return result
end
function M.band(a,b) a,b=pair(a,b); return unsigned(bit.band(a,b)) end
function M.bor(a,b) a,b=pair(a,b); return unsigned(bit.bor(a,b)) end
function M.bxor(a,b) a,b=pair(a,b); return unsigned(bit.bxor(a,b)) end
function M.bnot(a) return unsigned(bit.bnot(uint(a))) end
function M.shl(a,b) a,b=pair(a,b); return b>=32 and 0 or unsigned(bit.lshift(a,b)) end
function M.shr(a,b) a,b=pair(a,b); return b>=32 and 0 or unsigned(bit.rshift(a,b)) end
return M
