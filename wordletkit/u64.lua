-- Exact U64/I64 operations over a pair of 32-bit words. No compiler, global patches or VM hooks.
--
-- A LuaJIT number is a double, so it holds every 32-bit word exactly but not a 64-bit value. Every
-- operation here therefore works on the two words and uses only sums and products that a double
-- represents exactly, which the 16-bit limb decomposition below makes sure of. Unsigned arithmetic
-- wraps at 64 bits, and the signed operations are two's complement with C's division rule: the
-- quotient is truncated toward zero and the remainder takes the dividend's sign.
local bit = require("bit")
local M = {}

local WORD = 4294967296      -- 2^32
local LIMB = 65536           -- 2^16
local LAST = 4294967295      -- 2^32 - 1
local SIGN = 2147483648      -- the sign bit of a word

local function word(x)
    assert(type(x) == "number" and x >= 0 and x < WORD and x == math.floor(x), "expected a 32-bit word")
    return x
end

local function pair(ah, al) return word(ah), word(al) end
local function normal(x) return x % WORD end

M.check = word
M.iszero = function(ah, al) return ah == 0 and al == 0 end
function M.eq(ah, al, bh, bl)
    ah, al = pair(ah, al); bh, bl = pair(bh, bl)
    return ah == bh and al == bl
end
function M.lt(ah, al, bh, bl)
    ah, al = pair(ah, al); bh, bl = pair(bh, bl)
    return ah < bh or (ah == bh and al < bl)
end
function M.le(ah, al, bh, bl)
    ah, al = pair(ah, al); bh, bl = pair(bh, bl)
    return ah < bh or (ah == bh and al <= bl)
end

function M.add(ah, al, bh, bl)
    ah, al = pair(ah, al); bh, bl = pair(bh, bl)
    local low = al + bl
    return normal(ah + bh + math.floor(low / WORD)), normal(low)
end

function M.sub(ah, al, bh, bl)
    ah, al = pair(ah, al); bh, bl = pair(bh, bl)
    return normal(ah - bh - (al < bl and 1 or 0)), normal(al - bl)
end

function M.neg(ah, al) return M.sub(0, 0, ah, al) end

-- The exact 32x32 product as a low word and a high word. Each operand is split into 16-bit limbs, so
-- every partial product and sum stays far below 2^53 and is therefore exact.
local function mul32(a, b)
    local a0, a1 = a % LIMB, math.floor(a / LIMB)
    local b0, b1 = b % LIMB, math.floor(b / LIMB)
    -- a*b = t0 + t1*2^16 + t2*2^32, so the low two words are a carry chain over those three terms.
    local t0 = a0 * b0
    local t1 = a0 * b1 + a1 * b0
    local t2 = a1 * b1
    local assembled = t0 + (t1 % LIMB) * LIMB
    local carry = math.floor(assembled / WORD)
    return assembled % WORD, (t2 + math.floor(t1 / LIMB) + carry) % WORD
end

function M.mul(ah, al, bh, bl)
    ah, al = pair(ah, al); bh, bl = pair(bh, bl)
    -- (ah*2^32 + al)(bh*2^32 + bl) modulo 2^64 is (ah*bl + al*bh) * 2^32 + al*bl, because the
    -- ah*bh term is 2^64. Only the low words of the cross products reach the high word.
    local low, alBlHigh = mul32(al, bl)
    local ahBlLow = mul32(ah, bl)
    local alBhLow = mul32(al, bh)
    return normal(alBlHigh + ahBlLow + alBhLow), low
end

function M.shl(ah, al, amount)
    ah, al = pair(ah, al)
    if amount <= 0 then return ah, al end
    if amount >= 64 then return 0, 0 end
    if amount >= 32 then return normal(al * 2 ^ (amount - 32)), 0 end
    return normal(ah * 2 ^ amount + math.floor(al / 2 ^ (32 - amount))), normal(al * 2 ^ amount)
end

function M.shr(ah, al, amount)
    ah, al = pair(ah, al)
    if amount <= 0 then return ah, al end
    if amount >= 64 then return 0, 0 end
    if amount >= 32 then return 0, math.floor(ah / 2 ^ (amount - 32)) end
    return math.floor(ah / 2 ^ amount), math.floor(al / 2 ^ amount) + (ah % 2 ^ amount) * 2 ^ (32 - amount)
end

-- An arithmetic shift right keeps the sign: the vacated bits become the sign bit.
function M.sar(ah, al, amount)
    ah, al = pair(ah, al)
    if amount <= 0 then return ah, al end
    local negative = ah >= SIGN
    if amount >= 64 then return negative and LAST or 0, negative and LAST or 0 end
    local high, low = M.shr(ah, al, amount)
    if not negative then return high, low end
    if amount >= 32 then
        -- Every bit of the high word is now sign, and the bits the low word kept are its top ones.
        return LAST, normal(low + (2 ^ (amount - 32) - 1) * 2 ^ (64 - amount))
    end
    -- The bits shifted into the low word came from the high word, which is already the sign, so
    -- only the high word needs filling.
    return normal(high + (2 ^ amount - 1) * 2 ^ (32 - amount)), low
end

function M.band(ah, al, bh, bl)
    ah, al = pair(ah, al); bh, bl = pair(bh, bl)
    return normal(bit.band(ah, bh)), normal(bit.band(al, bl))
end
function M.bor(ah, al, bh, bl)
    ah, al = pair(ah, al); bh, bl = pair(bh, bl)
    return normal(bit.bor(ah, bh)), normal(bit.bor(al, bl))
end
function M.bxor(ah, al, bh, bl)
    ah, al = pair(ah, al); bh, bl = pair(bh, bl)
    return normal(bit.bxor(ah, bh)), normal(bit.bxor(al, bl))
end
function M.bnot(ah, al)
    ah, al = pair(ah, al)
    return normal(bit.bnot(ah)), normal(bit.bnot(al))
end

-- A restoring division: 64 steps, each shifting the remainder and subtracting when the divisor fits.
-- The bit shifted out of the high word is kept, because with a large divisor the shifted remainder can
-- exceed 64 bits, and in that case it is certainly at least the divisor.
function M.divmod(ah, al, bh, bl)
    ah, al = pair(ah, al); bh, bl = pair(bh, bl)
    assert(not (bh == 0 and bl == 0), "division-zero")
    local qh, ql, rh, rl = 0, 0, 0, 0
    for step = 63, 0, -1 do
        local carry = rh >= SIGN and 1 or 0
        rh, rl = M.shl(rh, rl, 1)
        if step >= 32 then
            if math.floor(ah / 2 ^ (step - 32)) % 2 == 1 then rl = rl + 1 end
        else
            if math.floor(al / 2 ^ step) % 2 == 1 then rl = rl + 1 end
        end
        if carry == 1 or not M.lt(rh, rl, bh, bl) then
            rh, rl = M.sub(rh, rl, bh, bl)
            if step >= 32 then qh = normal(qh + 2 ^ (step - 32)) else ql = normal(ql + 2 ^ step) end
        end
    end
    return qh, ql, rh, rl
end

function M.pow(ah, al, eh, el)
    ah, al = pair(ah, al); eh, el = pair(eh, el)
    local rh, rl = 1, 0
    while not M.iszero(eh, el) do
        if el % 2 == 1 then rh, rl = M.mul(rh, rl, ah, al) end
        eh, el = M.shr(eh, el, 1)
        if not M.iszero(eh, el) then ah, al = M.mul(ah, al, ah, al) end
    end
    return rh, rl
end

-- Signed operations, on the same words read as two's complement.
function M.spositive(ah, al) return word(ah) < SIGN end
function M.sneg(ah, al) return M.neg(ah, al) end

function M.slt(ah, al, bh, bl)
    ah, al = pair(ah, al); bh, bl = pair(bh, bl)
    local negativeA, negativeB = ah >= SIGN, bh >= SIGN
    if negativeA ~= negativeB then return negativeA end
    return M.lt(ah, al, bh, bl)
end

function M.sle(ah, al, bh, bl)
    ah, al = pair(ah, al); bh, bl = pair(bh, bl)
    local negativeA, negativeB = ah >= SIGN, bh >= SIGN
    if negativeA ~= negativeB then return negativeA end
    return M.le(ah, al, bh, bl)
end

-- C's rule, with the one case C leaves undefined defined here: the most negative value divided by -1
-- wraps to itself, which is what dividing the magnitudes gives.
function M.sdivmod(ah, al, bh, bl)
    ah, al = pair(ah, al); bh, bl = pair(bh, bl)
    local negativeA, negativeB = ah >= SIGN, bh >= SIGN
    local magAh, magAl, magBh, magBl = ah, al, bh, bl
    if negativeA then magAh, magAl = M.neg(ah, al) end
    if negativeB then magBh, magBl = M.neg(bh, bl) end
    local qh, ql, rh, rl = M.divmod(magAh, magAl, magBh, magBl)
    if negativeA ~= negativeB then qh, ql = M.neg(qh, ql) end
    if negativeA then rh, rl = M.neg(rh, rl) end
    return qh, ql, rh, rl
end

local function decimal(ah, al)
    if M.iszero(ah, al) then return "0" end
    local digits, rh, rl = {}, ah, al
    while not M.iszero(rh, rl) do
        local qh, ql, _, remainder = M.divmod(rh, rl, 0, 10)
        digits[#digits + 1] = string.char(48 + remainder)
        rh, rl = qh, ql
    end
    local out = {}
    for index = #digits, 1, -1 do out[#out + 1] = digits[index] end
    return table.concat(out)
end

function M.tostring(ah, al, isSigned)
    ah, al = pair(ah, al)
    if isSigned and ah >= SIGN then return "-" .. decimal(M.neg(ah, al)) end
    return decimal(ah, al)
end

-- The nearest double, rounding once: the leading bit gives the exponent, the top 53 bits give the
-- significand, and the bits below them decide the rounding, ties going to even.
function M.tofloat(ah, al)
    ah, al = pair(ah, al)
    if M.iszero(ah, al) then return 0.0 end
    local top
    for step = 63, 0, -1 do
        local isSet = step >= 32 and math.floor(ah / 2 ^ (step - 32)) % 2 == 1
            or step < 32 and math.floor(al / 2 ^ step) % 2 == 1
        if isSet then top = step break end
    end
    -- A value below 2^53 is an exact double, and above it the shift is at most 11 bits, so the
    -- discarded bits all live in the low word.
    if top <= 52 then return ah * WORD + al end
    local shift = top - 52
    local high, low = M.shr(ah, al, shift)
    local result = (high * WORD + low) * 2 ^ shift
    local remainder = al % 2 ^ shift
    local half = 2 ^ (shift - 1)
    if remainder > half or (remainder == half and low % 2 == 1) then result = result + 2 ^ shift end
    return result
end

-- Reads a decimal or hexadecimal literal, with or without the `0x`, into two words. A literal that
-- would need more than 64 bits is refused rather than wrapped, which is what a source literal needs.
function M.fromstring(text)
    local digits, base = text, 10
    if digits:lower():sub(1, 2) == "0x" then digits, base = digits:sub(3), 16 end
    if #digits == 0 then return nil end
    local high, low = 0, 0
    for index = 1, #digits do
        local digit = tonumber(digits:sub(index, index), base)
        if not digit then return nil end
        -- (high:low) * base + digit, refusing a result that would need a 65th bit.
        local product, productHigh = mul32(low, base)
        local scaled, scaledHigh = mul32(high, base)
        if scaledHigh ~= 0 then return nil end
        local newLow = product + digit
        local newHigh = scaled + productHigh + math.floor(newLow / WORD)
        if newHigh >= WORD then return nil end
        high, low = newHigh, newLow % WORD
    end
    return high, low
end

return M
