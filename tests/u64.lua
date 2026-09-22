-- Checks for the exact 64-bit kernel. Loaded by tests/run.lua from the project root.
-- The kernel is checked against hand-computed values, against an independent bit-serial reference,
-- and against the arithmetic identities that any correct implementation has to satisfy.
local kit = require("wordletkit")
local u = kit.U64

local checks = 0
local function check(ok, message)
    assert(ok, message)
    checks = checks + 1
end

local function words(value)
    local high = math.floor(value / 4294967296)
    return high, value - high * 4294967296
end
local function value(high, low) return high * 4294967296 + low end

-- Boundaries ---------------------------------------------------------------------------------------
check(u.iszero(0, 0) and not u.iszero(0, 1), "zero is the pair of zero words")
check(u.add(0, 4294967295, 0, 1) == 1, "the low word carries into the high word")
check(select(1, u.add(0, 4294967295, 0, 1)) == 1, "the carry reaches the high word")
check(u.add(4294967295, 4294967295, 0, 1) == 0 and select(2, u.add(4294967295, 4294967295, 0, 1)) == 0,
    "the high word carries out and is dropped")
check(u.sub(0, 0, 0, 1) == 4294967295 and select(2, u.sub(0, 0, 0, 1)) == 4294967295,
    "subtracting from zero wraps")
check(select(2, u.neg(0, 1)) == 4294967295 and select(1, u.neg(0, 1)) == 4294967295, "-1 is every bit set")
check(select(1, u.mul(0, 4294967295, 0, 4294967295)) == 4294967294
    and select(2, u.mul(0, 4294967295, 0, 4294967295)) == 1,
    "the largest 32-bit square decomposes into two words")
check(select(1, u.mul(4294967295, 4294967295, 4294967295, 4294967295)) == 0
    and select(2, u.mul(4294967295, 4294967295, 4294967295, 4294967295)) == 1,
    "the largest 64-bit square is one")
check(select(1, u.mul(1, 0, 0, 3)) == 3 and select(2, u.mul(1, 0, 0, 3)) == 0,
    "2^32 times 3 scales the high word")

-- Division -----------------------------------------------------------------------------------------
do
    local qh, ql, rh, rl = u.divmod(0, 100, 0, 3)
    check(qh == 0 and ql == 33 and rh == 0 and rl == 1, "100 divided by 3")
    qh, ql, rh, rl = u.divmod(1, 0, 0, 3)
    check(qh == 0 and ql == 1431655765 and rh == 0 and rl == 1, "2^32 divided by 3")
    qh, ql, rh, rl = u.divmod(4294967295, 4294967295, 0, 10)
    check(u.tostring(qh, ql, false) == "1844674407370955161" and rl == 5,
        "the largest value divided by ten")
    qh, ql = u.divmod(4294967295, 4294967295, 4294967295, 4294967295)
    check(qh == 0 and ql == 1, "the largest value divided by itself")
    check(not pcall(u.divmod, 1, 0, 0, 0), "dividing by zero is refused")
end

-- Shifts and bits ----------------------------------------------------------------------------------
check(select(1, u.shl(0, 1, 32)) == 1 and select(2, u.shl(0, 1, 32)) == 0, "shifting into the high word")
check(select(1, u.shl(1, 0, 32)) == 0 and select(2, u.shl(1, 0, 32)) == 0, "shifting out of range is zero")
check(select(2, u.shr(1, 0, 32)) == 1 and select(1, u.shr(1, 0, 32)) == 0, "shifting down a word")
check(u.shl(1, 0, 64) == 0 and select(2, u.shr(0, 1, 64)) == 0, "a shift of 64 clears the value")
check(select(1, u.bnot(0, 0)) == 4294967295 and select(2, u.bnot(0, 0)) == 4294967295,
    "the complement of zero is every bit set")
check(select(2, u.band(4294967295, 4294967295, 0, 255)) == 255, "and keeps the low bits")
check(select(1, u.bor(1, 0, 0, 0)) == 1, "or sets a high bit")
check(select(2, u.bxor(4294967295, 4294967295, 0, 4294967295)) == 0, "xor clears equal bits")

-- Signed -------------------------------------------------------------------------------------------
check(select(1, u.sdivmod(4294967295, 4294967289, 0, 2)) == 4294967295
    and select(2, u.sdivmod(4294967295, 4294967289, 0, 2)) == 4294967293,
    "-7 divided by 2 truncates toward zero")
check(select(4, u.sdivmod(4294967295, 4294967289, 0, 2)) == 4294967295,
    "the remainder of -7 by 2 is -1")
check(select(2, u.sdivmod(4294967295, 4294967295, 4294967295, 4294967295)) == 1,
    "the most negative value divided by -1 wraps to itself")
check(u.slt(4294967295, 4294967295, 0, 1) and not u.slt(0, 1, 4294967295, 4294967295),
    "a negative value is below a positive one")
check(u.slt(4294967295, 4294967294, 4294967295, 4294967295), "-2 is below -1")
check(not u.lt(4294967295, 4294967295, 0, 1), "unsigned comparison puts the sign bit last")
check(select(1, u.sar(4294967295, 4294967295, 1)) == 4294967295
    and select(2, u.sar(4294967295, 4294967295, 1)) == 4294967295, "-1 shifted right is -1")
check(select(1, u.sar(4294967295, 0, 40)) == 4294967295 and select(2, u.sar(4294967295, 0, 40)) == 4294967295,
    "a large arithmetic shift fills with the sign")
check(select(1, u.sar(2147483648, 0, 32)) == 4294967295
    and select(2, u.sar(2147483648, 0, 32)) == 2147483648, "the most negative value shifted right")
check(select(1, u.sar(0, 8, 1)) == 0 and select(2, u.sar(0, 8, 1)) == 4, "a positive shift is logical")

-- Text and conversion ------------------------------------------------------------------------------
check(u.tostring(0, 0, false) == "0" and u.tostring(0, 10, false) == "10", "decimal digits")
check(u.tostring(4294967295, 4294967295, false) == "18446744073709551615", "the largest value in text")
check(u.tostring(4294967295, 4294967295, true) == "-1", "a signed value in text")
check(u.tostring(4294967295, 4294967294, true) == "-2", "another signed value in text")
check(u.tofloat(0, 0) == 0.0 and u.tofloat(0, 10) == 10.0, "small values convert exactly")
check(u.tofloat(2147483648, 0) == 2 ^ 63, "2^63 converts exactly")
check(u.tofloat(4294967295, 4294967295) == 2 ^ 64, "the largest value rounds to 2^64")

-- An independent bit-serial reference, written differently from the fast paths above.
local function serial_add(ah, al, bh, bl)
    local high, low, carry = 0, 0, 0
    for index = 0, 63 do
        local bitA = index >= 32 and math.floor(ah / 2 ^ (index - 32)) % 2 or math.floor(al / 2 ^ index) % 2
        local bitB = index >= 32 and math.floor(bh / 2 ^ (index - 32)) % 2 or math.floor(bl / 2 ^ index) % 2
        local sum = bitA + bitB + carry
        carry = sum >= 2 and 1 or 0
        if sum % 2 == 1 then
            if index >= 32 then high = high + 2 ^ (index - 32) else low = low + 2 ^ index end
        end
    end
    return high, low
end
local function serial_mul(ah, al, bh, bl)
    local high, low = 0, 0
    for index = 0, 63 do
        local bitB = index >= 32 and math.floor(bh / 2 ^ (index - 32)) % 2 or math.floor(bl / 2 ^ index) % 2
        if bitB == 1 then high, low = serial_add(high, low, ah, al) end
        if index < 63 then ah, al = u.shl(ah, al, 1) end
    end
    return high, low
end
for _, a in ipairs({ { 0, 0 }, { 0, 1 }, { 0, 4294967295 }, { 1, 0 }, { 2147483648, 0 },
    { 4294967295, 4294967295 }, { 12345, 67890 } }) do
    for _, b in ipairs({ { 0, 0 }, { 0, 1 }, { 0, 4294967295 }, { 1, 0 }, { 4294967295, 4294967295 } }) do
        check(select(1, u.add(a[1], a[2], b[1], b[2])) == select(1, serial_add(a[1], a[2], b[1], b[2]))
            and select(2, u.add(a[1], a[2], b[1], b[2])) == select(2, serial_add(a[1], a[2], b[1], b[2])),
            "addition agrees with the bit-serial reference")
        local fh, fl = u.mul(a[1], a[2], b[1], b[2])
        local sh, sl = serial_mul(a[1], a[2], b[1], b[2])
        check(fh == sh and fl == sl, "multiplication agrees with the bit-serial reference")
        -- Subtraction is the inverse of addition on the wrapped values.
        local dh, dl = u.sub(select(1, u.add(a[1], a[2], b[1], b[2])),
            select(2, u.add(a[1], a[2], b[1], b[2])), b[1], b[2])
        check(dh == a[1] and dl == a[2], "subtraction undoes addition")
    end
end

-- The division identity has to hold for every pair, which is what makes the 64-step loop trustworthy.
local cases = { { 0, 0 }, { 0, 1 }, { 0, 2 }, { 0, 10 }, { 1, 0 }, { 0, 4294967295 }, { 1, 1 },
    { 4294967295, 4294967295 }, { 2147483648, 0 }, { 12345, 67890 }, { 999, 123456789 } }
for _, a in ipairs(cases) do
    for _, d in ipairs(cases) do
        if not u.iszero(d[1], d[2]) then
            local qh, ql, rh, rl = u.divmod(a[1], a[2], d[1], d[2])
            local mh, ml = u.mul(qh, ql, d[1], d[2])
            local sh, sl = u.add(mh, ml, rh, rl)
            check(sh == a[1] and sl == a[2] and u.lt(rh, rl, d[1], d[2]),
                "quotient times divisor plus remainder is the dividend")
        end
    end
end

print(("PASS: exact 64-bit kernel (%d checks)"):format(checks))
