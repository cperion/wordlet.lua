-- Lint the continuation protocol of `wordlet/eval.lua` (interfaces.md §4.3).
--
-- The protocol is easy to state and easy to violate silently, so it is checked rather than remembered:
-- a converted method answers with a *pair* through its continuation, in tail position. A bare
-- `return value` makes the driver treat the value as the next continuation, which fails far from the
-- line that caused it, and a method that never answers leaves the chain unfinished.
--
-- A method counts as converted when its parameter list has both `machine` and `k`.
--
-- Usage: luajit tools/cpslint.lua [path]
local path = arg[1] or "wordlet/eval.lua"
local text = io.open(path):read("*a")
if not text then print("cannot read " .. path); os.exit(1) end
local lines = {}
for line in (text .. "\n"):gmatch("(.-)\n") do lines[#lines + 1] = line end

local violations, converted = 0, 0
local function report(line, message)
    violations = violations + 1
    print(("%s:%d: %s"):format(path, line, message))
end

local index = 1
while index <= #lines do
    local head = lines[index]
    local name, params = head:match("^function Eval:([%w_]+)%((.*)%)$")
    local isConverted = params and params:find("%f[%w]machine%f[%W]") and params:find("%f[%w]k%f[%W]")
    if name and isConverted then
        converted = converted + 1
        local body, last, answers = {}, index + 1, 0
        while last <= #lines and lines[last] ~= "end" do body[#body + 1] = lines[last]; last = last + 1 end
        for offset, line in ipairs(body) do
            local at = index + offset
            -- Any `return` in the body, not just one at the start of a line: the violation this
            -- lint exists for was `if #bound == 1 then return bound[1] end`, which the line-anchored
            -- form missed and which the driver answered with "attempt to call a table value".
            -- Two shapes a converted body legitimately contains, and the lint must not call them
            -- violations: a `return` inside an anonymous closure (`pcall(function() return ... end)`),
            -- whose answer is not this method's, and `return localName(...)` where `localName` is a
            -- local driver declared in the same body that itself answers through `k` (the element and
            -- handler walks are written that way).
            local opensClosure = line:find("function") and line:find("return")
                and line:find("function") < line:find("return")
            local localDriver = nil
            for declared in line:gmatch("return%s+([%w_]+)%(") do localDriver = declared end
            for _, bodyLine in ipairs(body) do
                if localDriver and bodyLine:match("local function " .. localDriver .. "%(") then
                    opensClosure = true
                end
                -- A driver that had to be forward declared (`local afterParameters` then
                -- `afterParameters = function(...)`) is a local too, and the assignment must sit above
                -- its caller or it is never reached -- which is exactly the bug this check now covers.
                if localDriver and bodyLine:match("local " .. localDriver .. "%s*$") then
                    opensClosure = true
                end
                if localDriver and bodyLine:match("^%s*" .. localDriver .. " = function%(") then
                    opensClosure = true
                end
            end
            -- The frontier matters: without it `not returned then` reads as a return statement, which is
            -- how two `execBody` bodies were reported as violations when they were correct.
            -- A comment is prose: "A handler is a callable, so it may return a result vector" is not a
            -- return statement, and the word `return` in it is not a missing continuation.
            local comment = line:match("^%s*%-%-")
            local scan = (opensClosure or comment) and "" or line
            local position = 1
            while true do
                local startAt, endAt, after = scan:find("%f[%w]return%s+([^%s])", position)
                if not startAt then break end
                position = endAt + 1
                -- Inside a quoted string, `return` is prose: "Every reachable path must return a
                -- value" was reported as a missing continuation until quote parity was checked.
                local quoted = select(2, line:sub(1, startAt - 1):gsub('"', "")) % 2 == 1
                -- A tail call into a converted method passes `machine` first, whether or not its
                -- name carries the `CPS` suffix (`evalUnary` predates the convention).
                local call = line:sub(startAt)
                if not quoted and after ~= "k" and not call:match("return%s+self:[%w_]+CPS%(")
                    and not call:match("return%s+self:[%w_]+%(machine,")
                    and not call:match("return%s+self:[%w_]+%(m%d*,")
                    and not call:match("return%s+self:drive%(") then
                    report(at, ("%s returns without its continuation: %s"):format(name,
                        line:gsub("^%s+", "")))
                end
            end
            if line:match("return%s+k%(") or line:match("return%s+self:[%w_]+CPS%(") then
                answers = answers + 1
            end
        end
        if answers == 0 then
            report(index, ("%s never answers through `k`"):format(name))
        end
        index = last + 1
    else
        index = index + 1
    end
end


-- A range replacement that ends at a function's last *statement* leaves its `end` behind, and a stray
-- duplicate `end` parses as "expected near 'end'" far from the edit. It has happened on almost every
-- batch, so it is checked here: two column-0 `end` lines in a row inside a function body is the shape.
for index = 1, #lines - 1 do
    if lines[index] == "end" and lines[index + 1] == "end" then
        report(index + 1, "duplicate `end` (a replaced range left the original behind)")
    end
end

-- A converted method that kept its plain name (`evalUnary`, `evalShortCircuit`) is the trap the shims
-- hide: a call written with the *old* signature looks like an ordinary method call, reaches the CPS
-- body with `machine = ctx`, and the first thing that touches the real `expr` is nil.
local plainNamed = { "evalUnary", "evalShortCircuit" }
for _, name in ipairs(plainNamed) do
    local pattern = "self:" .. name .. "%("
    for index, text in ipairs(lines) do
        if text:match(pattern) and not text:match("self:" .. name .. "%(machine,")
            and not text:match("function Eval:" .. name .. "%(") then
            report(index, ("%s is called without the machine: %s"):format(name, text:gsub("^%s+", "")))
        end
    end
end

-- The boundary helpers are the scaffold: they must keep answering values, not pairs, and every one of
-- them is deleted by the rip's last step.
local shims = 0
local function count(pattern) local _, n = text:gsub(pattern, ""); return n end
-- The scaffold boundary: the drive wrapper and the answer continuation. Everything else in this
-- file is a continuation the machine calls.
shims = count("self:drive%(") + count("function Eval:drive%(") + count("local function done%(")
print(("cpslint: %d converted methods, %d scaffold sites, %d protocol violations"):format(converted, shims, violations))
os.exit(violations == 0 and 0 or 1)
