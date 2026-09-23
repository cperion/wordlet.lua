-- The evaluator's control core (`wordlet/machine.lua`). Loaded by tests/run.lua from the project root.
--
-- These pin the property the CPS rewrite rests on, so it cannot rot silently: pending continuations
-- cost heap rather than host stack, a diagnostic reaches the nearest handler and the machine resumes,
-- and the depth budget is a counted number that names the frame which hit it.
local source = debug.getinfo(1, "S").source:sub(2)
package.path = (source:match("^(.*[/\\])") or "./") .. "../?.lua;"
    .. (source:match("^(.*[/\\])") or "./") .. "../?/init.lua;" .. package.path

local Machine = require("wordlet.machine")
local Session = require("wordlet.session")
local D = require("wordlet.diag")
local checks = 0
local function check(ok, message) assert(ok, message); checks = checks + 1 end

-- The reference interpreter's budgets are the largest ones, and `run` selects them.
local function interpreter(limits)
    local session = Session.new({ limits = limits })
    session.run = true
    return Machine.new(session)
end

-- A hundred thousand pending continuations. The direct evaluator reaches about 1156 before the host's
-- Lua stack runs out, so this number is not decoration: it is the whole point of the rewrite.
do
    local depth = 100000
    local function countdown(_, n)
        if n == 0 then return nil, n end
        return countdown, n - 1
    end
    local machine = interpreter({ steps = 10000000, interpretDepth = 10000000 })
    local reached = machine:run(countdown, depth)
    check(reached == 0, "a 100 000-step continuation chain runs to the end")
    check(machine.session.steps == depth + 1, "every step is counted in the session's step budget")
end

-- A diagnostic abandons the pending chain (nothing to unwind: the closures are simply not called) and
-- hands the diagnostic to the nearest handler descriptor, whose answer resumes the machine. This is
-- what replaces the `pcall` that `withNesting` wraps around every fold attempt today.
do
    local sawCode, sawSpan
    local function swallow(_, diagnostic)
        sawCode, sawSpan = diagnostic.code, diagnostic.span
        return function(_, value) return nil, value + 7 end, 0
    end
    local function descend(_, n)
        if n == 0 then D.resource("static-depth", "too deep to fold", { file = "t.let", line = 3 }) end
        return descend, n - 1
    end
    local machine = interpreter({ steps = 10000000, interpretDepth = 10000000 })
    local resumed = machine:run(function(target)
        target:push("Try", { file = "t.let", line = 1 }, "fold attempt", swallow)
        return descend, 1000
    end, 0)
    check(sawCode == "static-depth", "the handler receives the diagnostic the deep step raised")
    check(sawSpan ~= nil, "a descriptor carries the span a diagnostic is reported at")
    check(resumed == 7, "the handler's continuation resumes the machine with its own value")
end

-- A Lua error that is not a Diagnostic is not ours to swallow: it is re-raised untouched.
do
    local machine = interpreter({ steps = 10000000 })
    local ok, err = pcall(function() return machine:run(function() error("host failure", 0) end, 0) end)
    check(not ok and err == "host failure", "a host error is not treated as a compiler diagnostic")
end

-- Depth is a counted number of descriptors, and the budget names the frame that hit it. The limit is
-- the session's, so an interpreter run uses the interpreter's budget.
do
    local machine = interpreter({ interpretDepth = 64, steps = 10000000 })
    local function nest(_, count)
        machine:checkDepth("call", { file = "t.let", line = 1 }, "g")
        machine:push("Call", { file = "t.let", line = 1 }, "g")
        return nest, (count or 0) + 1
    end
    local ok, err = pcall(function() return machine:run(nest, 0) end)
    check(not ok and D.is(err) and err.code == "depth", "the depth budget refuses at its own count")
    check(err.message:find("64", 1, true) ~= nil and err.message:find("at g", 1, true) ~= nil,
        "the depth diagnostic names the limit and the frame that hit it")

    -- A self-tail call rewrites the frame it is in, so a tail-recursive chain never grows the count.
    local tail = interpreter({ interpretDepth = 64, steps = 10000000 })
    local descriptor = tail:push("Call", nil, "g")
    for iteration = 1, 10000 do
        descriptor = tail:rewrite(descriptor, { iteration })
        tail:checkDepth("call", nil, "g")
    end
    check(tail.depth == 1, "a self-tail call reuses its frame instead of nesting")
end


-- The migration boundary (`Eval:onMachine`): a direct-style caller gets a value out of a CPS chain.
-- One machine per session, so a builtin that re-enters evaluation gets a second stack rather than
-- corrupting this one; the descriptors a chain pushed are gone when it answers; and a diagnostic
-- crosses the boundary as a Diagnostic, which is what lets the direct-style code above keep treating
-- it exactly as before.
do
    -- Requiring the evaluator installs its methods on the session class: the frames come from there.
    local Eval = require("wordlet.eval")
    local session = Eval.new({ limits = { steps = 100000 } })
    session.run = true
    local ctx = session:staticFrame(nil, { file = "t.let", line = 1 })
    local function finish(_, value) return nil, value end
    local function start() return finish, 41 end

    check(session:onMachine(ctx, start) == 41, "a CPS chain answers its value to the caller")
    check(session.machine ~= nil, "the machine is kept on the session for the next boundary")
    check(session.machine.depth == 0, "no descriptor survives a finished chain")

    local function bad()
        return function() D.reject("t-machine", "raised inside a step", nil) end, nil
    end
    local ok, err = pcall(function() return session:onMachine(ctx, bad) end)
    check(not ok and D.is(err) and err.code == "t-machine", "a diagnostic crosses the boundary as one")
    check(session:onMachine(ctx, start) == 41, "the machine is usable again after a diagnostic")
    check(session.machine.session == session, "the machine belongs to one session, never to a global")
end

print(("PASS: control core (%d checks: constant host stack, handler unwinding, counted depth, migration boundary)"):format(checks))
