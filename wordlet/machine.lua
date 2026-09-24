-- The evaluator's control core: continuation-passing with Lua closures, one driver loop, and a shadow
-- stack of descriptors for the frames that must be counted, reported or unwound through.
--
-- Why this is stack-safe. Lua guarantees proper tail calls, so a step written as
-- `return k(value)` in tail position reuses its frame instead of growing the host stack. The direct
-- evaluator grows because a sequence like `local left = eval(left) ... eval(right)` is not in tail
-- position, and because every fold attempt wraps itself in a `pcall` -- a protected call can never be
-- a tail call. Writing every recursive edge as
--
--     return eval(child, function(value) ... return k(...) end)
--
-- makes all of them tail, and moving protection to the single `pcall` per step in the driver removes
-- the rest. Depth then costs heap (one closure per pending step), not host frames.
--
-- The driver's convention is a pair: a step is `(k, value)`, and a continuation answers with the next
-- pair, or with `nil` as the continuation to mean "this is the final value".
--
-- Closures are opaque, which is what the descriptors are for: the continuation chain cannot be walked,
-- so the descriptors are its inspectable shadow. A diagnostic needs no unwinding at all -- the pending
-- chain is simply not called -- but it must find the nearest *handler*, and that is the descriptor
-- stack's job. A handler is a continuation that takes the diagnostic and answers with the pair that
-- resumes the machine (which is how a fold that cannot finish becomes a compiled instance instead).
local D = require("wordlet.diag")

local M = {}

local Machine = {}
Machine.__index = Machine

function M.new(session)
    return setmetatable({ session = session, descriptors = {}, depth = 0 }, Machine)
end

-- A descriptor is the data half of a frame: what it is, where it came from, and how to continue if a
-- diagnostic arrives. `handler` is present only for a boundary that can swallow one.
function Machine:push(kind, span, name, handler)
    local descriptor = { kind = kind, span = span, name = name, handler = handler }
    self.descriptors[#self.descriptors + 1] = descriptor
    self.depth = self.depth + 1
    return descriptor
end

function Machine:pop()
    local descriptor = self.descriptors[#self.descriptors]
    if descriptor then
        self.descriptors[#self.descriptors] = nil
        self.depth = self.depth - 1
    end
    return descriptor
end

-- The nearest boundary that can swallow a diagnostic, with everything above it dropped: those steps
-- are not state to unwind, they are continuations that will never be called.
function Machine:popToHandler()
    local descriptor = self:pop()
    while descriptor do
        if descriptor.handler then return descriptor end
        descriptor = self:pop()
    end
    return nil
end

-- The depth budgets count descriptors, so they report an exact number and name the frame that hit it
-- rather than depending on how much host stack happened to be left.
function Machine:checkDepth(kind, span, name)
    -- Two kinds, because they bound two different recursions and carry two different codes. A static
    -- fold is an optimization in residual code, so it is bounded by `maxStaticDepth` and its refusal is
    -- `static-depth` (a residual fold compiles instead); the reference interpreter has no fallback and
    -- gets `maxInterpretDepth`. Specialization nesting is bounded by `maxBuildDepth` and reports
    -- `depth`. These are the session's own numbers and messages; the descriptors are what count the
    -- depth, so the two bounds live here rather than in a wrapper.
    local allowed, code
    if kind == "static" then
        allowed = self.session.run and self.session.maxInterpretDepth or self.session.maxStaticDepth
        code = "static-depth"
    else
        -- A build or a call nests in an interpreter run too, where there is no fallback, so the
        -- interpreter's budget applies, as the session's nesting wrapper used to choose it.
        allowed = self.session.run and self.session.maxInterpretDepth or self.session.maxBuildDepth
        code = "depth"
    end
    if self.depth >= allowed then
        local message
        if kind == "static" then
            message = "Static evaluation nests more than " .. allowed .. " deep in " .. name
                .. "; a recursive word with a run-time argument is compiled instead, and"
                .. " the reference interpreter is bounded"
        else
            message = ("%s nests more than %d deep (at %s); a recursive word whose static arguments"
                .. " change specializes once per value, so bind the changing value at run time")
                :format(kind, allowed, name)
        end
        D.resource(code, message, span)
    end
end

-- A step: call the continuation, under the one protected call, and answer with the next pair. A
-- diagnostic that is not ours is re-raised untouched; ours goes to the nearest handler.
--
-- The value part is a *vector*, because the language's own answers are: a value definition produces one
-- value per binder, a store target produces a slot and a place, and a declared result list produces the
-- types and the signature requirements. Carrying one value here silently dropped the rest at every
-- boundary, which is what made a lambda lose the signature that was supposed to type it.
function Machine:step(k, ...)
    local function invoke(...) return { n = select("#", ...), ... } end
    local results = invoke(pcall(k, self, ...))
    if results[1] then
        -- A successful step is (continuation, values...): the protected call's status flag is not part
        -- of the protocol, so it is dropped here rather than by every reader of the pair.
        local shifted = { n = results.n - 1 }
        for index = 2, results.n do shifted[index - 1] = results[index] end
        return shifted
    end
    local diagnostic = results[2]
    if not D.is(diagnostic) then error(diagnostic, 0) end
    local descriptor = self:popToHandler()
    if not descriptor then error(diagnostic, 0) end
    return { n = 2, descriptor.handler, diagnostic }
end

-- Drive until a continuation answers `nil`: the closure chain is the stack, and this loop is the only
-- host frame it needs. The value vector is repacked per step so an answer of any arity survives.
function Machine:run(k, ...)
    local values = { n = select("#", ...), ... }
    while k do
        self.session.steps = self.session.steps + 1
        if self.session.steps > self.session.maxSteps then
            D.resource("steps", "Static evaluation budget exhausted")
        end
        local results = self:step(k, unpack(values, 1, values.n))
        k = results[1]
        values = { n = results.n - 1 }
        for index = 2, results.n do values[index - 1] = results[index] end
    end
    return unpack(values, 1, values.n)
end

-- A self-tail call does not push a frame: it rewrites the one it is in, which is the trampoline the
-- residual layer already performs as `Ir.Loop`/`Ir.Next`.
function Machine:rewrite(descriptor, bindings)
    descriptor.bindings = bindings
    return descriptor
end

-- Run a CPS entry to a value. A converted method takes one more argument than it used to -- the
-- continuation -- so a caller that is not converted yet needs exactly this: one host frame at the
-- boundary, and none per step. It is a migration device and it disappears with the last such caller.
function Machine:call(entry)
    return self:run(entry, nil)
end

M.Machine = Machine
return M
