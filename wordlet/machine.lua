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
    while true do
        local descriptor = self:pop()
        if not descriptor then return nil end
        if descriptor.handler then return descriptor end
    end
end

-- The depth budgets count descriptors, so they report an exact number and name the frame that hit it
-- rather than depending on how much host stack happened to be left.
function Machine:checkDepth(kind, span, name)
    local allowed = (self.session.run and self.session.maxInterpretDepth) or self.session.maxBuildDepth
    if self.depth >= allowed then
        D.resource("depth", ("%s nests more than %d deep (at %s); a recursive word whose static "
            .. "arguments change specializes once per value, so bind the changing value at run time")
            :format(kind, allowed, name), span)
    end
end

-- A step: call the continuation with the value, under the one protected call, and answer with the next
-- pair. A diagnostic that is not ours is re-raised untouched; ours goes to the nearest handler.
function Machine:step(k, value)
    local ok, nextK, nextValue = pcall(k, self, value)
    if ok then return nextK, nextValue end
    if not D.is(nextK) then error(nextK, 0) end
    local descriptor = self:popToHandler()
    if not descriptor then error(nextK, 0) end
    return descriptor.handler, nextK
end

-- Drive until a continuation answers `nil`: the closure chain is the stack, and this loop is the only
-- host frame it needs.
function Machine:run(k, value)
    while k do
        self.session.steps = self.session.steps + 1
        if self.session.steps > self.session.maxSteps then
            D.resource("steps", "Static evaluation budget exhausted")
        end
        k, value = self:step(k, value)
    end
    return value
end

-- A self-tail call does not push a frame: it rewrites the one it is in, which is the trampoline the
-- residual layer already performs as `Ir.Loop`/`Ir.Next`.
function Machine:rewrite(descriptor, bindings)
    descriptor.bindings = bindings
    return descriptor
end

M.Machine = Machine
return M
