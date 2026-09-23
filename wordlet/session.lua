-- The compilation session: every table one compilation owns, and the budgets that bound how deeply
-- it may nest. `structure.md` §3.2 fixes this shape.
--
-- `eval.lua` installs the evaluator's methods on this same class (`local Eval = Session`), so a
-- session is the receiver of every `Eval:*` method. This module owns the data and the nesting
-- counters; the walk that fills them stays in the evaluator.
--
-- The two layers `ASDL.md` states are visible here. `types` caches interned `Ty` descriptions, so
-- it grows with distinct types only and its keys are identities. Everything beside it is an
-- occurrence — a specialization, a plan, an arm, a definition, a module cell — so a session is never
-- reused: a second compilation needs a second session, because those tables and the budgets below
-- belong to the compilation that filled them.
local D = require("wordlet.diag")

local Session = {}
Session.__index = Session

function Session.new(options)
    options = options or {}
    local limits = options.limits or {}
    return setmetatable({
        -- Configuration, read-only after construction.
        options = options, limits = limits,

        -- Descriptions: interned `Ty` values, keyed by identity.
        types = {
            cells = {},       -- a named cell's sealed definition, keyed by the cell identity
            byMeaning = {},   -- S.encode(ty) -> the one named type with that structural meaning
            referenced = {},  -- cells named through Ref/Ptr/Slice, which need emitting even when empty
        },

        -- Occurrences: what one compilation builds, keyed by the identity that distinguishes it.
        defs = {},              -- source name -> definition
        instances = {},         -- instance key -> instance
        order = {},             -- Instance[], build order
        plans = {},             -- plan key -> closure plan
        arms = {},              -- arm key -> tagged-callable arm
        modules = {},           -- module storage entry, first-demand order
        -- Foreign declarations in first-use order, so the prototypes they need are deterministic.
        foreigns = { instances = {}, order = {} },

        -- Identity allocators.
        nextCell = 0, nextDef = 0, nextFn = 0, nextModule = 0,

        -- Budget counters, reset per compilation.
        steps = 0, maxSteps = limits.steps or 1000000,
        -- Three separate budgets, because they bound three different recursions. Specialization
        -- nesting is the depth of nested instance building; static depth is nested compile-time
        -- folding, which is an optimization in residual code and can fall back to compiling; and
        -- the interpreter, which has no fallback, gets the largest bound it can have without
        -- reaching the host's own stack limit (measured at roughly 2500 on this host, so this
        -- deliberately stays well below it).
        buildDepth = 0, maxBuildDepth = limits.depth or 256,
        staticDepth = 0, maxStaticDepth = limits.staticDepth or 64,
        maxInterpretDepth = limits.interpretDepth or 1024,

        -- Compile-wide mode.
        top = nil,        -- the current module's top scope
        run = false,      -- the reference interpreter: reads and writes module storage
        demanding = false, -- a module initializer is being demanded
    }, Session)
end

function Session:step(span)
    self.steps = self.steps + 1
    if self.steps > self.maxSteps then D.resource("steps", "Static evaluation budget exhausted", span) end
end

-- Run one nested attempt under the budget `kind` names, restoring the depth however the attempt
-- ends. Both limits are checked before the depth changes, so a refused entry leaves the session as
-- it found it, and the attempt runs under `pcall` because a diagnostic is not always fatal: a build
-- records the failed instance and re-raises, while a fold in residual code compiles instead. The
-- caller decides which, so this returns the diagnostic rather than raising it.
--
-- `scope` is the word the static message names, so a nested fold that runs out of room says which
-- recursive word needs a run-time argument.
function Session:withNesting(kind, span, scope, fn, ...)
    local static = kind == "static"
    if static then
        local allowed = self.run and self.maxInterpretDepth or self.maxStaticDepth
        if self.staticDepth >= allowed then
            D.resource("static-depth", "Static evaluation nests more than " .. allowed .. " deep in "
                .. scope .. "; a recursive word with a run-time argument is compiled instead, and"
                .. " the reference interpreter is bounded", span)
        end
        self.staticDepth = self.staticDepth + 1
    else
        -- Specialization nests: building one instance evaluates its body, and a body that
        -- specializes again nests another build. The host's Lua stack gives out long before a
        -- thousand nested builds would reach the key budget, so the nesting is bounded here and its
        -- exhaustion names a resource instead of surfacing as an unlabelled stack overflow.
        if self.buildDepth >= self.maxBuildDepth then
            D.resource("depth", "Specialization nests more than " .. self.maxBuildDepth
                .. " deep; a recursive word whose static arguments change specializes once per value,"
                .. " so bind the changing value at run time", span)
        end
        self.buildDepth = self.buildDepth + 1
    end
    -- `pcall`'s status and the one value the attempt produced: every caller destructures that pair,
    -- and an attempt that produced no value is `true, nil`.
    local ok, value = pcall(fn, ...)
    if static then self.staticDepth = self.staticDepth - 1
    else self.buildDepth = self.buildDepth - 1 end
    return ok, value
end

return Session
