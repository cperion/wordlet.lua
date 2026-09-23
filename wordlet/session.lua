-- The compilation session: every table one compilation owns, and the budgets that bound how deeply
-- it may nest. `structure.md` §3.2 fixes this shape.
--
-- `eval.lua` installs the evaluator's methods on this same class (`local Eval = Session`), so a
-- session is the receiver of every `Eval:*` method. This module owns the data and the budgets; the
-- walk that fills them stays in the evaluator, and the machine counts the depth.
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


return Session
