# Contextual C emission: tail components first

## 0. Decision and scope

**Keep the current evaluator and typed residual IR. Add one contextual body emitter. Use it to lower
safe mutual-tail recursion to labels, and optionally to expand small residual helpers.**

We may emit slightly more C to expose local computation and avoid unnecessary calls. That is a code
quality policy, not a claim that more source always produces faster machine code. The current backend
already asks GCC/Clang to inline private functions; ordinary helper expansion must earn its place by
measurement. The new, concrete guarantee is bounded stack for recognized safe mutual-tail cycles,
including at `-O0` without host inlining or sibling-call optimization.

This revision replaces the earlier broad redesign. Do **not** implement its new CFG schema, evaluator
cutover, global frame-region unions, return selectors, generalized continuation carriers or new VM.
Keep `Ir.Fn`, structured `If`/`Switch`, `Loop`/`Next`, independent specialization and the existing C
representations. The compiler's Lua CPS evaluator is not the runtime control mechanism being changed.

The organizing operation is:

```text
emit_body(checked residual body, input bindings, static return destination)
```

It emits operations, not a runtime PC, operand stack or dispatcher. A known invocation has three
possible lowerings:

| Situation | Lowering |
| --- | --- |
| Eligible tail transfer within the current tail component | Parallel input binding, then goto a reserved entry label |
| Affordable known helper, with no overlapping active component | Emit a fresh contextual copy of its residual body |
| Other invocation | Keep an ordinary C call |

Tail-component expansion is mandatory; optional helper expansion is separately budgeted. Setting its
budget to zero must not break a recognized tail cycle into recursive C calls.

### Production status

Implemented through owned APIs in `wordlet/tail.lua`, `wordlet/contextual.lua` and `wordlet/lower.lua`;
registered in the standalone bundle. No ASDL, ABI, specialization-key or evaluator architecture
replacement was needed. Optional credit defaults to **0**, nesting stops at **32 Groups**, and total
weighted emission defaults to **1,000,000 nodes**. See `interfaces.md` for the options and reports,
and `VALIDATION.md` for production test evidence, distinct from the historical prototype below.

Production regressions also exposed and fixed evaluator bugs: vector-valued expression conditionals,
Unit/common-value joining, missing control when both nested arms tail-transfer, tail context under a
known condition, signed-zero comparison, and module-state reads folded during nullary calls or code
construction inside initialization. Existing self-tail parameter-alias work is preserved. These are
focused semantic fixes, not a replacement frontend or source replay in the backend.

The full corpus runs at zero/nonzero credit. Dedicated tests exercise expression/statement tuple
cycles, foreign-driven and module-state-driven nullary Unit cycles, retained borrowed receivers and
cleanup, local/opaque returns, discarded results, effects, imports/header separation, deterministic
output, template immutability and bounds. Deep cycles run at five million steps under GCC/Clang
O0/O2/O3 with host inlining/sibling calls disabled and a 256 KiB stack. No runtime speedup is claimed.

## 1. Historical prototype evidence

A backend-only prototype operates on **actual Wordlet residual IR**, not a scalar toy language. It
uses the existing checker, analysis, arithmetic/place emitter and ABI layouts. Its only hook into the
copied compiler is at the end of `wordlet/lower.lua`; the implementation is a separate experimental
module. The repository's evaluator and tests were not edited for it.

Scratch artifacts from this investigation:

```text
/tmp/wordlet-contextual.jlQAzQ/project/wordlet/contextual.lua
/tmp/wordlet-contextual.jlQAzQ/project/tests/contextual-witness.lua
/tmp/wordlet-contextual.jlQAzQ/project/tests/contextual-corpus.lua
/tmp/wordlet-contextual.jlQAzQ/run.py
/tmp/wordlet-contextual.jlQAzQ/matrix.log
```

Those paths are session artifacts, not distribution dependencies or a substitute for the specification
below. The monkey-patch hook was an experiment; production uses owned emitter APIs instead.

### Actual results

- The pre-integration compiler passed `timeout --kill-after=2s 180s luajit tests/run.lua` in
  **20.04 s**, including bundling/isolation and the ongoing evaluator changes in the working tree.
- The prototype passed the existing **41-program interpreter/C differential corpus, 621 harness
  checks per run**, at credits 0 and 512, with GCC and Clang at both `-O0` and `-O2`: eight runs.
- Six additional witnesses passed at both credits, with both compilers at `-O0`, `-O2` and `-O3`:
  **72 compile/run combinations**, using strict C11 warnings, disabled host inlining and sibling-call
  optimization, and a **256 KiB stack**.
- Witnesses cover repeated/nested helpers shared by two exports, mutual tails at 5,000,000/5,000,001
  steps, existing self-tail argument swaps, mixed recursion, a borrowed method surviving recursive
  work, and an 18-level repeated-helper growth case. The witness harness also checks template fields
  and lists are unchanged, repeated compilation is deterministic, and per-function budgets hold.
- The final combined prototype matrix took **92.765 s**. This is validation wall time, not a runtime
  speed measurement. The extracted differential harness needed a final newline for Clang's strict
  EOF warning; no warning was disabled to hide it.

Selected emitted-C measurements, excluding witness mains:

| Program | Credit | C roots | Remaining direct-call sites | C bytes |
| --- | ---: | ---: | ---: | ---: |
| Two exports using small nested helpers | 0 | 4 | 5 | 882 |
| Same helpers | 512 | 2 | 0 | 2,385 |
| Mutual even/odd | 0 or 512 | 2 | 0 | 1,126 |
| Repeated-helper growth chain | 0 | 19 | 36 | 4,954 |
| Same growth chain | 512 | 19 | 141 | 141,508 |

The growth example is a warning: a bounded greedy depth-first policy can still duplicate extensively
without eliminating outlines. Do not ship credit 512 as a supposedly tuned default. The prototype
also disables forced host inlining for all private bodies and duplicates public aliases; neither is
a necessary production change.

The full project suite was **not** run against the prototype. In particular, these results do not
certify all foreign/callback ABI paths, distribution integration or a general lifetime analysis.
The prototype recognizes direct Call/Return pairs; it did not implement forwarding through structured
joins. Production now does, with checked copy-only normalization. No general runtime speedup over the current compiler has been established. An earlier
synthetic comparison even found a GCC `-O3` slowdown from duplication, reinforcing the need to measure.

## 2. Preserve the frontend boundary

Compilation still does:

```text
source → current evaluator → independently checked Ir.Fn instances
                              ↓
                     tail preparation / analysis
                              ↓
                     contextual C body emission
                              ↓
                  existing layout/artifact closure
```

Do not change these to implement this feature:

- instance reservation, specialization keys and recursion result contracts;
- `constructInstanceCPS` / `constructCallableInstanceCPS` source elaboration;
- runtime argument evaluation and immediate read snapshots;
- `value.body` construction homes and demand-driven spilling;
- source closure/capture checks, Unit erasure and tagged-callable dispatch;
- existing self-tail `Loop`/`Next` generation;
- defer capture and source scope-exit semantics.

The emitter consumes compiler data. It never re-evaluates AST expressions or infers a static/effect-free
call merely from a known code identity. Preserve the existing fixes in `wordlet/eval.lua` and
`tests/eval.lua`, including self-tail aliases, lambda laziness and Unit behavior. Focused frontend
bug fixes discovered during validation are described in the production status above.

## 3. Tail preparation over the current IR

Use a new `wordlet/tail.lua` module for preparation, separate from C text rendering. Its tables belong
to this compilation, not to process-global caches or interned Ty nodes.

### 3.1 First recognize an exact terminal pair

Within a statement list, recognize its final two statements:

```text
Call([r1, ...], target, arguments)
Return([Ref(r1), ...])
```

Require positional identity of the entire runtime result vector and equal target/owner result types.
Zero-result Call followed by empty Return is valid. A projection, conversion, arithmetic operation,
cleanup action or return of an additional caller value is not this pattern.

Store a fact about the Call occurrence; do not mutate its `kind`, results or target. A fact records the
owning Fn, list/index, following Return and target. The emitter consumes the pair together when it
uses a tail transfer. Restricting the pair to the end of the list avoids leaving unreachable references
to call-result bindings that emission no longer declares.

Enumerate nested statements through `wordlet/walk.lua`. Its reflected field types are qualified
(`Ir.Stmt`, `Ir.Case`), not bare `Stmt` and `Case`. Structural descent is schema-driven; the decisions
about adjacency, return identity and lifetime are explicit semantic rules.

### 3.2 Normalize forwarding joins without introducing a new IR

Common expression bodies currently transport results through join storage:

```text
Var(join, T, nil)
If(test,
   [Call(r, f, args), Store(Local(join), Ref(r))],
   [Store(Local(join), base)])
Read(v, T, Local(join))
Return([Ref(v)])
```

For a proven private transport slot, rewrite to ordinary existing IR:

```text
If(test,
   [Call(r, f, args), Return([Ref(r)])],
   [Return([base])])
```

Then the same terminal-pair recognizer works. No CFG schema or source evaluator rewrite is needed.

Implement this as a conservative copy transformation, not textual C editing:

1. Match an exact trailing Read/Return transport and the owning join declaration/control shape.
2. Verify the slots are owned, unexposed locals; every occurrence belongs to the matched declaration,
   transport reads and terminal arm stores. Reject module storage and PlaceParam referents.
3. Require every continuing arm to establish the complete returned vector. Already-returning arms
   and existing Next paths retain their behavior.
4. Replace only matched terminal stores/reads with Return expressions. Preserve all preceding calls,
   snapshots, stores, traps and guards in their original order. If proving this requires dropping an
   operation with observable behavior, decline the transformation.
5. Remove now-unused join declarations and transport nodes, copy affected lists/If/Switch/Fn nodes,
   and check the resulting functions again with the same module/foreign definitions.
6. Run `Analysis.analyze` on the normalized body, not the old transport body.

Start with the exact single-result diamond, then nested diamonds/Switch and result vectors. Do not
use the current `Check.falls` treatment of Trap as a general reachability proof: Trap is conditional,
not an unconditional successful exit. Unknown patterns remain ordinary calls.

This normalization is implemented and tested in production; it was not proven by the prototype.
Both `if ... then f(...) else g(...)` and statement-form tail returns need tests before advertising
support for ordinary scalar mutual-tail recursion.

### 3.3 Activation reuse needs a separate safety condition

Being in return position does not prove the previous invocation's storage can be overwritten or its
scope exited. A slice, raw address, borrowed receiver or closure environment may still expose it.

Use a deliberately sufficient first rule, matching the prototype's limited proof:

- all formal inputs are by-value scalar integers, Bool or F64;
- all runtime results and invocation-owned storage/value representations are scalar;
- the body contains no Addr, BorrowArg, View or Indirect occurrence, and no operation exposing an owned
  object through another representation.

Module storage has independent lifetime; accessing it does not make it invocation-owned. Existing
`Loop`/`Next` nodes keep their existing semantics rather than being reclassified by this rule.

A failure of this conservative rule means **keep the call**, not reject the source. Broader reuse may
be added only with explicit owned-root/provenance evidence and adversarial lifetime tests. In
particular, an incoming borrowed referent is not necessarily callee-owned, but proving more cases is
outside the initial scalar guarantee.

Ordinary non-tail helper expansion can still handle records, borrowed inputs and environments: it
uses fresh bindings and nested C scopes, not activation reuse. The distinction is essential.

### 3.4 Compute directed tail components

Only reuse-safe direct pairs enter `Plan.tailSites`; keep unproved structural candidates out of that
map. Build their directed graph, then compute SCCs. A singleton with no self edge is just a one-entry
component. Only directed cycles require mandatory grouping; never
merge unrelated functions because they happen to share a helper.

Every component has a common runtime result interface, though its members may have different input
counts/types. Reserve all member entry labels and input carriers before emitting any member body.
The prototype used repeated reachability for small graphs; production uses an iterative linear
SCC algorithm and deterministic input order.

The guarantee is precise: **cycles entirely composed of recognized, reuse-safe forwarding edges are
local control**. An unrecognized or lifetime-retaining edge does not acquire that guarantee merely
because the source call looks tail-positioned.

## 4. Four small compiler-state records

Keep original per-Fn Value/Storage ids. Qualify emitted local names by context; no global IR-id
migration or alpha-cloned expression graph is required merely to print a fresh copy.

```lua
Plan = {
    functions,                  -- target -> original or normalized checked Fn
    analyses,                   -- target -> Analysis.analyze(functions[target])
    tailSites,                  -- Call occurrence -> terminal-pair and safety evidence
    componentOf, components,    -- target -> component; component -> ordered member targets
    costs,                      -- base component weight, without transitive expansion
}

Unit = {
    root, lines, remaining, nextName,
    active = {},                -- component ids on the current emission nesting path
    calls = {},                 -- actual remaining C-call edges and their reasons
}

Group = {
    component, destination,
    entries = {},               -- target -> member Context, reserved before body emission
}

Context = {
    unit, group, signature, analysis,
    prefix, destination,        -- fresh namespace and compiler-only return destination
    -- existing per-emitter assigned/shared/inline/storageAlias state remains local here
}
```

A destination is either `CExit` or `{ label, outputs, types }`. Outputs are caller-local result names,
omitting unused results. It is a Lua compiler object; never emit a return selector for it.

No general global `(pc, symbolic stack)` memo table is needed. A Group's reserved entries close its
own tail cycle. Separate ordinary invocations may simply create separate Groups, with fresh names
and destinations. This deliberately permits duplication instead of maximizing sharing.

## 5. One contextual emission mechanism

### 5.1 Enter a body/component

```text
emitGroup(unit, component, selectedEntry, arguments, destination):
    reserve a Context for every member
    reserve the member input carriers and entry labels
    bind selectedEntry's inputs
    mark component active
    enter selectedEntry; emit every member body using existing statement/expression lowering
    unmark component active
```

For a cyclic component, input carriers live in the enclosing group scope and each member body has a
braced entry scope. This lets a transfer leave the departing invocation's locals and enter the target's
initialization code. The reuse-safety rule must justify that departure.

For an ordinary singleton, emit a nested block without entry/goto scaffolding. At a root, reuse the
actual C parameters rather than copying all of them into a second set of locals. Existing self-tail
loops remain loops inside the member body.

### 5.2 Lower a known invocation

This is algorithmic pseudocode; `emitNormalCall` still uses existing typed ABI/result lowering:

```lua
local component = plan.componentOf[call.target]
local site = plan.tailSites[call]
local localTarget = site and ctx.group.entries[call.target]

if localTarget then
    emitParallelInputs(ctx, localTarget, call.arguments)
    emitGoto(localTarget.label)
    return 2                         -- consumed Call and its exact terminal Return
end

if component and not ctx.unit.active[component.id]
    and withinExpansionDepth(ctx.unit)
    and component.cost <= ctx.unit.remaining then
    ctx.unit.remaining = ctx.unit.remaining - component.cost
    local destination = site and ctx.destination or newLocalDestination(ctx, call)
    emitGroup(ctx.unit, component, call.target, call.arguments, destination)
    if not site then finishLocalDestinationIfNeeded(destination) end
    return site and 2 or 1
end

requireResidualRootIfPresent(call.target) -- foreign targets need declarations, not bodies
recordActualCallAndReason(ctx.unit, call)
return emitNormalCall(ctx, call)
```

Internal component transfers are checked **before** the optional budget or active-component cut.
A non-tail call into an active component must remain a real call: the older invocation is suspended
and its locals/results may still matter. A call to an ancestor component is also conservatively cut,
even if a more elaborate unroller could emit another finite copy.

This active-path rule replaces the earlier global retaining-edge admission DAG. There is no need to
choose a universal retaining-edge cut order before emission. Known tail cycles already close inside
the reserved group; optional expansion stops before revisiting an active component.

### 5.3 Redirect returns, including fused calls

A member Return either uses the current `returnText` for CExit, or snapshots its used results, assigns
the destination's result locals, and jumps to its fixed label. Return vectors retain their order and
runtime types; no Unit value is invented to fill an empty vector.

**Audit `Emitter:call` as well as `Emitter:returnText`.** The current call/Return fusion emits
`return callee(...)` directly. Inside a locally returning helper that would incorrectly return from
the entire CUnit. Either make fusion destination-aware or disable that Return fusion under local
destinations. Keep safe call/Store fusion and root Return fusion.

Only omit a local return jump when that specific Return physically falls into its destination. The
prototype safely elides the final top-level Return jump for a freshly nested singleton whose join is
immediately outside it. Do not apply that flag to early returns, cyclic groups or inherited destinations.

## 6. Bindings, effects and C scope rules

- Give each non-root context an injective prefix for values, owned storage and expression temporaries.
  Source ids are only unique within their Fn. A raw `v1` from two residual bodies must not alias.
- Resolve module storage through the existing module registry **before** contextual local naming.
  Module objects retain their global identity.
- Keep `Analysis.analyze` facts and `assigned`/`storageAlias` tables local to each emitted context.
  Facts from one copy must not suppress declarations in another copy or arm.
- By-value record/array parameters remain copies. Borrowed parameters receive pointer carriers;
  binding a carrier is not a store through its old referent.
- Evaluate/render arguments in the caller context before installing callee bindings. A C declaration
  such as `uint32_t v1 = v1` can silently self-initialize after shadowing; fresh names avoid that trap.
- On a reused tail entry, snapshot **all** RHS values/addresses before any destination write. Swaps,
  aggregates and overlapping projections cannot be implemented by naive sequential assignments.
- Retain Read snapshots across calls/stores and keep guards before the operations they protect.
  Existing pure-expression sharing does not authorize re-reading a mutable place later.
- A non-tail expanded helper's block is nested inside its caller. The caller's addressable objects
  remain alive while the helper runs; the local return exits only the helper's nested scope.
- A View's existing implicit adapter environment must stay in the owning context's scope. It must not
  acquire a shorter-lived temporary block merely because text is being expanded.

Start with conservative parallel-copy temporaries. Later remove unchanged assignments and break only
actual copy cycles, using alias-aware dependencies. Similarly, remove unneeded labels and root copies
before introducing a new optimization IR to solve cosmetic C output problems.

## 7. Root discovery, ABI and host inlining

A root is a required real C ABI entry: public export/initializer, callback target or remaining direct
call target. Keep all logical signatures available for checking/binding, but emit private bodies only
when the actual residual C needs them.

Reserve a root before compiling its body and drain a deterministic work queue:

```lua
function requireRoot(target)
    if roots[target] then return roots[target] end
    local root = reserveUsingExistingSignature(target)
    roots[target] = root
    queue[#queue + 1] = root
    return root
end
```

Seed exports and initialization. While emitting a component, scan all its member bodies: an ordinary
remaining Call requires its target root; a View requires the code its existing adapter calls. An
internal tail jump does not require a separate target C function. Recursive outline requests find
the reserved root rather than starting another compilation.

Each required entry into a tail component may own a rooted copy. Two exported mutually recursive
entries can therefore have separate ordinary ABI functions, each containing local labels for the
cycle. Accept that duplication rather than introducing an entry-selector runner. Existing public-alias
wrappers and callback adapters may remain initially; removing every wrapper is not this feature's goal.

Do not conflate Wordlet expansion with host inlining:

- preserve the documented meaning of the existing `inline` option;
- introduce a distinct optional residual-expansion credit;
- never rely on either forced host inlining or sibling-call optimization for tail-cycle safety;
- do not force-inline a root participating in a remaining known C-call cycle. The old
  `selfRecursive(fn)` detected only direct self-recursion; production removed it and its cache.

Record actual C-call edges as bodies are built, compute their SCCs before final signature/linkage
rendering, and use plain static linkage for recursive private roots. Body buffers can be wrapped in
signatures after root discovery completes. Opaque calls retain their ABI; do not invent direct targets
or a constant-stack promise for unknown recursion.

## 8. Optional code-growth policy

The policy is deliberately smaller than a general inliner cost model:

1. A root's tail component is mandatory, even when larger than optional credit.
2. Each fresh optional component copy spends its complete base weight before nested expansion.
3. All nested copies spend from the same CUnit credit; never reset it per callee or branch.
4. Refusal emits an ordinary call. An active-component/depth refusal is separate from a size refusal.
5. Root reservation bounds recursive outline discovery. A hard total emitted-node limit may report a
   resource diagnostic; it must never break an internal tail cycle or omit its code.

Count shared expression DAG nodes once per template, but effects as occurrences. Do not recursively
recount a shared pure expression tree exponentially. This is an IR-size proxy, not machine-code bytes
or stack-frame size; large aggregate copies/addressable objects need separate attention in measurements.

For each CUnit:

```text
copied template weight <= mandatory root-component weight + optional credit
```

Production makes credit configurable, defaults it to zero, and validates zero-credit behavior.
A nonzero default remains a separate measurement decision. The desired style is modest helper expansion, not a promise to
inline everything. Compare the existing backend, zero credit, and several small credits on real
programs. Include compile time, emitted/object size, stack storage and runtime. The prototype's greedy
depth-first growth case is a required policy regression, not an example to celebrate.

## 9. Concrete implementation boundaries

| File / anchor | Change |
| --- | --- |
| new `wordlet/tail.lua` | Normalize narrowly proven return transport using existing constructors; index functions; recognize terminal pairs; compute scalar reuse safety, SCCs and base costs. |
| `wordlet/lower.lua`, `newEmitter` | Add context namespace, Unit/Group references and destination; retain existing expression/place lowering. |
| `Emitter:value`, `storage`, `tempName`, `placeC` | Contextual names, with module lookup retaining global identity. Audit raw tuple/adapter temporary names for scope collisions. |
| `Emitter:call` | The three-way lowering in §5; typed parallel input transfer; destination-aware remaining-call fusion. |
| `Emitter:returnText` | CExit versus local result binding/goto, with narrow fall-through elision. |
| `Emitter:statements`, `switch` | Preserve existing control/effect emission; consume only validated Call/Return pairs together; cover local returns inside If/Switch/Loop. |
| `Emitter:makeView` | Preserve environment lifetime and register required callback target roots. |
| `M.bodies`, `M.close` | Prepare/check normalized bodies; reserve actual roots; emit contextual groups; finish linkage after actual call-graph discovery. |
| `M.signatureText`, `selfRecursive` | Use actual root recursion facts for forced-inline eligibility; remove obsolete direct-self-only cache once unused. |
| `wordlet/cabi.lua`, `liveInstances` / `layouts.order` | Separate the conservative logical instance catalog from actual emitted-root order. Keep signatures for non-root component members. Preserve all ABI layout rules. |
| `wordlet/analysis.lua` | Analyse normalized Fn bodies; preserve snapshot, read elimination, expression-sharing and parameter-alias facts. Add only genuinely required analysis APIs. |
| `wordlet/check.lua` | Reuse existing function/program checks for normalized IR; add preparation checks without weakening source verification. |
| `wordlet/init.lua` | Normally unchanged: both compile paths already call Lower.close. If preparation needs a shared helper, invoke it through that common boundary. |
| tests and `bundle-manifest.lua` | Add dedicated tail/contextual tests and the required new module; keep bundle/relocation tests explicit. |

No ASDL constructor change is currently required. Do not delete `Ir.Fn`, Loop/Next, `loopBackCPS`,
`Resolve.tailCalls`, or evaluator `body`/`setup` handling for this implementation. Do not regenerate a
hypothetical new CFG schema from an older version of this document.

The prototype is a reference for mechanics, not code to copy unquestioningly: its SCC implementation,
scalar-only tail recognition, globally disabled host attributes, alias duplication and greedy expansion
order are all explicitly limited. Integrate through owned APIs, not a production monkey patch.

## 10. Implementation sequence and acceptance

Stages 1–5 below are integrated and tested. Stage 6 retains the zero-credit default; real-program
performance tuning and broader lifetime proofs are not implied by correctness acceptance.

1. **Extract tail preparation and contextual naming.** Keep all ordinary calls and existing self loops.
   Verify no source/IR mutation, deterministic output, module identities and existing source diagnostics.
2. **Close direct scalar tail SCCs.** Reserve all entries first, implement parallel copies and maintain
   normal calls for retaining recursion. Test with expansion credit zero and host optimizations disabled.
3. **Normalize common forwarding joins.** Recheck/reanalyse the new ordinary Fn bodies. Test expression
   and statement spellings, nested branches, sums, zero and multiple results, and guarded operations.
4. **Add optional helper copies through the same emitter.** Local destinations must cover early returns,
   nested helpers, loops and call/Return fusion. Keep active-component and depth cuts conservative.
5. **Close only actual roots and finalize linkage.** Exercise exports, aliases, initializer, callbacks,
   foreigns, separate header/source/cdef consumers and remaining mixed-recursion cycles.
6. **Measure and tune, then document the validated guarantee.** Do not broaden the lifetime rule or
   choose a nonzero default solely because the synthetic helper output looks appealing.

Required targeted tests include:

- deep even/odd and a three-entry cycle at zero credit, different input arities, self-tail swaps,
  and multiple required ABI roots; GCC/Clang strict C11 at O0/O2/O3 with a small stack;
- mixed/non-tail recursion retaining its pending values and borrowed objects;
- a tail-looking call with pending cleanup, result work or observable owned storage stays retaining;
- two calls to one helper get distinct local destinations, no runtime return selector and no value-id
  collision; interleaved effects occur exactly once and in source order;
- typed by-value aggregate copies, borrowed receivers, tagged callables, View environments, Unit,
  selected-only lambda elaboration and guard/payload dominance survive expansion;
- malformed preparation facts (wrong result vector, escaping owner, foreign target, wrong component)
  are rejected as compiler bugs instead of producing unchecked gotos;
- growth bounds and deterministic output, including the deliberately unfavorable repeated-helper chain;
- preserved arithmetic, parameter-alias, DAG-sharing and remaining-call fusion quality;
- full distribution/isolation and real SHA-256 acceptance after integration.

Run `timeout --kill-after=2s 180s luajit tests/run.lua` on the implemented compiler and report actual
results and wall time. The earlier prototype corpus is evidence for the mechanism, not certification
of a completed implementation.

## 11. Acceptance question

Can each expansion, jump or remaining call be explained by one of: a safe tail component, a deliberately
chosen local code copy, a required lifetime/ABI/recursion boundary, or an explicit size/depth limit?

**One contextual emitter. Tail cycles are mandatory local control. Small residual bodies may be copied.
Everything else keeps an ordinary call. Lean on the existing compiler and the C optimizer.**
