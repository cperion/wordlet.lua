# Static-result memoization: cache completed, effect-free invocations

**Status: deferred design, not an implemented production cache.** The selected work is instead
constant-time key accounting and a targeted immediate-lambda fix; see
[lambda-investigation.md](lambda-investigation.md). That fix runs the static-pc VM `(10,7)` in 23
invocations with no residual bases or memoization. The cache machinery below remains a proposal.

## 1. Decision

Add a bounded, session-local cache of **completed static invocation results**. A hit substitutes a
fresh value snapshot for repeating a computation. It must not substitute a value for an effect,
replay source, change when a call becomes static, or treat a pending computation as a result.

Keep the current CPS evaluator, structured IR, specialization cache and contextual C backend.
Three mechanisms remain distinct:

| Mechanism | Shares |
| --- | --- |
| `instances` | independently elaborated residual bodies for specialization keys |
| proposed static memo | completed values of certified static invocations |
| possible later lambda-template cache | capture-independent construction/checking work |

Large compilation budgets remain legitimate developer choices. Cache capacity is an optimization
budget, not a language limit. Exhausting it evicts or bypasses; it does not reject a program.
Memoization does not promise to make every large or nonterminating computation affordable.

## 2. Findings when this design was written

- Words/methods use `foldOrBuildCPS` and `evaluateStaticallyCPS`. Closures have a separate path through
  `invokeClosureCPS` and `evaluateClosureStaticallyCPS`. Changing only the word path is not full coverage.
- Successful normalization is **not** a purity certificate. A local named word can mutate a concrete
  record in its enclosing lexical scope without a receiver argument and without touching a module.
- `run` and `demanding` are execution permissions, temporarily suspended during instance building.
  They are not purity flags. Initialization and interpretation may memoize pure calls too.
- Scalar `Value` wrappers are mutable implementation objects: `become`/`convert` change their type,
  representation and `literal` flag; `copyArgument` currently aliases scalar wrappers. A cache must
  not keep a live Value or hand the same Value to two callers.
- `V.isStatic`/`V.encode` serve specialization, not memo safety. Known arrays can encode even though
  their contents are mutable. Literal provenance affects coercion, and float equality merges signed
  zeros. Reusing these predicates or encodings unchanged is insufficient.
- A lambda evaluation allocates a fresh definition id and eagerly builds its base instance. This can
  multiply work, but completed **word** results can already cut off repeated construction underneath
  them. We need not globally merge lambda identities to obtain that benefit.
- At design time both residual-key admission paths counted `instances` by scanning the whole map. N reservations do
  O(N²) budget bookkeeping. This has since been fixed with a maintained count, including failed
  reservations and the module initializer accurately, rather than assuming every order-list append
  inserts a new map key.
- `Machine.run` can raise a fuel error outside `Machine.step`'s protected call. Ordinary diagnostic
  handlers alone cannot guarantee cleanup of pending memo entries.

## 3. Evidence: mechanism, not a general purity implementation

Scratch probes wrap the real evaluator, **explicitly trusting only the supplied pure fixtures**.
They do not discover purity and are not production patches:

```
/tmp/wordlet-memo-design.QMjBEg/probe.lua
/tmp/wordlet-memo-design.QMjBEg/results.log
/tmp/wordlet-memo-design.QMjBEg/modes.lua
/tmp/wordlet-memo-design.QMjBEg/modes.log
```

| Fixture | Ordinary evaluations | Memo misses / hits | Result |
| --- | ---: | ---: | ---: |
| `fib(25)` | 242,785 | 26 / 23 | 75,025 |
| `fib(35)` | not attempted without memo | 36 / 33 | 9,227,465 |
| interpreted VM `(3,7)`, mode-partitioned memo | 511 | 17 / 14 | 19 |
| interpreted VM `(10,7)`, mode-partitioned memo | previously exceeded raised budgets | 45 / 42 | 40 |

The VM's residual-instance counts were also 511 without memo at count 3, 17 with partitioned memo
at count 3, and 45 with partitioned memo at count 10. The VM probes used static/build depth 1024,
interpretation depth 4096, 4096 keys and ten million steps. No depth limit was removed.

The full instrumented probe took **9.96 s** wall time; the additional mode-partitioned probe took
**0.28 s**. Per-fixture CPU times are in the logs. These are experimental measurements, not promised
production speedups: instrumentation itself adds overhead to the uncached baseline.

Two deliberately unsafe applications of that same cache produced wrong results:

- module getter called before and after a store: **0 instead of 7**;
- nullary local helper mutating an enclosing record during normalization: **11 instead of 12**.

The probes also confirmed scalar wrapper aliasing and in-place coercion. These failures determine
the safety boundary; a successful Fibonacci demo alone is not acceptance.

## 4. First safe value boundary

Before enabling hits, establish consistent by-value behavior **with memo both on and off**:

1. Clone admissible scalar argument wrappers before parameter coercion/binding.
2. Audit scalar binding reads/captures so coercing a fetched value cannot mutate an ambient binding.
3. Return fresh admissible scalar wrappers at the static-call boundary on misses as well as hits.
4. Snapshot after result-contract checks, preserving type and literal provenance.

Do not broadly replace mutable places or pretend records/references are scalar values. Isolate these
changes and test their aliasing/coercion semantics independently. If a remaining mutation route cannot
be proved isolated, affected calls must bypass memoization; silently changing semantics only on hits
is not an acceptable shortcut.

Initial key/result data: integer atoms with exact widths and high/low words, bool, unit, f64 other
than NaN, immutable strings, and complete logical result vectors of these. Preserve explicit unit
positions. Distinguish `+0.0`/`-0.0`; encode infinities explicitly. Finite double encodings must round
trip exactly. NaNs bypass initially rather than collapsing payload/sign distinctions.

Use a memo-specific freeze/key/thaw codec. Include `literal` metadata and reject unexpected value
shapes. Keys are unambiguous typed, length-delimited data, never concatenated unescaped fragments.
Thaw creates new Values; cached payloads expose no mutable Value tables, IR ids, places or builders.
Code and sealed type identities may be represented in **keys/dependencies**, not returned as cached
callables or type-producing results in the initial implementation.

No new AST/IR variant is needed. Cache records are session bookkeeping like Frame/Instance; semantic
types remain the existing Ty descriptors and returned values use existing Value constructors.

## 5. Invocation identity and lookup point

A candidate key contains:

```
execution partition: entry-time (run, demanding) flags; keep interpreter initialization distinct
callable identity: existing word/closure definition identity, not its printed name
validated logical argument vector, including previously bound arguments
fixed keyed supplies and, for eligible closures, explicit closed capture snapshots
resolved parameter/result contract fingerprint
```

Keep partitions initially. Stronger cross-mode reuse is a separate proof, not a prerequisite: the
mode-partitioned VM probe still eliminates the explosion.

Preserve written-order callee/argument evaluation and saturation. A hit cannot skip argument effects.
Start a bounded observation guard at the invocation boundary, before preparing its private scope;
reserve a keyed pending entry only after preparation succeeds. Prepare and validate before lookup:
argument adjustment, requirements, coercion and result-contract resolution still run in the current
context. Include preparation observations conservatively in the certificate, and propagate them even
on a hit. Unify the validated static boundary
where practical; do not assume direct match/defer/closure supply has traversed an expression-call
validator. Closure parameter types already resolved on the plan should not be evaluated from source
again just to form a key.

Use existing identities first. Fresh ids can cause misses but not incorrect sharing. Do not replace
`def.id` with a source span or AST pointer alone: lexical bindings, inferred signatures, static
supplies and captures can differ. A later lambda-template design must retain those distinctions.

## 6. Purity belongs to an actual execution

Use a conservative **execution certificate**, collected while the existing evaluator runs a miss.
Do not elaborate an unselected branch to prove it pure. Do not infer purity from a successful fold,
a scalar return, a known code identity, or an absence of explicit arguments.

Each candidate accumulates:

- immutable ambient binding/type/code dependencies;
- a summary of concrete storage it accessed;
- opaque/unsupported operations or incomplete validation;
- its completed, checked, encodable result.

Every reachable evaluator route must either implement its observation contract or veto publication.
Unknown semantic operations fail closed to ordinary execution, not to a new source rejection. Keep
this policy in explicit semantic visitors/hooks, not ASDL class methods or a replay interpreter.

### 6.1 Ambient dependencies

Reading a parameter or local value computed inside the candidate needs no ambient dependency.
Reading an outside immutable binding records its identity/resolution and frozen semantic value.
Reading an outside record/array is a storage dependency, not an immutable binding certificate.

Keep one current entry per candidate key, not an unbounded history of environmental versions.
A ready entry carries probes for its observed ambient dependencies. A hit validates them by inspecting
existing compiler bindings, **without demanding a binding or evaluating source**. A changed, missing,
unready, shadowed or unencodable dependency is a miss. Record lookup provenance, not merely the old
slot: a newly introduced nearer binding must invalidate a previous resolution. Open type cells are
not stable dependencies; observe sealed meanings or bypass. Discard an invalid certificate before
reserving its replacement, rather than treating it as a permanently cached failure.

A parent must inherit a child's ambient dependencies on both execution and cache-hit paths. Drop
only dependencies proven private to the parent evaluation; do not leak the previous invocation's
parameter scopes into its certificate. Bound dependency count and validation work. If the certificate
would grow too large, bypass that entry rather than perform unbounded key/environment traversal.

Use weak identity registries for transient scopes/slots where necessary. A collected dependency
causes a miss. Cache entries must not retain a huge enclosing frame merely to remember one scalar.

### 6.2 Concrete storage and local mutation

The first enabled slice may veto all concrete storage accesses. Extend it explicitly to private
allocation, needed for useful compile-time programs and the VM fixture's local instruction arrays.

Give tracked allocations and candidate starts session-local monotonically ordered birth tokens.
An object actually allocated after candidate entry can be private to that invocation. Creating a
new wrapper for module storage, a borrowed object or an existing place does **not** create ownership.
Track actual touched targets, including nested aggregates; a shallow copy does not make its children
private. Untracked targets and reference/pointer/view routes initially veto publication.

A candidate may mutate its own fresh record/array and return an atom. It may not read/write storage
that predates it, even if a store writes back the same value. Publishing private state into an older
object or an ambient binding is an ambient write and vetoes the candidate. Module storage is always
ambient, even when its initializer allocated it after candidate entry.

This classification is relative to the candidate. The nullary mutating helper is not cacheable, but
its caller that allocated the record can still be pure as a whole. Do not taint all ancestors just
because an inner invocation touches its caller's private object.

Implement transitive summaries bottom-up: for supported storage operations, record the oldest birth
touched; merge minima plus explicit unknown/opaque flags at return/unwind. Compare each candidate's
summary against **its own** checkpoint. This avoids scanning every active frame on every store.
A pure cache hit has no ambient storage effects to replay; never merge obsolete allocation ids from
its earlier execution. Fresh returned aggregates are a later codec/ownership extension, not part of
initial result caching.

### 6.3 Compiler work versus source execution

A residual Store emitted while building a closure is not an executed store. Conversely, a concrete
helper invoked during that build can execute and its observations must not disappear behind the
build boundary. Beginning an unfinished initializer vetoes publication by already-active candidates;
it must not be omitted as incidental compiler work. Pure calls started inside that initializer may
still obtain their own certificates. Actual state effects count wherever they occur.

Allowing successful lambda/base construction inside a memoized computation is an explicit second
acceptance gate. Audit validation dependencies, actual nested static execution and retained compiler
artifacts. Unreferenced code registration may be skipped on a later hit only when no code/type/place
escapes through the cached result and its checking assumptions remain valid. Unresolved metadata,
unsupported construction or a caught validation/fold failure vetoes publication initially.

Until this gate is implemented, bypass candidates containing such construction and report the reason.
Do not claim the production VM benefit from a scalar-only Fibonacci implementation. The trusted VM
probe proves that completed word-result caching can avoid repeated lambda construction; it does not
prove that arbitrary construction is safe to omit.

## 7. Cache state and cleanup

```
absent -> pending(owner) -> ready(snapshot, certificate)
                        -> absent on failure, veto, or capacity refusal
```

- Publish only after normal completion, deferred work, result checking and snapshot creation.
- A pending entry is not a value, success, failure or proof of divergence. Re-entry bypasses the cache
  and follows existing evaluation/fallback limits. It must not replace the owner's entry. A nullary
  stateful recursion can legitimately revisit the same argument key and then terminate.
- Do not cache diagnostics, runtime-permission refusals, resource failures or partial results.
- Merge observations of unsuccessful inner work before any existing handler resumes a continuation.
- Attach memo ownership/cleanup to the control core without increasing semantic depth just for memo
  bookkeeping. Cleanup runs once on success and all abort routes, including fuel errors outside
  `Machine.step`, non-Diagnostic Lua errors, and swallowed fold diagnostics.
- A run-level cleanup boundary can restore the memo checkpoint with one fixed protected frame. It
  must not execute source handlers while cleaning an aborted run or add a `pcall` per recursive call.
- Pure completed children may remain cached after a parent fails. Pending state must never survive
  as a poisoned hit. This does not promise recovery of an otherwise invalid Session after a raw bug.

Hit lookup/validation/thaw costs count as actual work. Do not charge the original computation's fuel
again, and do not reset cumulative work counters. Keep existing invocation-depth accounting initially,
including preparation: type/contract evaluation itself can recurse. A hit avoids executing the body;
it does not waive validation limits or add a second counted frame for memo bookkeeping.

## 8. Capacity, lifetime and observability

Proposed API: `staticMemo = true | false`; initial implementation opt-in until acceptance, then
consider enabling by default. Preserve an off switch for differential testing and troubleshooting.

Proposed starting cache limits (not compilation limits):

- `limits.memoEntries = 65536` total pending plus ready entries;
- `limits.memoBytes = 16777216` accounted key/snapshot/certificate bytes and bookkeeping weight;
- `limits.memoKeyBytes = 65536` per key;
- `limits.memoDependencies = 256` per certificate.

These values are tunable starting policies, not measured optima or a bound on total Lua RSS. Include
pending keys and growing certificates in byte accounting; proof overflow vetoes publication and stops
retaining observations, while preserving conservative summary/cleanup state. Bound snapshot size too.
Oversized keys/results and saturated pending admission
bypass. Evict ready entries with deterministic O(1) LRU bookkeeping; never evict an active owner's
pending record. Do not retain unbounded purity histories or negative-cache every unique failure.

The cache is owned by one Session, never by process-global ASDL state. Clear entries/identity
registries at the completed evaluation lifecycle boundary; retain aggregate statistics, not caller
frames. The exact facade cleanup point must follow the last evaluator consumer, not an arbitrary
individual export: sharing across exports and initializer demands in one session is useful.

Counters should expose requests, hits, misses/body evaluations, active-key bypasses, veto reasons,
evictions, current/peak accounted size and residual instance reservations. Count creation by lambda
syntax origin for investigation, without merging its actual identities. No unbounded event log.

## 9. Acceptance and implementation order

1. **Instrument and repair accounting.** Constant-time residual-key count, typed-call/definition-origin
   counters, reproducible cold/warm cases. No caching yet.
2. **Establish snapshot/validation boundaries.** Scalar aliasing, literal provenance, fresh results,
   complete contracts and codec limits tested with memo off.
3. **Implement certificates and control cleanup.** All binding/read/write shortcuts and builtin paths
   audited; unsupported operations bypass. Test transitive dependencies and all abort routes.
4. **Add bounded word-result memo.** Scalar functional core first, enabled explicitly. `fib(25)` must
   have roughly 26 body evaluations, not merely pass because limits increased.
5. **Support private data, closure execution and validated construction.** Keep one certificate model;
   pass the static-pc VM with mode partitioning, without globally canonicalizing lambda plans.
6. **Validate broadly, then choose the default.** On/off results, effects and diagnostics agree except
   deliberately different resource consumption. Full compiler/C/distribution tests at residual credits
   0 and 256; GCC/Clang low-stack tail tests. Measure time, allocations, instance counts and cache size.

Files: new `wordlet/memo.lua` for codec/cache/certificates; `session.lua` for ownership/configuration;
`eval.lua` for validated static entry and semantic observations; `machine.lua` for cleanup; appropriate
Value helpers for atom isolation; focused tests plus `bundle-manifest.lua` and isolation registration.
No backend purity inference or static-result lookup from C emission.

Required adversarial tests include:

- Fibonacci and repeated calls across exports and initializer demands;
- module reads/writes, same-value stores, local captured mutation and transitive helper effects;
- a hit on a pure child cannot hide a dependency from its parent;
- private mutation allowed only relative to the correct owning candidate, including shallow aliases;
- ambient shadowing, changed callable captures, keyed supplies, module identity and type-cell sealing;
- integer widths, literal adoption, signed zero, infinities, NaN bypass, strings and unit vectors;
- mutating a returned Value cannot corrupt another return or the cache, with memo on and off;
- selected-only handlers, closure base construction and constructor validation failures;
- same-key stateful recursion, pure active recursion, decreasing recursion and all resource failures;
- eviction, zero capacity, oversized inputs/certificates, GC of transient dependencies, session reuse
  boundaries, deterministic cold runs and a genuinely memo-disabled comparison.

**Success is fewer repeated evaluations with the same answers and effects—not bigger limits disguised
as memoization, and not a fast cache that accidentally turns mutable state into constants.**
