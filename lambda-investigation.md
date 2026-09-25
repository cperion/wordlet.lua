# Residual accounting and repeated lambda construction

## Scope and status

Implemented: constant-time residual-instance budget accounting and a narrow immediate-static-lambda
execution path that avoids an unused base. The profiler records the cause and the fix.
**No static-result memoization or lambda identity merging is implemented.** First-class lambda
values and residual calls retain checked-base construction.

## 1. Budget accounting

Previously both `instanceForCPS` and `callableInstanceCPS` counted every member of `instances` before
admitting a new key. N reservations therefore performed O(N²) counting work, independently of the
cost of building their bodies.

`Session:registerInstance` now maintains `instanceCount` and appends to the existing discovery order.
Both admission paths read that counter in O(1). This preserves the previous budget meaning:

- reserve before constructing the body, including recursive/building entries;
- a failed reservation remains counted; retrying that key rethrows its original diagnostic;
- cached requests do not increment the count;
- the compiler-owned module initializer keeps its admission exemption but counts in the registry;
- replacing its key does not increment cardinality, even though construction appends to `order`;
- each new Session starts at zero. Limits and defaults are unchanged.

The evaluator suite adds 49 checks for named and closure paths, zero/exact capacities, failures and
retries, initializer replacement, and session isolation. The implementation does not assume that
`#order` always equals map cardinality.

A one-off registry probe requested real bodies of `f(x,k:U32):U32=x+k` with runtime `x` and 16,384
distinct static `k` values: cold wall time was 2.74 s before and 2.08 s after the change. Smaller
samples were nearly unchanged. These are single diagnostic samples, not a general speedup claim;
body construction and GC remain substantial costs. Scratch artifacts are under
`/tmp/wordlet-lambda-investigation/{registry.lua,registry-before.log,registry-after.log}`.

## 2. Reproduce the lambda investigation

```sh
/usr/bin/time -f 'wall=%e s RSS=%M KiB' \
  timeout --kill-after=2s 90s luajit tools/profile-lambdas.lua 5
```

Arguments are maximum fixture count (default 4), key budget (default 65,536), and step budget
(default 10,000,000). Static/build depth is 1024 and interpreter depth is 4096. These are explicit
probe settings, not new compiler defaults. Resource exhaustion reports failure, not a partial answer.

The tool overrides methods on **one owned session**, not the shared evaluator class. It follows the
same parse/load/initialize/export/supply entry sequence as `wordlet.interpret`. Every original method
still runs; no computation, capture, type check, base build or invocation is skipped. Expected values
are asserted, but performance counts are observations rather than tests that require an explosion.
The standalone suite smoke-runs the tool after relocation, from a different working directory.

It reports:

- static invocations of the fixture's recursive word, including those under a Build descriptor;
- lambda definitions by syntax origin;
- callable-instance requests, actual builds and concrete closure invocations separately;
- diagnostic capture/input/environment shapes after removing the fresh lambda-id prefix;
- residual-instance cardinality, evaluator steps and instrumented CPU time.

Shape grouping also retains literal provenance. It is **not a proof that plans are interchangeable**:
it does not establish lexical dependency stability, ownership, aliases or metadata validity.

## 3. Measurements

Three fixtures run at each count:

1. The static-`pc` VM from the known-match regression: three opcode alternatives with lambda handlers.
2. The same concrete transitions written with direct word calls and conditionals, without lambdas.
3. A lambda chain, without any sum or match:

   ```wordlet
   let chain(n:U32):U32 =
     if n==0 then 0 else (|u:Unit|->chain(n-1)+1)(Unit())
   ```

The chain's depth is `2*n+2`, so its logical word-call count matches the VM's `2*n+3` transitions.

Before the immediate-use fix, with constant-time accounting and without memoization:

| VM count | VM word evaluations | under Build | lambda definitions / builds | diagnostic shapes | direct-control evaluations |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 0 | 7 | 4 | 7 | 3 | 3 |
| 1 | 31 | 26 | 31 | 5 | 5 |
| 2 | 127 | 120 | 127 | 7 | 7 |
| 3 | 511 | 502 | 511 | 9 | 9 |
| 4 | 2,047 | 2,036 | 2,047 | 11 | 11 |
| 5 | 8,191 | 8,178 | 8,191 | 13 | 13 |

Every VM lambda definition requested a fresh base and was also invoked concretely once. At count 3,
the step/branch/halt literals were constructed 85/170/256 times, respectively. Their diagnostic shape
counts were 4/4/1. There are only **three lambda syntax nodes** in the source.

The sum-free chain reproduced the same 7/31/127/511/2047/8191 word-evaluation counts. At depth 8 it
constructed and concretely invoked 255 lambdas, from **one syntax node**, with eight diagnostic shapes.
Thus this is not peculiar to sum matching or instruction-array indexing.

All three fixtures returned their expected values. The combined count-0-through-5 probe took
**8.06 s wall time**, peak RSS **94,632 KiB**. At count 5, instrumented CPU times were 3.818 s for the
VM, 0.001585 s for its direct control, and 1.539 s for the chain. Timings include instrumentation;
these are explanatory fixture measurements, not production workload forecasts. Full output is in
`/tmp/wordlet-lambda-investigation/lambdas.log`.

## 4. Mechanism

1. `evalLambdaCPS` captures values and resolves parameter types.
2. It unconditionally allocates a new definition id, puts that id in `plan.key`, and requests a base
   through `callableInstanceCPS` to discover the closure's result signature.
3. `constructCallableInstanceCPS` checks the lambda body under residual construction. In these fixtures,
   captures are known, and the Unit parameter contributes no unknown payload. Calling the recursive
   word therefore folds the remaining suffix while building the base.
4. After construction, `invokeClosureCPS` sees known arguments and captures in a non-residual frame.
   `evaluateClosureStaticallyCPS` evaluates the same lambda body concretely, repeating the suffix.
5. Descendant lambda creation repeats these two paths, each with a new key, so the existing instance
   cache cannot reuse the repeated base requests.

For the observed VM path, each iteration has two recursive handlers, each doubling suffix work:
`T(0)=7`, `T(n)=4*T(n-1)+3`, hence `T(n)=2^(2*n+3)-1` while budgets permit completion. Count 10 would
therefore require **8,388,607** evaluations/handler bases under that recurrence, not merely 23 logical
transitions. This is an extrapolation from the mechanism and measurements, not a completed count-10
run. Exhausting 100,000 keys was evidence of this growth, not evidence that the program diverges.

## 5. Implemented fix: immediate use need not construct an ABI

`prepareLambdaCPS` prepares captures and parameter types but does not check a generic body or claim
its result signature. Its plan is internal compiler data, never a provisional source closure Value.
`completeLambdaCPS` remains the ordinary checked-base path for a first-class callable.

A direct literal call or selected known-match literal, in a non-residual frame, can use the prepared
plan immediately when saturated with known integer/F64/Bool/Unit/string arguments and no runtime or
borrowed captures. It enters the existing closure invocation owner and executes the body once.
No code identity is shared, no result is cached, and no result type is guessed. The invocation checks
its parameters and the actually selected body path. Enclosing result contracts still apply.

Captures/annotations are evaluated at the literal's written position, before argument or subsequent
handler-expression effects. Invocation waits for arguments or match coverage/handler checks. A
borrowed/runtime environment completes its base at the original position. Other ineligible calls
complete a real callable using the already evaluated arguments; they do not replay source.
First-class lambda values and residual calls remain eager, and a repeated bound-lambda construction
can still be expensive. This is deliberately not a general lazy-closure framework.

The integration also checks/copies static closure parameters, isolates numeric parameter/capture
wrappers from in-place coercion, and reuses resolved parameter types rather than evaluating annotation
expressions again. Partial closures use the correct remaining-parameter offset for expectations.

After the fix (same profiler, no memo):

| VM count | evaluations | under Build | prepared definitions | base builds | result |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 3 | 9 | 0 | 9 | 0 | 19 |
| 5 | 13 | 0 | 13 | 0 | 25 |
| 10 | 23 | 0 | 23 | 0 | 40 |

The chain also becomes linear: depth 22 needs 23 word evaluations and no base builds. The combined
count-0-through-10 profile completed in **0.17 s wall time**, peak RSS **5,864 KiB**. VM count 10
used 882 evaluator steps in that probe. Tests independently execute it with **zero residual keys**
and 5,000 steps, and compile its result to constant 40 under default compilation budgets.
The later validation log in VALIDATION.md is authoritative for the final full-suite run.

Regression coverage includes annotation/capture/argument/handler ordering, exact-once local effects,
record parameter copies, numeric retagging, Unit/result vectors, partial/contextual callable inputs,
wrong parameter types, borrow/reference rejection, and unchanged first-class checking. The C corpus
checks both residual credits 0 and 256. General code-template sharing remains separate future work;
the diagnostic shape counts are not a license to merge plans or activation-specific bindings.
