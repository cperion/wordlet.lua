# Validation contract

## Checks that run now

```
timeout --kill-after=2s 30s luajit tests/run.lua
```

The runner verifies ASDL interning/type checks, non-interned occurrences, actual copied-method
behavior, corrected List equality selectors, and concrete U32 arithmetic against edge cases and an
independent bit-serial multiplication reference. It copies this project's declared files to a
temporary path containing spaces and a quote, then builds there from another working directory.
It compares repeated bundle bytes and loads the bundle with Lua search paths cleared. Fixture modules
exercise real require-mode embedding, optional CLI dispatch, private package.loaded compatibility,
failed-load retry, cycles, unlisted dependencies, missing/syntactically invalid source and write errors.
The runner cleans its temporary directory and reports failures with nonzero exit status.

These are bootstrap tests, not Wordlet compiler tests. No parser/evaluator/C correctness claim follows
from a passing bundle or ASDL constructor check. Tests need POSIX tools; they are not a sandbox for
untrusted module source or manifest code.

## Source fixtures (not executable yet)

- examples/arithmetic.let: transform(4)=19; divmod(17,5)=(3,2); consume(17,5)=17. Unknown zero
  divisor aborts; statically evaluating a zero divisor rejects.
- examples/receivers.let: observe(7,false)=(7,7); observe(7,true)=(7,8). The first result must
  remain a snapshot despite the method call. At U32 maximum, increment wraps to zero.
- examples/captures.let: run(5,7)=12. An exported make_adder result must remain callable after
  its creator returns and copy its captured value by value.
- examples/arrays.let: literal_sum()=60, local_pick(2)=9, store(1,4)=643, grid(1,0)=3, via_parameter(5)=11,
  aliased(3)=99099. A literal takes its type from its elements or an annotation, a known index is
  checked while compiling, a run-time index is guarded, and a local binding aliases while a pass,
  return or field store copies.
- examples/references.let: read_shared(1)=6, bump_shared(1)=7, borrowed(2)=55, following()=10,
  bump_following()=15. A reference to module storage persists a store; a reference to a captured
  record is live for the caller; a recursive Node/Link reaches and mutates its neighbour through a
  stored reference.
- examples/tagged.let: pick(true)=11, pick(false)=9, scaled(true,5)=11, scaled(false,5)=4,
  across(true,4)=5, across(false,4)=12. Two words, two lambdas that capture, and a tagged callable
  returned from a call all dispatch on the tag without a function pointer.
- examples/sums.let: area_of_circle(5)=25, area_of_round(6)=36, area_of_box(4)=12, scaled(3)=36,
  total(0)=6, total(4)=16, unwrap_or(0,9)=9, unwrap_or(4,9)=4. A known alternative resolves its
  match while compiling; a run-time alternative becomes a C tag test; a Unit alternative carries no
  payload and its handler takes no C argument.

## Implementation gates for the owned-syntax compiler

Each gate needs executable positive and negative cases. No gate means “keep an old suite green.”

Gates 1–5 and 9–11 have their first executable form in `tests/parse.lua`, `tests/eval.lua` and
`tests/c.lua`. Gate 6 is partial (no bounded changing-specialization growth check yet).

1. **Concrete schemas:** `ast.asdl`/`ir.asdl` parse and construct (tests/schemas.lua); stable source
   spans; every semantic visitor covers every AST/IR variant; immutable canonical lists; no effect
   occurrence interning; builder-level per-function expression interning.
2. **Grammar:** free-form equivalence, comments/tokens, operator precedence, `:` results versus `->` lambda bodies, parenthesized signature inputs,
   named/shared parameters, per-binding annotations, schemas/initializers/configuration, separators.
3. **Interpreter:** U32 rules, Bool-only short circuit, exact application adjustment, static partial
   supply, Type-dependent requirements, lexical scope and lazy top-level dependencies.
4. **Storage:** immutable bindings versus mutable fields, immediate reads, record value copies,
   compound-target evaluation once, receiver effects through calls and actual nested owner routes.
5. **Structured branches:** each arm elaborated once, correct early-return completion, result-vector
   joins, initialization on every continuing arm, no arm-local definitions leaked outside scope.
6. **Instances:** canonical known argument/code/capture bindings, shared helper bodies, no caller path
   multiplication, bounded changing-specialization recursion and complete annotated residual cycles.
7. **Sums:** `OneOf(schema)` builds one canonical sum; member selection constructs an alternative by
   keyed supply, positionally for a non-record payload, or with no value for `Unit`; matching requires
   exactly one callable handler per alternative, all with the same result type. A known tag elaborates
   only its own handler; an opaque tag emits a tag test per alternative with the payload projected
   inside the arm. C lowers to a tag plus a union and a `Unit` parameter is erased. Non-schema cases,
   an empty schema, unknown alternatives, missing or duplicated handlers, unknown payload fields and
   disagreeing arm types all reject.
8. **Callables:** a callable that borrows (a closure over a receiver, or a method value) crosses a
   callable parameter as a non-retaining view whose adapter holds the borrowed place, pure code
   crosses as a null-environment view, and each still agrees with the interpreter. ** two callables of one signature chosen at run time join into a tagged callable and
   dispatch on its tag; a multi-result tagged call and one crossing a call boundary agree with the
   interpreter; mismatched signatures, a borrowing arm, an undeclared word arm and erasure into a
   signature all reject. owned environments survive creator return (make_adder/run/compose/snap); a captured
   field is a snapshot while a captured receiver is a live borrow; distinct lambdas are distinct code
   identities; escaping a borrowed closure is rejected; an opaque callable uses a signature-specific
   invocation pointer, and a callable with no known code and no view is rejected rather than
   mis-compiled.
8b. **References and recursion (implemented):** reference construction from a module binding and from
   an enclosing owner, selection, store and aliasing through a reference, both lifetime rejections
   (`ref-target` for a local, a copy or a temporary; `ref-escape` for a reference to an enclosing
   owner that escapes), a recursive Node/Link list over module storage built and traversed with a
   mutation seen through a stored reference, and by-value cycles rejected across one and several
   definitions (`type-cycle`) while a cycle through a reference is accepted with a finite
   forward-declared layout. A reference is also a parameter, a result and a field: a host may pass a
   pointer for `Ref(T)`, a reference to module storage may be returned from a call and followed, and
   a tied reference held in a local record reaches the enclosing instance.
8c. **Arrays (implemented):** a literal with an inferred element type and an annotated one, a static
   index, a run-time index with its guard (the guard aborts, asserted in C), element stores, nested
   arrays, an array parameter (a copy) and a local alias (not a copy), an array result compared
   element by element, a pool of nodes in module storage reached by `Ref(pool[i])`, and the
   rejections `type-required` for an empty literal, `array-length`, `type-mismatch`, `index-range`
   and `not-a-place`.
8d. **Integer widths (implemented):** `U8`/`U16` literals by annotation, wrapping arithmetic at the
   named width (compared against the interpreter and the generated C), implicit widening, a literal
   adopting a narrower operand, mixed run-time widths widening, a checked conversion that rejects a
   known value out of range and aborts a run-time one, a non-integer conversion rejected, and the
   rejections `numeric-range` for an out-of-range annotation or conversion.
8e. **Imports (implemented):** a two-file program compiled through `compile_file` and run from C, an
   imported type used as an annotation and as a keyed supply, a name the module does not export
   (`unknown-member`), a missing file (`import-input`), a cycle (`import-cycle`), and a source string
   that tries to use an import.
8f. **Signed integers (implemented):** `I32` wrapping, truncating division with the remainder taking
   the dividend's sign, an arithmetic shift, negation, a reinterpreting signedness change, a
   literal adapting to a signed operand, the `int32_t` representation and the reinterpretation helper,
   and the rejections `type-mismatch` for mixing signed and unsigned and `numeric-range` for a
   negative value narrowed to an unsigned type or a negative signed power.
8g. **64-bit integers (implemented):** the exact kernel's own checks, then 64-bit literals (`0xFFFFFFFFFFFFFFFF`
   and a decimal one), widening, narrowing (rejected when known and trapped at run time), products
   that need both words, division and remainder of a signed value, a shift into the high word, and a
   `numeric-range` rejection for a known value that does not fit. The differential case compares all
   of it against the interpreter.
9. **IR/checking:** storage/value distinction, scope and definite assignment, target signature checks,
   module storage seeded outside every function,
   dynamic failure guards, transitive borrow provenance, finite layouts, no metadata runtime slots.
10. **C:** strict C11 compile/run, arithmetic boundary values, side-effect order, safe tail permutations,
   constant-stack self-tails (5,000,000 iterations),
   no dangling environment, separate header/source consumer, stable names and Unit erasure.
11. **Distribution:** replace wordletkit with the REAL facade/CLI in the manifest; bundle parity with the
    checkout implementation; clean relocated builds and runtime execution without source search paths.

The reference interpreter describes aggregate results too: a record as its field map, a sum
alternative as its canonical tag index plus payload, and a reference as the target it names, with a
depth guard for a structure that points back at itself. The C harness therefore compares aggregate
results field by field instead of only comparing scalars. Use concrete interpreter behavior and
generated C on the same programs, comparing returned vectors AND ordered state changes. Retain IR structure tests for invariants, not arbitrary temporary spelling.
Use bounded compiler/execution subprocesses and report wall-clock time. A static interpreter work
budget counts work even when no residual instruction is emitted.

## Initial resource settings to implement

These are explicit starting configuration defaults, not measured limits or language type rules:
source size 16 MiB per file; lexical tokens 1,000,000 per file; static depth 64; static evaluator
steps 1,000,000 per root demand; source/AST nesting 256; residual
statements 100,000 per instance; residual body keys 1,024 per program; aggregate depth 64 and expanded
components 1,000,000 per value. Keep counters cumulative across dependent work in the corresponding
root scope; retries must not reset the counter that is supposed to bound them. Limit exhaustion is a
resource diagnostic naming the scope. There is no exponential replay-path counter.

Diagnostic status convention for the new CLI: reject=1, bug=2, todo=3, resource=4, internal=2.
Compiler bugs and unexpected implementation exceptions are not mislabeled as user type failures.
Every source diagnostic carries a span; source-independent loader/I/O failures identify their path.

## Standalone audit

All active documentation links and source require paths must resolve inside this directory, except
explicit host tools/external modules. Historical origins in THIRD_PARTY.md are informational only.
Do not import the old evaluator, borrow checker, schemas or tests by relative parent path. Preserve
the verified MIT notices in LICENSE and vendor/LICENSE. Tests check that the default bundle embeds
both, so attribution survives standalone distribution.
