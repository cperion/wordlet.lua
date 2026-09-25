# Validation contract

## Checks that run now

```
timeout --kill-after=2s 180s luajit tests/run.lua
```

The runner verifies ASDL interning/type checks, non-interned occurrences, actual copied-method
behavior, corrected List equality selectors, and concrete u32 arithmetic against edge cases and an
independent bit-serial multiplication reference. It copies this project's declared files to a
temporary path containing spaces and a quote, then builds there from another working directory.
It compares repeated bundle bytes, checks that the generated ASDL and syntax-reference modules match
their sources (`tools/embed.lua --check`), and loads the bundle with Lua search paths cleared. Fixture modules
exercise real require-mode embedding, optional CLI dispatch, private package.loaded compatibility,
failed-load retry, cycles, unlisted dependencies, missing/syntactically invalid source and write errors.
The runner cleans its temporary directory and reports failures with nonzero exit status.

The same command then runs the compiler suites in order: `tests/schemas.lua` (AST/IR schemas),
`tests/u64.lua` (the exact 64-bit kernel), `tests/parse.lua` (lexer/parser), `tests/eval.lua`
(evaluator semantics) and `tests/c.lua` (interpreter/C differential, compiling and running the
generated C11 under `-Wall -Wextra -Werror -O2` with residual expansion credit 0 and 256),
`tests/contextual.lua` (contextual lowering and bounded tail-stack tests), `tests/sha256.lua` (real
SHA-256 acceptance), and `tests/jit.lua` (the LuaJIT FFI front end, which
builds and loads an artifact with the host compiler). A failure in any suite stops the run, so a passing
bundle or ASDL constructor check alone is not a parser/evaluator/C correctness claim; the compiler
suites are what make that claim. Tests need POSIX tools and a C11 compiler; they are not a sandbox
for untrusted module source or manifest code.

## The primitive vocabulary is lowercase and reserved

Wordlet spells its own words in lowercase and has no second, capitalized spelling of any: the
primitive types `u8`, `u16`, `u32`, `u64`, `i32`, `i64`, `f64`, `bool`, `unit` and `type`, the byte
slice `string`, and the type constructors `oneof`, `ref`, `array`, `slice`, `ptr` and `null`. Those
names live in `ir.asdl`'s `Ty` module, so `S.encode`/`S.display` -- and therefore every diagnostic --
print the same spelling the source writes. Program-defined names are lowercase `snake_case`
(`GUIDE.md` section 3); capitalization carries no category in either direction.

A module-level `let`, `extern` or word declaration may not bind a predefined word (`reserved`,
`wordlet/eval.lua`); a local binding may shadow one like any outer name. `oneof` takes its keyed
schema directly -- `oneof { a: u32 }` -- and the parenthesized form `oneof({ a: u32 })` remains the
spelling for a schema held in an expression.

Checked by the full suite: `examples/*.let`, `tests/eval.lua`, `tests/parse.lua`, `tests/c.lua`,
`tests/contextual.lua` and `tests/sha256.lua` all use the lowercase vocabulary, and the C corpus
compiles and runs the renamed examples at credits 0 and 256 under GCC and Clang. This is a surface
spelling change: it removes no capability and changes no generated code beyond identifiers.

## Contextual C acceptance

`tests/contextual.lua` compiles/runs production C at `-O0`, `-O2` and `-O3`, with
`-fno-inline -fno-optimize-sibling-calls -DWORDLET_NO_FORCED_INLINE`, strict C11 warnings and a
**256 KiB stack**, at optional residual credits **0 and 256**. Run with `CC=clang` to repeat the
matrix under Clang; the default `cc` on the validation host is GCC. Normal host attributes are also
compiled to check mixed-recursive linkage.

The five-million-step witnesses include scalar mutual tails, nested diamonds, heterogeneous
three-member swaps, expression/statement tuple results, and nullary unit cycles driven both by a
foreign function and by mutable module state. A static-`pc` dispatch regression includes selected
lambda-handler instances in its tail cycle. Existing self-tail loops are checked independently.
Additional cases cover borrowed receivers and cleanup that must retain calls; foreign/opaque/local
and discarded returns; erased unit components; exact-once vector-branch effects; signed zeros;
module-reading/mutating closures constructed without executing their bodies; aliases, imports and
separate headers; runtime aborts, template immutability, deterministic output, a 12,000-node SCC
stress case and expansion/total-size limits. The evaluator suite also checks vector arity/type errors
and initialization/interpreter permissions. Known-match regressions cover dead lambda bodies,
captures and annotations; per-occurrence selection; opaque-arm checking; missing/duplicate/unknown
alternatives; and the unchanged evaluation of non-lambda handler expressions. C tests also check
unused sum boxes without losing payload effects.

Production validation on GCC 13.3 / Clang 18.1:

- Full `tests/run.lua`: **PASS, 55.62 s** (peak RSS 167,580 KiB); evaluator 795 checks, C
  differential/distribution 1407 checks across 43 programs, contextual 5115 checks, plus
  schema/parser/kernel, SHA-256, JIT and isolated deterministic distribution acceptance.
- `CC=clang luajit tests/contextual.lua`: **PASS, 5115 checks, 3.46 s**.
- `CC=clang luajit tests/c.lua`: **PASS, 1407 checks / 43 programs, 24.71 s**.
- An additional static-`pc`/known-match/payload-effect witness passed **12 compile/run combinations
  in 1.89 s**: GCC, Clang and tcc, C99/C11, credits 0/256, five million iterations on a 256 KiB stack.
  GCC/Clang used `-O0 -fno-inline -fno-optimize-sibling-calls -Wall -Wextra -Wpedantic -Werror`;
  tcc used `-Wall -Werror` without unsupported GCC warning/optimization flags.

These are validation wall times, not benchmark speedups.

The guarantee is only for recognized safe tail components. Unproved aggregate/borrowed ownership
and remaining opaque or non-tail recursion retain ordinary calls. Nonzero residual credit is an
optional code-size policy, not evidence of a general speedup.

Static-call memoization remains unimplemented and no result is cached anywhere. What changed is
narrower: a saturated immediate literal call, and a selected known-match literal handler, in a
non-residual frame, prepare captures and parameter types and then execute the body once instead of
first building an unused generic base and folding the same suffix twice. Ineligible uses (borrowed or
runtime environment, aggregate argument, partial supply, first-class value, residual call) still
complete a checked callable. The static-`pc` VM therefore interprets counts 0, 1, 3, 10 and 100 and
folds `run(10,7)` to a constant under default budgets; the evaluator test runs count 10 with
`keys=0` and `steps=5000`, and `tools/profile-lambdas.lua 10` reports 23 lambda definitions and **0**
base builds in 0.17 s wall time (peak RSS 5,864 KiB). Repeating a *bound* closure construction can
still be expensive. Deep-run acceptance remains compiled C, not a claim that every fully static
interpreter invocation is now cheap.

## Source examples (executable)

Each bullet is the reference-interpreter oracle for that `examples/*.let` file. `tests/c.lua` and
`tests/eval.lua` exercise the same shapes, and `luajit dist/wordlet.lua --check FILE.let` type-checks
one directly.

- examples/arithmetic.let: transform(4)=19; divmod(17,5)=(3,2); consume(17,5)=17. Unknown zero
  divisor aborts; statically evaluating a zero divisor rejects.
- examples/receivers.let: observe(7,false)=(7,7); observe(7,true)=(7,8). The first result must
  remain a snapshot despite the method call. At u32 maximum, increment wraps to zero.
- examples/captures.let: run(5,7)=12. An exported make_adder result must remain callable after
  its creator returns and copy its captured value by value.
- examples/arrays.let: literal_sum()=60, local_pick(2)=9, store(1,4)=643, grid(1,0)=3, via_parameter(5)=11,
  aliased(3)=99099. A literal takes its type from its elements or an annotation, a known index is
  checked while compiling, a run-time index is guarded, and a local binding aliases while a pass,
  return or field store copies.
- examples/strings.let: byte_at("A",0)=65, length_of("hello")=5, count_a("banana",0)=3, same()=true,
  different()=false, escaped()=4, empty_length()=0, grouped()=1000170, banner_length()=13,
  banner_first()=102, banner_is_raw()=4, module_view(1)=20, sliced_sum()=60. A string is a byte
  slice, so `==` compares content; a byte literal is a numeric literal; a long string is raw and may
  span lines; a view of module storage may be returned while a view of a local rejects; and a slice
  parameter's length is only known while it runs. `tests/eval.lua` reads this file and asserts every
  value listed here, so this bullet is executable rather than prose.
- examples/dispatch.let: main()=7. A small stack machine: an opcode is one alternative of a sum, a
  step decodes it with an exhaustive keyed match whose handlers return the next machine, and one
  tail self-call drives the loop. Because the recursive call is the loop word's own body it lowers
  to a back edge (`for (;;) { ... continue; }`), not a call, so dispatch is constant stack; a handler
  that called the loop would be a different code instance and would grow the stack one frame per
  step. `tests/eval.lua` asserts the value and that the loop, not a call, survives.
- examples/interpreter.let: main()=7. The same dispatch with the hot state as the loop's parameters
  (`ptr(Op)` code, `pc`, `ptr(u32)` stack, `sp`) instead of a record, so a step copies no aggregate.
  Handlers return the transition (next pc, next sp, done) and `run` tail-calls itself outside the
  match, which is the only self-call. `tests/c.lua` compiles and runs it, since a `ptr` exists only
  in compiled code.
- examples/pipeline.let: settle(1,50)=50, settle(0,50)=0, settle(1,500)=0, summarize(1,50)=50,
  summarize(1,500)=0. Hierarchical continuation wiring: a parent owns a stateful record and composes
  a child that is a method on it; the child's only exits are the callable requirements the parent
  supplies. `settle` supplies exits that yield a scalar, `evaluate` returns the outcome as a sum, and
  `summarize` dispatches it — the downward and upward duals of the same child, separated by the
  `R: type` parameter. `tests/eval.lua` asserts every value listed here.
- examples/references.let: read_shared(1)=6, bump_shared(1)=7, borrowed(2)=55, following()=10,
  bump_following()=15. A reference to module storage persists a store; a reference to a captured
  record is live for the caller; a recursive Node/Link reaches and mutates its neighbour through a
  stored reference.
- examples/tagged.let: pick(true)=11, pick(false)=9, scaled(true,5)=11, scaled(false,5)=4,
  across(true,4)=5, across(false,4)=12. Two words, two lambdas that capture, and a tagged callable
  returned from a call all dispatch on the tag without a function pointer.
- examples/sums.let: area_of_circle(5)=25, area_of_round(6)=36, area_of_box(4)=12, scaled(3)=36,
  total(0)=6, total(4)=16, unwrap_or(0,9)=9, unwrap_or(4,9)=4. A known alternative resolves its
  match while compiling; a run-time alternative becomes a C tag test; a unit alternative carries no
  payload and its handler takes no C argument.
- examples/sha256.let: a real program. `abc()` equals the published SHA-256("abc") digest
  `ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad`, and `digest_seed(x)` agrees
  with the interpreter for a runtime `x`. `tests/sha256.lua` checks the interpreter, the generated C
  and the published vector together.

## Implementation gates for the owned-syntax compiler

Each gate needs executable positive and negative cases. No gate means “keep an old suite green.”

Gates 1–5 and 9–11 have their first executable form in `tests/parse.lua`, `tests/eval.lua` and
`tests/c.lua`. Gate 6 is partial (no bounded changing-specialization growth check yet).

1. **Concrete schemas:** `ast.asdl`/`ir.asdl` parse and construct (tests/schemas.lua); stable source
   spans; every semantic visitor covers every AST/IR variant; immutable canonical lists; no effect
   occurrence interning; builder-level per-function expression interning.
2. **Grammar:** free-form equivalence, comments/tokens, operator precedence, `:` results versus `->` lambda bodies, parenthesized signature inputs,
   named/shared parameters, per-binding annotations, schemas/initializers/configuration, separators.
3. **Interpreter:** u32 rules, bool-only short circuit, exact application adjustment, static partial
   supply, type-dependent requirements, lexical scope and lazy top-level dependencies.
4. **Storage:** immutable bindings versus mutable fields, immediate reads, record value copies,
   compound-target evaluation once, receiver effects through calls and actual nested owner routes.
5. **Structured branches:** each arm elaborated once, correct early-return completion, result-vector
   joins, initialization on every continuing arm, no arm-local definitions leaked outside scope.
6. **Instances:** canonical known argument/code/capture bindings, shared helper bodies, no caller path
   multiplication, bounded changing-specialization recursion and complete annotated residual cycles.
7. **Sums:** `oneof { ... }` on a keyed schema builds one canonical sum; member selection constructs an alternative by
   keyed supply, positionally for a non-record payload, or with no value for `unit`; matching requires
   exactly one callable handler per alternative, all with the same result type. A known tag elaborates
   only its own handler; an opaque tag emits a tag test per alternative with the payload projected
   inside the arm. C lowers to a tag plus a union and a `unit` parameter is erased. Non-schema cases,
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
   pointer for `ref(T)`, a reference to module storage may be returned from a call and followed, and
   a tied reference held in a local record reaches the enclosing instance.
8c. **Arrays (implemented):** a literal with an inferred element type and an annotated one, a static
   index, a run-time index with its guard (the guard aborts, asserted in C), element stores, nested
   arrays, an array parameter (a copy) and a local alias (not a copy), an array result compared
   element by element, a pool of nodes in module storage reached by `ref(pool[i])`, and the
   rejections `type-required` for an empty literal, `array-length`, `type-mismatch`, `index-range`
   and `not-a-place`.
8d. **Integer widths (implemented):** `u8`/`u16` literals by annotation, wrapping arithmetic at the
   named width (compared against the interpreter and the generated C), implicit widening, a literal
   adopting a narrower operand, mixed run-time widths widening, a checked conversion that rejects a
   known value out of range and aborts a run-time one, a non-integer conversion rejected, and the
   rejections `numeric-range` for an out-of-range annotation or conversion.
8e. **Imports (implemented):** a two-file program compiled through `compile_file` and run from C, an
   imported type used as an annotation and as a keyed supply, a name the module does not export
   (`unknown-member`), a missing file (`import-input`), a cycle (`import-cycle`), and a source string
   that tries to use an import.
8f. **Signed integers (implemented):** `i32` wrapping, truncating division with the remainder taking
   the dividend's sign, an arithmetic shift, negation, a reinterpreting signedness change, a
   literal adapting to a signed operand, the `int32_t` representation and the reinterpretation helper,
   and the rejections `type-mismatch` for mixing signed and unsigned and `numeric-range` for a
   negative value narrowed to an unsigned type or a negative signed power.
8g. **64-bit integers (implemented):** the exact kernel's own checks, then 64-bit literals (`0xFFFFFFFFFFFFFFFF`
   and a decimal one), widening, narrowing (rejected when known and trapped at run time), products
   that need both words, division and remainder of a signed value, a shift into the high word, and a
   `numeric-range` rejection for a known value that does not fit. The differential case compares all
   of it against the interpreter.
8h. **Slices and strings (implemented):** a string literal's bytes and escapes, an empty literal, and
   a multi-byte character taken as its source bytes; content equality and inequality; a slice parameter
   whose length is unknown while compiling, a slice over a module array, a slice over a local array, and
   an array literal viewed as a temporary; the read-only rejection (`not-a-place`) for a store through a
   view; the `borrow-escape` rejection for a view of a local returned from its activation and for a record
   holding one, while a view of module storage and a `string` literal both return; the `lex-string`
   rejections; and a `string` parameter and result compared against the interpreter through the generated
   C ABI, where the argument is built as the same two-member struct the backend emits.
8i. **Literals (implemented):** decimal, hexadecimal and binary integers, with a separator allowed
   between digits; a separator that leads, trails or doubles rejected (`lex-number`); a binary literal
   above a word taking the same exact 64-bit path a hexadecimal one does; a byte literal as one byte
   with the same escapes a string has, rejected when it is not exactly one byte; a long string that is
   raw, spans lines, drops one newline after its opening bracket and lets its level contain a lower
   level's close; a long comment at any level, and a line comment that merely begins with a bracket
   after a space kept as a line comment; `[[` still read as an array whose first element is an array;
   and a multi-line literal keeping the line of whatever follows it, so a later diagnostic still
   points where it should.
8j. **IEEE-754 double (implemented):** float literals with a point, an exponent and separators, and a
   point that needs a digit on both sides so `1.` stays an integer; IEEE arithmetic including a
   division by zero producing an infinity, zero over zero producing a NaN, and a NaN comparing false
   while `!=` holds; both conversion directions, with an integer rounding to the nearest double by
   ties-to-even and a float truncating toward zero, a known out-of-range value rejected (`numeric-range`)
   and a run-time one stopped by an emitted guard, including one for a NaN; f64 negated; f64 rejecting
   the remainder, power, shift and bitwise operators; an integer literal adopting f64 while a wider
   non-literal integer needs `f64(x)`; and a differential case comparing every one of those against the
   generated C, where an infinity and a NaN are named and tested rather than compared.
8k. **Deferred actions (implemented):** `defer` as a statement form taking a call, with its callee and
   arguments evaluated where it is written; several actions in one block running in reverse order; a
   `return` inside a statement conditional's arm running the pending action as well, which is why the
   action is emitted at each return rather than once after the block; and a tail self-call in a deferred
   block staying a real call so the action runs after it returns instead of being skipped by a back
   edge. This work also found and fixed an effect-only rule: a call whose body writes module storage
   through a local binding holding a reference is compiled rather than folded away, because the write is
   runtime state and folding it dropped the store from the generated code.
8l. **Foreign declarations (implemented):** `extern let` declaring a host function with no body and a
   required result; the artifact emitting a prototype with external linkage and a direct call, which the
   host links its own definition against; a `unit` result being erased so the call is a statement; the
   reference interpreter rejecting a foreign call (`foreign-effect`); and a fold that cannot complete
   because of one being compiled instead.
8m. **Raw pointers and scoped resources (implemented):** `ptr(T)` as a distinct type from `ref`, with
   `ptr(place)` taking an address without reading what it addresses, a host-returned pointer indexed and
   written through with no bounds check, `p.field` selecting through `ptr(Record)`, `null(T)` and address
   comparison, and the two rejections that keep the types apart: a pointer does not satisfy a `ref`
   requirement and `ref(p)` does not turn one back into a checked borrow. Also the region shape of
   section 8.7: a known body specialized so the generic combinator does not survive and the call site is
   direct, no invocation pointer anywhere in the artifact, and the acquire emitted before the body and
   the release after it. A run-time argument is now checked against its parameter's requirement in the
   residual path as well, where a wrong type used to reach the IR checker and be reported as a compiler
   bug rather than a source error. A pointer is also an indirection boundary for a recursive type, so
   `let Node = { value: u32, next: ptr(Node) }` has a finite layout while a by-value cycle still rejects
   (`type-cycle`), and field selection through a `ptr(Record)` resolves the cell a recursive definition
   reserved the way a reference does.
   bug rather than a source error.
8n. **What a value or a place is, not how it was reached (audited):** the evaluator used to decide
   several things from the syntax or the name route rather than from the value or place actually in
   hand, and each of those was a false rejection or a crash. Now covered: a container resolved as a
   place carries no value, so a consumer that needs the expression reads one from the place instead of
   indexing a nil; a nested lambda's captures travel through the lambda that encloses it, because an
   environment cannot hold a name its enclosing environment lacks; a slice is a third indirection
   boundary, so a type may mention itself through one while a by-value cycle still rejects; a reference
   decides module storage from the place as well as from the name route, so `ref(r[i])` through a local
   reference to module storage is module storage and its store reaches the module array, while the
   interpreter says it needs storage rather than blaming the target's lifetime; and a requirement types
   a lambda however it is spelled, so an alias of a signature is as good as a written one. The cycle
   checker also walks an array's element, so a cycle that crosses an array reports `type-cycle` rather
   than an eager initializer demand and names the boundary that would have made it finite; a type
   declared later is still not a cycle, and an indirection inside the array is still a boundary.
9. **IR/checking:** storage/value distinction, scope and definite assignment, target signature checks,
   module storage seeded outside every function,
   dynamic failure guards, transitive borrow provenance, finite layouts, no metadata runtime slots.
10. **C:** strict C11 compile/run, arithmetic boundary values, side-effect order, safe tail permutations,
   constant-stack self-tails (5,000,000 iterations),
   no dangling environment, separate header/source consumer, stable names and unit erasure.
11. **Distribution:** replace wordletkit with the REAL facade/CLI in the manifest; bundle parity with the
    checkout implementation; clean relocated builds and runtime execution without source search paths.

The reference interpreter describes aggregate results too: a record as its field map, a sum
alternative as its canonical tag index plus payload, and a reference as the target it names, with a
depth guard for a structure that points back at itself. The C harness therefore compares aggregate
results field by field instead of only comparing scalars. Use concrete interpreter behavior and
generated C on the same programs, comparing returned vectors AND ordered state changes. Retain IR structure tests for invariants, not arbitrary temporary spelling.
Use bounded compiler/execution subprocesses and report wall-clock time. A static interpreter work
budget counts work even when no residual instruction is emitted.

## Initial resource settings

These are explicit starting configuration defaults, not measured limits or language type rules:
source size 16 MiB per file; lexical tokens 1,000,000 per file; static depth 64; static evaluator
steps 1,000,000 per root demand; source/AST nesting 256; residual
statements 100,000 per instance; residual body keys 1,024 per program; aggregate depth 64 and expanded
components 1,000,000 per value. Keep counters cumulative across dependent work in the corresponding
root scope; retries must not reset the counter that is supposed to bound them. Limit exhaustion is a
resource diagnostic naming the scope. There is no exponential replay-path counter.

**Implemented so far**, and what they exist to stop:

| Budget | Default | A diagnostic for |
| --- | --- | --- |
| specialization nesting (`depth`) | 256 | a recursive word whose static arguments change specializing once per value. The host's own stack gives out well before a key budget of a thousand nested builds would be reached, so the nesting is bounded below it and exhaustion is a `resource` rather than an unlabelled stack overflow |
| static depth (`static-depth`) | 64 compiling, 1024 in the reference interpreter | nested compile-time folding. Folding is an optimization in residual code, so a fold that runs out of depth is compiled instead; the interpreter has no fallback and gets the largest bound it can have without reaching the host limit, measured at roughly 2500 |
| residual body keys (`keys`) | 1024 per program | one instance per distinct specialization |
| static evaluator steps (`steps`) | 1,000,000 | total compile-time evaluation work |
| contextual emitted weight (`emittedNodes`, diagnostic `c-size`) | 1,000,000 total | copied template weight, counting expression DAG nodes once; not C bytes or stack-frame size |
| optional residual credit (`residualInlineBudget`) | 0 per emitted C function | additional copied template weight; mandatory tail components do not spend it |
| optional expansion nesting | 32 Groups | active-component/depth cuts retain ordinary calls, independently of credit |

Still unimplemented: source size and token count, source/AST nesting, residual statements per
instance, and aggregate depth and expanded components per value.

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
