# Wordlet compiler interfaces and code structure

Concrete contract for `architecture.md`. Data shapes are in `ast.asdl` and `ir.asdl`; both parse with
the vendored ASDL and are covered by `tests/schemas.lua`. This file fixes pass order, module APIs,
side tables, evaluation state and the public facade. It is implementation-ready; it is not itself an
implementation.

Terms: **E** = `Ir.Expr` (pure immutable expression), **S** = `Ir.Stmt` (ordered statement),
**value** = `Ir.Value` (function-local immutable result), **storage** = `Ir.Storage` (function-local
mutable cell).

## 1. Pass order and data handed between passes

```
text ──lex──► Token[] ──parse──► Ast.Program
                                     │
                          resolve ───┤► Resolution (side tables over AST; AST not mutated)
                                     │
                            eval ────┤► Compilation { exports, functions, types, modules, ... }
                                     │
                           check ────┤► the Ir.Fn list, verified (else bug)
                            cabi ────┤► Layouts
                           lower ────┴► one closed artifact, four views (unit, source, header, cdef)
```

Rules:

- Only `eval` inspects source meaning. `check`, `cabi` and `lower` consume IR and metadata.
- `resolve` reads the AST and writes side tables. It never rewrites the AST, so spans stay exact.
- Each pass is a pure function of its inputs plus options; no pass memoizes on interned nodes.
- Failures are raised as `Diagnostic` values (section 7), never returned as sentinel IR.

## 2. Module APIs

Lua-level signatures. `Diag` values are raised with `error`, not returned.

| Module | Exported | Contract |
| --- | --- | --- |
| `wordlet/lex.lua` | `tokens(source, name) -> Token[]` | free-form lexer; every token has a span |
| `wordlet/parse.lua` | `program(Token[]) -> Ast.Program` | builds `ast.asdl` nodes; exports are a separate grammar |
| `wordlet/resolve.lua` | `module(Ast.Program) -> Resolution` | scopes, bindings, captures, tail positions |
| `wordlet/schema.lua` | `Ty`/`Ir` contexts and `Ty` constructors, the intrinsic `Ty:` predicates, `runtime`/`representable`/`hasNamed`/`embedsCell`/`reachesCell` | interned descriptions; a fold owns its visited set |
| `wordlet/session.lua` | `new(options) -> Session` | one compilation's descriptions, occurrences and budgets |
| `wordlet/eval.lua` | `compile(program, loadedTop) -> Compilation` | a session method: keys, instances, IR, type application |
| `wordlet/check.lua` | `program(fnList, modules, foreigns)` | raises `bug` diagnostics only |
| `wordlet/cabi.lua` | `close(compilation) -> Layouts` | record layouts, callable ABIs, C names |
| `wordlet/analysis.lua` | `analyze(fn) -> Analysis` | one walk per `Ir.Fn`: storage/value uses, mutations, the inlining rule and the sharing rule (structure.md §3.5) |
| `wordlet/tail.lua` | `prepare(functions, modules, foreigns) -> plan`; `normalize(fn)`; `components(order, edges)` | checked copy-only join normalization, conservative scalar reuse, deterministic SCCs and costs |
| `wordlet/contextual.lua` | `bodies(layouts, newEmitter) -> buffers`; `call`, `returnText`, `group` | static destinations, tail components, optional copies and actual C roots |
| `wordlet/lower.lua` | `close(layouts)` then `unit(layouts)`, `cdef(layouts, ns)`, `source(layouts, headerName)`, `header(layouts, name)` | `close` computes the emission once; the four views read one closed artifact |
| `wordlet/diag.lua` | `reject/bug/todo/resource/internal(...)`, `format(Diagnostic) -> string` | diagnostic construction |
| `wordlet/init.lua` | `compile(options) -> Artifact`, `compile_file(path, options)` | public facade |
| `wordlet/cli.lua` | `function(api, argv) -> exit_status` | bundler CLI entry point |

Current reality, so the table is not read as a promise of empty files:

- `wordlet/resolve.lua` holds the purely syntactic facts — a lambda's captured names and a
  definition's tail self-call — exposed as `captures(wordDef)` and `tailCalls(body, name)`.
  **Bindings are resolved during evaluation, not by a separate pass**: a name can denote a word, a
  value, a schema or a field depending on values that only exist at evaluation time, so a static
  pass would have to duplicate that. The architecture gives `resolve` bindings as well; this is the
  one deliberate deviation, and it is why `Resolution` has no `bindings` table here.
- Primitive bootstrap lives in `wordlet/eval.lua` (`load`) rather than a `builtins.lua`: the names
  u32, bool, unit and type, plus the `oneof` type constructor. `oneof` is an ordinary word with a
  compiler-provided terminal (`Eval:builtin`), so it is applied, partially supplied and type-checked
  through the same path as any other word; its terminal receives the keyed schema and returns a
  `Ty.Sum` type value.
- The schema text is served by the generated modules `wordlet/schema/ast.lua` and
  `wordlet/schema/ir.lua`, produced from `ast.asdl`/`ir.asdl` by `tools/embed.lua`.

`Compilation = { session, exports, functions, types, foreigns, modules }`: the exported names, the
instances behind them, the module storage and the foreign declarations one compilation produced.
`check` and `cabi` consume the three lists (`functions`, `modules`, `foreigns`).

## 3. Resolution side tables

`Resolution` maps AST nodes to classification results. Node identity keys are fine because AST nodes
are not interned.

```lua
Resolution = {
  bindings  = { [Ast node] = Binding },   -- for Reference and StoreStmt targets
  words     = { [Ast.WordDef] = WordShape }, -- params, result contract, captures, entry id
  tail      = { [Ast node] = boolean },   -- syntactic tail position
  scopes    = { [Ast node] = Scope },     -- child scope for blocks/arms/lambdas
}

Binding    = Local(slot) | TopLevel(name) | Param(index) | ReceiverField(name) | Builtin(name)
WordShape  = { params = Param*, result = ResultContract?, captures = Capture*,
               free = name->Binding, self_key = KeyRef? }
Capture    = Static(name, Binding)          -- type/word metadata, checked and frozen
           | Value(name, Binding, Ty.V)     -- by-value immutable snapshot
           | Place(name, Binding, Ty.V)     -- borrowed receiver/ancestor route
```

Resolution rules, in order:

1. Record every declaration name in its scope; duplicate names in one scope reject.
2. Resolve `Reference(name)`: an enclosing lambda/word parameter wins, then an enclosing declaration,
   then the active receiver's field names, then a top-level word, then a builtin. The receiver step
   is what makes bare `state = ...` mean the receiver field.
3. Classify a `StoreStmt` target: `Reference` resolving to a receiver field, or a `FieldSelect` chain
   rooted at a resolved place. Any other target rejects ("not a storage place").
4. Verify that `Reference` used as a value never names an unassigned forward local.
5. Compute `free` per `WordDef`/`Lambda`: names bound outside it.
6. Classify each free name into a `Capture`: static metadata, by-value value, or borrowed place.
   Classify statically because the classification fixes the environment layout.
7. Mark tail positions: the body root, both arms of a tail `If`, and both arms of a tail `IfStmt`.

Capture classification is a language rule, not an optimization:

- a type, a word with static arguments, or frozen metadata → `Static`, stored in the code template;
- a runtime scalar or immutable aggregate snapshot → `Value`, copied into the environment;
- an actual receiver/method view, or any storage-rooted occurrence → `Place`, borrowed;
- anything already borrowed (a borrowed callable) stays borrowed.

`resolve` does not decide `:of`, key identity, or saturation; that is `eval`.

## 4. Evaluation state

```lua
Frame = {
  session,          -- the compilation session: descriptions, occurrences, budgets (session.lua)
  residual,         -- true emits into the Ir.Fn under construction; false runs with no builder
  scope,            -- the lexical scope
  span,             -- the span of the construct being evaluated
  tail,             -- is the current expression in tail position
  expectedResult,   -- a signature from an annotation context, if any
  builder,          -- Ir.builder (residual only)
  body,             -- Ir.Stmt list under construction (residual only)
  fn,               -- Ir.Fn under construction (residual only)
  instance,         -- the instance being built (residual only)
  deferFrame,       -- pending deferred actions
  terminated,       -- the current list was terminated
  resultTypes,      -- the result types of the body being executed (residual)
  result,           -- the reference interpreter's result vector (non-residual)
}
```

Key points:

- **A frame that is not residual has no builder.** The same expression walker runs with
  `ctx.builder`, `ctx.body` and `ctx.fn` nil. A static attempt therefore cannot leave partial IR
  behind: an operation that needs runtime storage raises `runtime-in-normalization` rather than
  emitting half a statement. Compile-time normalization never reads or writes module storage, so it
  cannot bake a snapshot or drop a store.
- **The reference interpreter runs the program.** `session.run` marks a session whose purpose is to
  execute rather than to specialise. Under it, normalize code reads and writes module storage through
  the concrete value it names, so a module array element or record field behaves exactly as the
  generated C does.
- **Initialization is eager and ordered.** `initializeModule` demands every top-level value binding
  once, in declaration order; a forward reference pulls a later initializer early. `demand` sets
  `session.demanding` while it runs, so an initializer may read and write module storage — it is
  compile-time execution over concrete values. Both instance-building boundaries suspend `run` and
  `demanding`, restoring them on success or diagnostic unwinding: building code inside an initializer
  or interpreter run does not execute that code. A nested initializer demand has its own permission.
- **Conditional joins are logical vectors.** Continuing arms agree in arity and per-position type;
  unit and common known components need no storage. Other components get private typed slots,
  preserving borrow flags. Materialization stays inside its selected arm; one `If` contains all arm
  effects and transfers. Terminated arms contribute no result, but their control is still emitted.
- The builder interns E per `Ir.Fn` (`Builder.memo`), as required by `architecture.md` §7. ASDL
  does not mark `Ir.Expr` unique because `Value` IDs are function-local, so the memo belongs to the
  function's builder rather than to the schema.
- Each nested `Lambda`/`MethodMember` body creates a fresh `Ir.Fn` with its own builder and id
  allocators; the enclosing frame is used only to resolve and classify captures.
- Evaluation returns a `Value`. Control completion is not a value: `execBlock` answers whether the
  block ended, and `ctx.terminated` records that the current evaluation already transferred control
  (a tail back edge, emitted as `Ir.Next`), which the enclosing `return` then reports. A body with
  no returning path rejects (`no-return`).
- **Known match selection precedes lambda construction.** `evalMatchCPS` records an unselected
  lambda literal as `false` in its local handler table: present for coverage/duplicate checks, but
  neither a closure plan nor a callable to invoke. Only a known tag may introduce this marker;
  opaque matches elaborate all arms. Non-lambda handler expressions keep their evaluation order
  and callable validation.
- **Immediate static lambda use separates preparation from ABI construction.** `prepareLambdaCPS`
  returns an internal plan with captures, resolved `paramTypes`/`inputs` and environment shape, but no
  `sig` or `ty`. `completeLambdaCPS` builds the base and supplies those checked fields before exposing
  a closure Value. Direct literal calls and known selected literal handlers in non-residual frames
  can use `invokePreparedLambdaCPS`: saturated known atom arguments and a non-borrowing static
  environment enter `invokeClosureCPS` without a base. Fallback completes a real callable and supplies
  the already-evaluated arguments. First-class values and residual calls keep checked construction;
  no pending plan is presented as a source Value or provisional return signature. Parameter types
  are reused, including the bound-argument offset, rather than replaying annotations.
- **Schema-directed interfaces.** `Surface.Face` is a compilation-owned, interned descriptor
  separate from structural `Ty`: a schema id, a container element face, or an open recursive
  definition cell. `Session.schemas` resolves it to the actual schema definition. `fieldFaces`
  records each schema field's declared interface. Value wrappers, field slots, parameter and result
  metadata carry faces only while evaluating source; `Ir.Fn`, type equality, C layouts and runtime
  records do not. A child method call projects the child's actual place and binds the method of its
  declared face. Binding a field value elsewhere copies its data, not its parent's storage.
  `withFace` changes the interface of a destination, not its type or code pointer; a partial supply
  must first prove identical static supply (`interface-supply`). Interfaces on dynamic type inputs
  participate in keys via the static type value's encoding, not via structural type identity.
- **One law for application.** `Eval:supply(ctx, callee, args, span)` is the only entry point: it
  appends the arguments to the callee's bound arguments, tests saturation, and hands a saturated
  call to the one owner for its kind — `invokeBuiltin`, `invokeForeign`, `invokeSource`,
  `invokeMethod`, `invokeClosure`, or `invokeRuntime` for a value whose representation is a
  callable. An eligible prepared immediate lambda enters that same closure owner directly, without
  manufacturing a first-class value merely to invoke it. A saturated word or method call shares one fold-or-build decision, `foldOrBuild`, and a
  call that cannot fold becomes an instance through `callInstance`, which emits the call or, in tail
  position, a `loopBack` back edge. A deferred action and a match handler call `supply` as well, so
  there is no second dispatcher to keep in step.

### 4.1 Emitting statements

`ctx.body` is the current `Stmt` list and `ctx.builder` is the `Ir.builder` that fills it. Statements
go in through `builder:let`/`var`/`read`/`store`/`trap`/`return_` and expressions through
`builder:const`/`ref`/`un`/`bin`/`get`/`make`/`convert`/`addr`/`sliceLength`/`nullPtr`/`ptrIndex`/
`sliceIndex`; `builder:emit` appends a finished statement. The builder owns the id allocators
(`valueId`, `storageId`) and the E memo, so every id is unique within the `Ir.Fn` it belongs to.

Two rules are easy to get wrong and are therefore explicit:

- **Materialise an arm's value under that arm's context.** A value is canonicalised into reads of the
  storage it lives in (`recordExpr`/`fieldExpr`), so those reads belong to the arm that built it.
  Storing an arm result with the enclosing context leaks reads of arm-local storage into the
  continuation. `evalCondition` and sum matching pass `yesCtx`/`noCtx`/the arm's context.
- **Keep `inputPlan` and `inputTypes` in step.** A call site materialises each argument against the
  input type recorded for it, so a builder that appends one without the other silently loses the
  expected type. That is invisible for scalars and records and wrong for callables and aggregates.
- **Never write `cond and nil or x`.** When the `and` branch yields `nil` the `or` branch runs
  anyway, which silently defeats an erasure guard such as a `unit` payload. Use an explicit `if`.

### 4.2 Self-tail rewrite at build time

When a saturated call in a syntactic tail position targets the current instance key, the evaluator
does not emit `Call`. Instead it:

1. evaluates every next argument into a temporary value (`Let`) *before* any assignment;
2. emits `Store` for each loop-carried `Var` (declared before the `Loop`);
3. emits `Next`.

The reversal (`architecture.md` §6.3) is ordinary `Call` + `Return`. No separate pass and no AST
analysis is needed, since tail position is already resolved. When the instance has no loop-carried
storage (all parameters unchanged) the rewrite is a plain `Next`.

### 4.3 The evaluator's machine protocol

`wordlet/eval.lua` is written in continuation-passing style and driven by `wordlet/machine.lua`. The
reason is depth: Lua guarantees proper tail calls, so an edge written `return self:fooCPS(m, ..., k)`
reuses its host frame, while `local a = eval(left) ... eval(right)` cannot. Every recursive edge in the
evaluator is now of the first shape, so an interpreted fold costs heap (one closure per pending step)
rather than host stack. The measured effect: `g(1023)` folds, `g(1025)` is refused with `static-depth`,
and the host's stack limit is never the reason anything fails.

The conventions:

- **A step is a pair.** A continuation is called as `k(machine, ...)` and answers with the next pair
  `(continuation, values...)`, or with `nil` as the continuation to mean "these are the final values".
  The value channel is a *vector*: a value definition produces one value per binder, `storeTarget`
  produces a slot and a place, and `declaredResult` produces the types and the signature requirements.
- **Closures are the stack; descriptors are its shadow.** Only the frames that must be counted,
  reported or unwound through become descriptors: a static fold, a `Build`, a `demand`, a call. A
  diagnostic needs no unwinding -- the pending chain is simply not called -- but it must find the
  nearest *handler*, which is what `Machine:popToHandler` walks.
- **Depth is counted, not inherited.** `Machine:checkDepth(kind, ...)` bounds the descriptors: a static
  fold is bounded by `maxStaticDepth` (or `maxInterpretDepth` in a reference-interpreter run) and
  refuses with `static-depth`, a build by `maxBuildDepth` and refuses with `depth`. A refused fold in
  residual code is not fatal: `foldOrBuild` pushes a handler, and the handler compiles an instance
  instead. That handler is what the direct evaluator spelled as `pcall` -- and it is why the evaluator
  no longer has one.
- **One boundary starts the loop.** `Eval:drive(ctx, entry)` is the only place outside the evaluator
  where the machine's loop is started, and the `*Top` entries (`supplyTop`, `exportedTop`,
  `initializeModule`, `resolveExportItem`, `compile`) are its only callers. Nothing inside the
  evaluator uses it; a converted method is called by name, with its continuation.

`tests/machine.lua` covers the core: constant host stack over a 100 000-step chain, handler unwinding,
counted depth, and the boundary.

## 5. Instances, keys and module storage

```lua
Compilation = { session, exports, functions, types, foreigns, modules }
Instance = {
  key;                -- cache key: the code identity plus the classified arguments
  code;               -- { tag = "word" | "method" | "closure", def, plan?, receiver? }
  fn;                 -- Ir.Fn: the ABI is fn.inputs, fn.results, fn.params, fn.hidden
  status;             -- "building" | "done" | "failed"
  failure;            -- the Diagnostic a failed build recorded, re-raised by a later attempt
  results;            -- one entry per *source* result slot; `false` where a signature requirement
  resultRequirements; -- the Ty.Sig for each `false` slot
  runtimeResults;     -- the same list with the unit slots erased: what Ir.Fn.results carries
  inputTypes;         -- Ty.V per input, in order
  inputPlan;          -- { kind = "value" | "place" } per input
  paramPositions;     -- the index in fn.params each input binds
  loopTargets; loopBack; loopHeader;  -- the self-tail rewrite's bookkeeping (§4.2)
}
```

- An instance's ABI is its `Ir.Fn`. `inputTypes`/`inputPlan`/`paramPositions` record how each
  input was derived while the body was built; the backend reads the `fn`.
- A *source* result slot that a signature requirement has yet to fix is `false`, with the
  requirement in `resultRequirements`; `runtimeResults` drops the `unit` slots and `Ir.Fn.results`
  is built from it. `Eval:logicalResults` puts the `unit` values back, which is what the reference
  interpreter and an entry with a `unit` result see.
- The key is what `Eval:instanceKey` and `Eval:callableKey` build: the definition id (or the closure
  plan key), the receiver's static fields, and then every parameter position -- a static argument
  contributes its encoded value and type, a runtime callable its code identity (two closures must
  not share an instance), and any other runtime argument a `*`.

Instance discovery order is deterministic: the export list in source order, then depth-first over
newly requested keys. Function IDs are assigned on reservation. `Session:registerInstance` owns map
insertion and order-list append. `instanceCount` tracks map cardinality in O(1), including building
and failed entries; cached requests do not increment it. Both source-instance admission paths use
that counter, not a scan or the order-list length. The compiler-owned module initializer retains
its existing admission exemption, but its registry key counts once, including when replaced.

### 5.1 Contextual C closure

`Lower.close` prepares normalized copies without mutating `Instance.fn`. Changed functions are
rechecked and analyzed. Each real C root reserves every entry of its safe scalar tail component
before emitting any body. Internal terminal identity calls install parallel argument snapshots and
jump locally; they never spend optional credit. Other known calls may get fresh nested copies with
static local return destinations, or remain ordinary calls. Active-component and depth cuts prevent
unbounded expansion; an unproved lifetime retains the call.

`layouts.signatures` retains logical interfaces. After body discovery, `layouts.instances` retains
the conservative instance catalog and `layouts.order` is the actual root queue: exports/initializer,
remaining direct targets and View adapter targets. `layouts.recursiveRoots` records SCC membership
of remaining known C calls, so recursive private roots are not forced inline. Unknown calls keep
existing ABIs and have no new stack guarantee. `layouts.contextual` holds the configured budget,
total weighted size and per-root reports (mandatory/total weight, calls, jumps, expansions, reasons).

## 6. IR invariants the builder must maintain

These are the obligations `check.lua` verifies; the builder should not rely on the verifier to fix them.

1. **Scopes.** A `value` defined by `Let`, `Read` or `Call` is in scope for the rest of its own `Stmt`
   list and nested lists inside that remainder. Values defined in an `If` arm are not visible after it.
2. **Falling through.** Define `falls(Stmt)` and `falls(S[] = list)`:

   ```
   falls(list)  = list is empty, or falls(last(list))
   falls(Return|Trap|Next) = false
   falls(Loop)             = false
   falls(If(_, y, n))      = falls(y) or falls(n)
   falls(other)            = true
   ```

   The `Ir.fn`'s body list must not fall through; `architecture.md` §9 requires every reachable path
   to end in `Return`.
3. **Definite initialization.** Track a set of initialized storage through a list: a `Var` with an
   initializer adds its storage and a `Store` adds the storage its place roots at; `If` and
   `Switch` keep what every arm that *continues* (item 2) leaves established, with the input set for
   an arm the builder did not name; a `Loop` hands its incoming set to the body and takes the
   body's fall-through set, because the emitter places the continuation inside the loop while a
   `Next` starts the next iteration. Module storage and a borrowed place parameter start
   initialized. A `Read` whose place roots at a storage not in the set is a `bug`.
4. **Places.** `Place.Local(storage)` requires storage declared by `Var`, by a `PlaceParam`, or by a
   module-level `Var` outside every function. `Place.Project(base, field)` requires a record-typed
   base and an existing field. `Place.Deref` requires a base holding a `ref` or a `ptr`, and records
   the pointee type on the node. `Place.Index` requires an array base with a matching element type
   and a `u32` index; `Place.SliceIndex` requires a slice-typed view value and `Place.PtrIndex` a
   `ptr`-typed one, each with a `u32` index.
5. **Args and slots.** `Ir.Call` arguments match the target `Ir.Fn.inputs` positionally: `InValue` →
   `ValueArg`, `InPlace` → `BorrowArg`. `Ir.View` names a callable's code and binds the hidden prefix
   of its inputs in order, never more slots than that code declares; the remaining inputs must match
   the view's own visible signature, and the bound type is a `Ty.View`, or a `Ty.Owned` whose
   environment is `unit` for pure code. `Ir.Indirect` matches the `Ty.View`'s *visible* signature.
   A `unit`-typed parameter is erased when the input plan is built, so it contributes no `Ty.Input`
   and no `Ir.Param` and appears in no argument list. The parameter's name is bound to the `unit`
   value directly, and because there is no `Ir.Literal` for `unit`, a `unit` value can never be
   materialised as an `Ir.Expr`.
6. **Tagged callables.** A `Ty.Tagged` value is a tag plus the environment of the arm that tag
   names. Its arms are registered in `Eval.arms` under the identity that names them in the type, so a
   call site dispatches from the type alone: the tagged arm of `Eval:invokeRuntime` tests each tag,
   projects that arm's environment out of the payload, and calls the arm's own code directly — the
   arm's environment is the call's hidden prefix, exactly as for a non-tagged owned callable. Every
   arm shares the visible signature, so the results join through one slot per result. A join needs
   both arms to be callables of one signature; a word arm needs declared result types and a closure
   arm may not borrow storage, because the value holds its environments by value. Erasing a
   runtime-tagged value into a signature rejects (`callable-erase`).
7. **Sum tags.** `Ir.ConstructVariant`/`Ir.VariantMatches`/`Ir.VariantPayload` each name their
   `Ty.Sum`. The tag must be one of its alternatives; a construct of a `unit` alternative must omit
   its payload and any other alternative must have one whose type matches; a projection must not
   target a `unit` alternative, and its operand value must have been bound with that exact sum type.
   A projection is only ever reachable inside an arm whose test established the tag, which is a
   builder obligation the checker cannot see from the statement list alone.
8. **Visible versus actual signature.** `Ty.Owned`/`Ty.View` carry the source-visible signature in
   `Ty.Sig`: what a caller passes. `Ir.Fn.inputs` carries the actual ABI, whose first `fn.hidden`
   inputs are the owner/capture prefix (`check.lua` bounds the count by the input list). The two
   must not be conflated, and `cabi` derives the C signature from the `fn`.
9. **Integer widths.** `Ir.Expr.Convert(operand, type)` is the only conversion, and both its operand
    and its type are integer widths. Arithmetic and bitwise operators take both operands at one width
    and yield it; a shift takes an integer value and a `u32` amount and yields the value's width; a
    comparison takes two integers of any widths and yields `bool`. Which width an operand needs is
    decided from the source: a literal adopts the other operand's width when it fits, and otherwise
    the wider width wins, so the decision never depends on what happens to be known at compile time.
11. **Indexes.** `Ir.Place.Index(base, index, type)` names one element: the base must be an array,
    the recorded type must be its element type, and the index expression must be a `u32`. A known
    index is checked while compiling and rejected when it is out of range; any other index is preceded
    on every path by `Trap(Ge(index, length), "index-range")`, which the builder emits and the
    verifier does not re-derive, exactly as for a run-time divisor.
12. **Traps.** A dynamic `Div`/`Rem` is preceded on every path by `Trap(zero?, "division-zero")`
   testing the same operand value.

## 7. Diagnostics

```lua
Diagnostic = { kind, code, message, span = Ast.Span? }
-- kind: reject=1  bug=2  todo=3  resource=4  internal=2
```

Every diagnostic carries a span when one exists. `eval` attaches the innermost expression span it
knows; `check` reports a bug without one, because an `Ir.Fn` carries no source span of its own — a
source mistake is rejected earlier, with a span. A `Diagnostic` is raised, so `pcall` boundaries in
`cli.lua`/`init.lua` must distinguish it from a Lua error by its `kind` field.

## 8. Public facade

```lua
local wordlet = require("wordlet")

local artifact = wordlet.compile_file("app.let")            -- or wordlet.compile{ source=..., name=... }

artifact:header("app")     -- string: include guard, extern "C", reachable types, export prototypes
artifact:source("app")     -- string: bodies; private prototypes stay here
artifact:unit()            -- string: one self-contained translation unit (header contents inlined)
artifact:exports()         -- { functions = {name...}, types = {name...} }

wordlet.syntax             -- string: the language reference, embedded from syntax.md
wordlet.guide              -- string: the design and naming guide, embedded from GUIDE.md
wordlet.walk               -- AST/IR traversal by ASDL reflection; children, nodeChildren, walk, sums
wordlet.jit.loadstring(s)   -- compile `.let` text with the C backend and load it (LuaJIT FFI)
wordlet.jit.loadfile(path)  -- the same for a file, resolving its own `use` imports
wordlet.jit.run(source)     -- load and call `main`
wordlet.jit.install()       -- register a searcher so `require("a.b")` finds `a/b.let`
```

`compile_file` resolves the module graph first: it reads each `use`d file relative to the importing
one, loads a module before the modules that use it, declares each namespace in the importing module's
top scope, and then compiles the entry module with its own top. `session:compile(program, top)`
accepts that pre-loaded scope; `session:declareNamespace` puts a namespace in it. A source string
cannot resolve an import, so `compile` rejects a `use` declaration (`import-input`).

Options: `name` (defaults to the path), `limits` (section 9), `target = "c11"`, `inline` (defaults
to `true`: a nonrecursive private root is asked to force-inline on GCC and clang, and is plain
`static` on another C11 compiler), `residualInlineBudget` (finite nonnegative integer, default `0`:
optional residual-copy weight per C function, separate from mandatory tail closure), and `symbolPrefix` (defaults to `""`: a prefix for every exported symbol,
which the FFI front end uses so several artifacts can be loaded in one process). Compilation errors
raise `Diagnostic`; the facade never returns a partial artifact. `artifact:unit()` exists because the
bundler's CLI defaults to one file, while `header`/`source` support separate compilation.

`wordlet/cli.lua` returns `function(api, argv) -> status`:

```
wordlet [--header NAME] [--unit] [--check] [-o OUT] FILE.let
```

`--check` compiles and reports diagnostics without writing output. Default output is stdout.

## 9. Limits

Start from the values in `VALIDATION.md` (static depth, evaluator steps, AST nesting, residual
statements, keys, aggregate size) and make them `Options.limits` fields with those defaults. Limits
are per root demand or per key and are reported as `resource` diagnostics naming the scope.
`limits.emittedNodes` is a finite nonnegative integer (default `1000000`) bounding total contextual
emission weight; exhaustion reports `resource [c-size]`, never a partial tail component. Optional
copies additionally stop at 32 nested Groups. Invalid emission budgets report `compile-option`.

## 10. Determinism

- Token and AST spans use byte offsets into the source; the file name is the load name.
- Function IDs are assigned in reservation order (exports first, sorted by export name).
- C names: `wordlet_<escaped>` for exports, `wordletfn_<n>` for private functions, numbered by
  preorder over functions sorted by ID. Escape every non-alphanumeric byte, including `_`, as `_XX`.
- Record/tuple layouts are numbered in first-demand order from that traversal, then sorted by
  canonical field order for emission.
- No pass iterates a hash table to produce output; use sorted key lists.

Two compilations of identical input produce byte-identical header and source.

## 11. Worked example

Source (`app.let`):

```
let inc(x: u32) : u32 = x + 1
let apply(f: (u32): u32, x: u32) : u32 = f(x)
let run(x: u32) : u32 = apply(inc, x)
return { functions = { inc, run } }
```

Resolution: `inc`/`apply`/`run` are top-level; `f`/`x` are params; `apply(inc, x)`'s `inc` is known
code with no captures, so it is a `Static` argument. `apply` is therefore specialised on `inc`, `f` is
erased from the ABI, and `f(x)` becomes a **direct call**. No `Ir.Indirect` is emitted: it is reserved
for a callable whose code is not known in this compilation, which is rejected today rather than
lowered.

Evaluation produces (schematically):

```
Fn id=inc  role=Entry hidden=0 inputs=[InValue u32] results=[u32]
  body: Return( Bin(Add, ref(x), Const(u32,1)) )        -- x is ValueParam 0

Fn id=run  role=Entry hidden=0 inputs=[InValue u32] results=[u32]
  body: Call([v1], "inc", [ValueArg(ref(x))])
        Return( ref(v1) )

Fn id=body#1 role=Body hidden=0 inputs=[InValue u32] results=[u32]
  body: Call([v1], "inc", [ValueArg(ref(x))])   -- f is a static fact, so no callable input
        Return( ref(v1) )
```

`inc` is known code, so `apply(inc, x)` specializes: `f` becomes a `Static` fact and the body key
records it, while `x` remains a runtime input. The `projections` table maps `run`'s single source
slot to `Runtime(1)`. `cabi` assigns `uint32_t` and emits:

```c
uint32_t wordlet_inc(uint32_t x);
uint32_t wordlet_run(uint32_t x);
```

with `wordlet_run` calling `wordlet_inc`, and the indirect call only in the private body used when
`apply` is invoked with unknown code.

This example fixes representation conventions; concrete expected-output tests belong in
`tests/` once `eval` exists.
