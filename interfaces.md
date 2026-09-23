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
                            eval ────┤► Compilation { Ir.Program, Meta }
                                     │
                           check ────┤► verified Ir.Program  (else bug)
                            cabi ────┤► Layouts
                           lower ────┴► header bytes, source bytes
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
| `wordlet/eval.lua` | `program(Ast.Program, Resolution, Options) -> Compilation` | keys, instances, IR, projections |
| `wordlet/check.lua` | `program(Ir.Program, Meta)` | raises `bug` diagnostics only |
| `wordlet/cabi.lua` | `close(Ir.Program, Meta) -> Layouts` | record layouts, callable ABIs, C names |
| `wordlet/lower.lua` | `header(Layouts) -> string`, `source(Layouts) -> string` | views of one closed artifact |
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
  U32, Bool, Unit and Type, plus the `OneOf` type constructor. `OneOf` is an ordinary word with a
  compiler-provided terminal (`Eval:builtin`), so it is applied, partially supplied and type-checked
  through the same path as any other word; its terminal receives the keyed schema and returns a
  `Ty.Sum` type value.
- The schema text is served by the generated modules `wordlet/schema/ast.lua` and
  `wordlet/schema/ir.lua`, produced from `ast.asdl`/`ir.asdl` by `tools/embed.lua`.

`Compilation = { program = Ir.Program, meta = Meta }`. `Meta` is compiler-private state that never
reaches `Ir.Program`: projections, trap policy, export selection, source spans, provenance.

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
EvalContext = {
  mode      = "normalize" | "residual",          -- Normalize/Residualize
  instance  = InstanceRef?,                      -- nil while normalizing
  fn        = Ir.Fn?,                            -- the Fn under construction (residual only)
  body      = Stmt[]?,                           -- statement list under construction, innermost last
  exprs     = { [ExprKey] = Ir.Expr }?,          -- per-function E memo (interning)
  next      = { value = n, storage = n, bundle = n },  -- per-Fn allocators
  params    = Ir.Param[]?,
  expected  = ResultContract?,                   -- from the annotation/binding context
  frames    = Frame[],                           -- lexical frames: name -> Value/Place
  limits    = Limits,
}
```

Key points:

- **Normalization has no builder.** `mode = "normalize"` runs the same expression walker but
  `ctx.fn`, `ctx.body` and `ctx.next` are nil. A static attempt therefore cannot leave partial IR
  behind: an operation that needs runtime storage raises `runtime-in-normalization` rather than
  emitting half a statement. Compile-time normalization never reads or writes module storage, so it
  cannot bake a snapshot or drop a store.
- **The reference interpreter runs the program.** `session.run` marks a session whose purpose is to
  execute rather than to specialise. Under it, normalize code reads and writes module storage through
  the concrete value it names, so a module array element or record field behaves exactly as the
  generated C does.
- **Initialization is eager and ordered.** `initializeModule` demands every top-level value binding
  once, in declaration order; a forward reference pulls a later initializer early. `demand` sets
  `session.moduleDemand` while it runs, so an initializer may read and write module storage — it is
  compile-time execution over concrete values. Residual specialization still rejects touching it.
- `exprs` implements per-function E interning, as required by `architecture.md` §7. ASDL does not
  intern `Ir.Expr` because `Value` IDs are function-local.
- Each nested `Lambda`/`MethodMember` body creates a fresh `Ir.Fn` with its own `next`, `body` and
  `exprs`; the enclosing context is used only to resolve and classify captures.
- Evaluation returns `Completion`: `Continues(Value*)`, `Returns(Value*)` or
  `TailTransfer(key, Value*)`. `Returns` is not a value and cannot be consumed by later statements.

### 4.1 Emitting statements

`ctx.body` is the current `Stmt` list. Emitters: `emitLet`, `emitVar`, `emitRead`, `emitStore`,
`emitCall`, `emitIf`, `emitLoop`, `emitReturn`, `emitTrap`. Every emitter that allocates uses
`ctx.next` so IDs are unique within the `Ir.Fn`.

Two rules are easy to get wrong and are therefore explicit:

- **Materialise an arm's value under that arm's context.** A value is canonicalised into reads of the
  storage it lives in (`recordExpr`/`fieldExpr`), so those reads belong to the arm that built it.
  Storing an arm result with the enclosing context leaks reads of arm-local storage into the
  continuation. `evalCondition` and sum matching pass `yesCtx`/`noCtx`/the arm's context.
- **Keep `inputPlan` and `inputTypes` in step.** A call site materialises each argument against the
  input type recorded for it, so a builder that appends one without the other silently loses the
  expected type. That is invisible for scalars and records and wrong for callables and aggregates.
- **Never write `cond and nil or x`.** When the `and` branch yields `nil` the `or` branch runs
  anyway, which silently defeats an erasure guard such as a `Unit` payload. Use an explicit `if`.

### 4.2 Self-tail rewrite at build time

When a saturated call in a syntactic tail position targets the current instance key, the evaluator
does not emit `Call`. Instead it:

1. evaluates every next argument into a temporary value (`Let`) *before* any assignment;
2. emits `Store` for each loop-carried `Var` (declared before the `Loop`);
3. emits `Next`.

The reversal (`architecture.md` §6.3) is ordinary `Call` + `Return`. No separate pass and no AST
analysis is needed, since tail position is already resolved. When the instance has no loop-carried
storage (all parameters unchanged) the rewrite is a plain `Next`.

## 5. Instances, keys and projections

```lua
InstanceRef = { key; fn_id; role; params; hidden; results }
Meta = {
  instances  = { [fn_id] = InstanceRef },
  projections= { [fn_id] = Projection },   -- source result slots -> runtime slots
  exports    = { FunctionExport*, TypeExport* },
  policies   = { [reason] = "abort" },
  spans      = { [fn_id] = Ast.Span },
}
Projection = { Static(Ty.V type, atom) | Runtime(number index) }[]
```

- A body's `Ir.Fn.results` contains only `Runtime` slots, in source order.
- An entry's `Ir.Fn.results` contains every source slot, materialized.
- `Atom` is a compiler-private checked static value (scalar, type, or frozen word). It never enters
  `Ir.Program`; an entry lowers a static slot to `Const`/`Make`.

Instance discovery order is deterministic: the export list in source order, then depth-first over
newly requested keys. Function IDs are assigned on reservation.

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
3. **Definite initialization.** Track a set of initialized storage through a list: `Var` adds its
   storage; `If` produces the *intersection* of its arms' outputs (a missing arm passes the input
   set through); `Loop` adds nothing and does not fall through. A `Read` of a storage not in the set
   is a `bug`.
4. **Places.** `Place.Local(storage)` requires storage declared by `Var`, by a `PlaceParam`, or by a
   module-level `Var` outside every function. `Place.Project(base, field)` requires a record-typed
   base and an existing field. `Place.Deref` requires a base holding a `Ref` or a `Ptr`, and records
   the pointee type on the node. `Place.Index` requires an array base with a matching element type
   and a `U32` index; `Place.SliceIndex` requires a slice-typed view value and `Place.PtrIndex` a
   `Ptr`-typed one, each with a `U32` index.
5. **Args and slots.** `Ir.Call` arguments match the target `Ir.Fn.inputs` positionally: `InValue` →
   `ValueArg`, `InPlace` → `BorrowArg`. `Ir.View` names a callable's code and binds the hidden prefix
   of its inputs in order, never more slots than that code declares; the remaining inputs must match
   the view's own visible signature, and the bound type is a `Ty.View`, or a `Ty.Owned` whose
   environment is `Unit` for pure code. `Ir.Indirect` matches the `Ty.View`'s *visible* signature.
   A `Unit`-typed parameter is erased when the input plan is built, so it contributes no `Ty.Input`
   and no `Ir.Param` and appears in no argument list. The parameter's name is bound to the `Unit`
   value directly, and because there is no `Ir.Literal` for `Unit`, a `Unit` value can never be
   materialised as an `Ir.Expr`.
6. **Tagged callables.** A `Ty.Tagged` value is a tag plus the environment of the arm that tag
   names. Its arms are registered in `Eval.arms` under the identity that names them in the type, so a
   call site dispatches from the type alone: `Eval:applyTagged` tests each tag, projects that arm's
   environment out of the payload, and calls the arm's own code directly — the arm's environment is
   the call's hidden prefix, exactly as for a non-tagged owned callable. Every arm shares the visible
   signature, so the results join through one slot per result. A join needs both arms to be callables
   of one signature; a word arm needs declared result types and a closure arm may not borrow storage,
   because the value holds its environments by value. Erasing a runtime-tagged value into a signature
   rejects (`callable-erase`).
7. **Sum tags.** `Ir.ConstructVariant`/`Ir.VariantMatches`/`Ir.VariantPayload` each name their
   `Ty.Sum`. The tag must be one of its alternatives; a construct of a `Unit` alternative must omit
   its payload and any other alternative must have one whose type matches; a projection must not
   target a `Unit` alternative, and its operand value must have been bound with that exact sum type.
   A projection is only ever reachable inside an arm whose test established the tag, which is a
   builder obligation the checker cannot see from the statement list alone.
8. **Visible versus actual signature.** `Ty.Owned`/`Ty.View` carry the source-visible signature.
   `Ir.Fn.inputs` carries the actual ABI including the hidden owner/capture prefix. The two are
   related by `Meta.projections`/`hidden` and must not be conflated.
10. **Integer widths.** `Ir.Expr.Convert(operand, type)` is the only conversion, and both its operand
    and its type are integer widths. Arithmetic and bitwise operators take both operands at one width
    and yield it; a shift takes an integer value and a `U32` amount and yields the value's width; a
    comparison takes two integers of any widths and yields `Bool`. Which width an operand needs is
    decided from the source: a literal adopts the other operand's width when it fits, and otherwise
    the wider width wins, so the decision never depends on what happens to be known at compile time.
11. **Indexes.** `Ir.Place.Index(base, index, type)` names one element: the base must be an array,
    the recorded type must be its element type, and the index expression must be a `U32`. A known
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

Every diagnostic carries a span when one exists. `eval` attaches the innermost expression span;
`check` attaches the enclosing `Ir.Fn`'s span from `Meta.spans`. A `Diagnostic` is raised, so
`pcall` boundaries in `cli.lua`/`init.lua` must distinguish it from a Lua error by its `kind` field.

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
top scope, and then compiles the entry module with its own top. `Eval:compile(program, top)` accepts
that pre-loaded scope; `Eval:declareNamespace` puts a namespace in it. A source string cannot resolve
an import, so `compile` rejects a `use` declaration (`import-input`).

Options: `name` (defaults to the path), `limits` (section 9), `target = "c11"`, `inline` (defaults
to `true`: a private function is asked to force-inline on GCC and clang, and is plain `static` on
another C11 compiler), and `symbolPrefix` (defaults to `""`: a prefix for every exported symbol,
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
let inc(x: U32) : U32 = x + 1
let apply(f: (U32): U32, x: U32) : U32 = f(x)
let run(x: U32) : U32 = apply(inc, x)
return { functions = { inc, run } }
```

Resolution: `inc`/`apply`/`run` are top-level; `f`/`x` are params; `apply(inc, x)`'s `inc` is known
code with no captures, so it is a `Static` argument. `apply` is therefore specialised on `inc`, `f` is
erased from the ABI, and `f(x)` becomes a **direct call**. No `Ir.Indirect` is emitted: it is reserved
for a callable whose code is not known in this compilation, which is rejected today rather than
lowered.

Evaluation produces (schematically):

```
Fn id=inc  role=Entry hidden=0 inputs=[InValue U32] results=[U32]
  body: Return( Bin(Add, Ref(x), Const(U32,1)) )        -- x is ValueParam 0

Fn id=run  role=Entry hidden=0 inputs=[InValue U32] results=[U32]
  body: Call([v1], "inc", [ValueArg(Ref(x))])
        Return( Ref(v1) )

Fn id=body#1 role=Body hidden=0 inputs=[InValue U32] results=[U32]
  body: Call([v1], "inc", [ValueArg(Ref(x))])   -- f is a static fact, so no callable input
        Return( Ref(v1) )
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
