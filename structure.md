# Wordlet compiler structure

`architecture.md` specifies what the compiler does. `interfaces.md` specifies the pass order
and the module APIs. This document specifies the shape of the compiler's Lua data and functions —
the tables, the method discipline on the ASDL classes, the supply machine — so that the
implementation reads as if it had been written from the start with the language's current intent
in mind.

It is a design document, not a changelog. Where it disagrees with the current code, it states
what the code should be, not what it is. The last section sequences the migration so that each
step is independently testable.

The ASDL rules in `ASDL.md` are the source of structural truth. Section 0 states the two
principles the rest of this document depends on.

---

## 0. The two ASDL principles

### 0.1 The sum IS the kind

An ASDL sum declares `A | B | C`. The schema is the discriminant. The runtime sets `node.kind`
to the constructor name — `"A"`, `"B"`, `"C"` — so `node.kind == "A"` reads the schema back
out. That is what `|` is for: it types the dispatch. An exhaustive matcher is the schema's
guarantee that no variant is forgotten, and reflection can enumerate every variant.

A tempting "simplification" is to collapse `A | B | C` into a single product with a manually
maintained tag:

```
-- WRONG
X = (string kind, ...)   -- kind = "A" | "B" | "C"
```

This is not a simplification. It defeats the schema. It removes exhaustiveness, removes
reflection, pushes a field name and a string vocabulary into every consumer, and rots when a
fourth variant appears because nothing forces the addition at the use site.

The correct way to share logic across variants of a sum is a *function that accepts several
variants* — a predicate on `.kind` — not a *merged variant*:

```
-- RIGHT
function usesReceiver(callable)   -- accepts word | method | closure
    local k = callable.kind       -- the ASDL-set kind
    return k == "method" or k == "closure"
end
```

### 0.2 The compiler is methods on the ASDL types

The schema declares `Ast.Expr = U32Literal(...) | Apply(...) | ... | Condition(...)`. The
compiler's evaluation of an expression is a method on that class. The variant *owns* the
behavior that names it:

```
function Ast.U32Literal:evaluate(ctx) return eval.literal(ctx, self) end
function Ast.Apply:evaluate(ctx)      return eval.apply(ctx, self) end
function Ast.Condition:evaluate(ctx)  return eval.condition(ctx, self) end
```

The evaluator becomes a call — `expr:evaluate(ctx)` — not a `switch (expr.kind)`. Adding a
new `Ast.Expr` variant means adding a variant method; the caller does not change. Every pass
that reads a particular variant set adds methods to those variants.

The same shape applies to every ASDL family:

| Family | Method set |
| --- | --- |
| `Ast.Expr` | `:evaluate(ctx)`, `:each(fn)` |
| `Ast.Stmt` | `:execute(ctx)`, `:each(fn)` |
| `Ast.Decl` | `:declare(session, scope)`, `:each(fn)` |
| `Ast.Body` | `:run(ctx)`, `:each(fn)` |
| `Ast.ResultSpec` | `:resolve(sc, span)`, `:each(fn)` |
| `Ast.SchemaMember` | `:collect(ctx, def)`, `:each(fn)` |
| `Ast.ExportItem` | `:resolve(session, top)`, `:each(fn)` |
| `Ir.Expr` | `:each(fn)`, `:pure()` |
| `Ir.Stmt` | `:each(fn)`, `:terminates()` |
| `Ir.Place` | `:each(fn)`, `:root()` |
| `Ir.Arg` | `:each(fn)`, `:expr()` |
| `Ty.V` | `:runtime()`, `:representable()`, `:hasNamed()`, `:isIndirection()` |

The parent class gets a default that reports the missing override; each variant overrides it.
`ASDL.md` states the installation rule: install new parent methods first, per-variant methods
second, in the schema-owning module only. A method installed on the parent *fills in* every
variant that has not overridden; a variant override is not overwritten by a later parent install.

`wordlet/schema.lua`, `wordlet/ast.lua`, and `wordlet/ir.lua` are the three
schema-owning modules. They install the parent defaults. The pass modules install the variant
implementations. A helper module that installs a whole method set (`ast_methods.lua`,
`ir_methods.lua`) is the recommended organization, loaded by `wordlet/init.lua` after every
module it names is available.

### 0.3 Reflection is for the structural question, not the semantic one

`walk.lua` reads `class.__fields` reflectively. That answers "what are the children of this
node?" structurally. That is fine and stays; it is how a *generic* traversal is written.

The semantic passes must not be reflective. What a `Reference` means, what an `Apply` means,
what a `Condition` means — those are different askings of each variant, and they belong on the
variant. Reflection cannot answer them, and a `switch (kind)` in the pass module answers them by
bypassing the class. The split is:

```
structural (reflective) : walk.children(node) -- for generic traversals
semantic   (method)     : node:evaluate(ctx)  -- per-variant meaning
```

Neither replaces the other. `walk.lua` is not deprecated by this document; a `switch (kind)` is.

---

## 1. The two-layer rule

`ASDL.md` states:

> Intern immutable type/key/expression descriptions. Do not intern call/store/read/allocation
> occurrences.

The schemas already declare which is which. `Ty.V`, `Ty.Field`, `Ty.Input` carry `unique`.
`Ir.Value`, `Ir.Storage`, `Ir.Expr`, `Ir.Place`, `Ir.Arg`, `Ir.Stmt`, `Ir.Param`, `Ir.Fn` do not.
That is the language's own statement of the compiler's two layers.

### 1.1 Layer 1 — descriptions

Interned, immutable, keyed by identity.

| Type | Meaning |
| --- | --- |
| `Ty.V` | a runtime type or calling requirement |
| `Ty.Field` | a named member of a record, sum, or callable environment |
| `Ty.Input` | an actual ABI input shape: `InValue(T)` or `InPlace(T)` |

A `Ty` is a *token*: two structurally equal types are one value, and `==` is the whole comparison.
Consequences:

- `S.encode(ty)` exists only to build a *key string*. It is never a comparison.
- Every `S.encode(a) ~= S.encode(b)` in the current code is `a ~= b`.
- Type-valued methods (`:runtime()`, `:representable()`, `:hasNamed()`) hold `seen[ty]` and stop
  on a repeat; there is no per-caller cycle-guard logic.
- The number of distinct `Ty` values is bounded by the source schema, not by how often each type
  is written.

### 1.2 Layer 2 — occurrences

Not interned, distinguished by constructor, one `Ir.Fn` at a time.

| Type | Distinction |
| --- | --- |
| `Ir.Value(id)` | an immutable result: from `Let`, `Read`, or `Call` |
| `Ir.Storage(id)` | a mutable cell: from `Var` or `PlaceParam` |
| `Ir.Expr` | a pure expression; a DAG within its own `Ir.Fn` |
| `Ir.Place` | a route to storage; pure to compute |
| `Ir.Stmt` | an ordered effect |
| `Ir.Fn` | one compilation unit; the schema of its own ABI |

A `Builder` interns `Ir.Expr` per `Ir.Fn`, which is exactly why the schema does not inter it
context-wide: `Value` ids are function-local, and a shared cache would collapse two functions'
value 1 into one table. Every analysis of occurrences is therefore *per function*. That is not
an implementation detail; it is a structural property.

`Ir.Fn` is the source of truth for its own ABI: `id`, `role`, `hidden`, `inputs`, `results`,
`params`, `body`. No other table may carry a second copy of those facts.

### 1.3 Which table lives on which layer

| Table | Layer | Keyed by |
| --- | --- | --- |
| `Session.types.cells` | 1 | `Ty.Named.cell` |
| `Session.types.byMeaning` | 1 | `S.encode(ty)` |
| `Session.types.referenced` | 1 | `Ty.Named.cell` |
| `Session.defs` | — | source name |
| `Session.instances`, `Session.order` | 2 | instance key / build index |
| `Session.plans`, `Session.arms` | 2 | plan key / arm key |
| `Session.modules`, `Session.foreigns` | 2 | first-demand order |
| `Builder.memo` (per `Ir.Fn`) | 2 | `Ir.Expr` intern key |
| `Analysis` (per `Ir.Fn`, ephemeral) | 2 | value id / storage id / `Ir.Expr` |

---

## 2. Method discipline

### 2.1 The install shape

Each schema-owning module installs a fallback on the parent:

```lua
-- wordlet/ir.lua, after the context is defined
local Ir = S.Ir

function Ir.Expr:each(fn)
    D.bug("ir-expr", "Ir.Expr variant has no :each method: " .. tostring(self.kind))
end
function Ir.Stmt:each(fn)
    D.bug("ir-stmt", "Ir.Stmt variant has no :each method: " .. tostring(self.kind))
end
```

The variant implementations live in the pass module that owns them:

```lua
-- wordlet/ir_methods.lua  (loaded after ir.lua; installs structural methods)
function Ir.Const:each(fn) end
function Ir.Ref:each(fn) end
function Ir.Un:each(fn) fn(self.operand) end
function Ir.Bin:each(fn) fn(self.left); fn(self.right) end
function Ir.Get:each(fn) fn(self.aggregate) end
function Ir.Make:each(fn) for _, f in ipairs(self.fields) do fn(f) end end
function Ir.Convert:each(fn) fn(self.operand) end
function Ir.Addr:each(fn) self.place:each(fn) end
function Ir.SliceLength:each(fn) fn(self.view) end
function Ir.Null:each(fn) end
```

`ASDL.md`: install the parent method first, the variant overrides second, in the
schema-owning module only. The pass module that owns the semantics owns the variant methods.

### 2.2 The `Ast` family

The compiler's *readers of the source* become methods on `Ast.Expr` etc. Each method takes the
evaluation frame as its argument; the framework does not thread a `kind` around.

```lua
-- wordlet/ast_methods.lua, installed once
local function eval(ast, ctx) return require("wordlet.eval").evaluate(ctx, ast) end

function Ast.Expr:evaluate(ctx)
    D.bug("ast-expr", "Ast.Expr variant has no :evaluate method: " .. tostring(self.kind))
end
function Ast.U32Literal:evaluate(ctx) return eval(self, ctx) end
function Ast.U64Literal:evaluate(ctx) return eval(self, ctx) end
function Ast.BoolLiteral:evaluate(ctx) return eval(self, ctx) end
function Ast.UnitLiteral:evaluate(ctx) return eval(self, ctx) end
function Ast.StringLiteral:evaluate(ctx) return eval(self, ctx) end
function Ast.FloatLiteral:evaluate(ctx) return eval(self, ctx) end
function Ast.Reference:evaluate(ctx) return eval(self, ctx) end
function Ast.Apply:evaluate(ctx) return eval(self, ctx) end
function Ast.FieldSelect:evaluate(ctx) return eval(self, ctx) end
function Ast.RecordSupply:evaluate(ctx) return eval(self, ctx) end
function Ast.ArrayExpr:evaluate(ctx) return eval(self, ctx) end
function Ast.IndexExpr:evaluate(ctx) return eval(self, ctx) end
function Ast.SchemaExpr:evaluate(ctx) return eval(self, ctx) end
function Ast.Lambda:evaluate(ctx) return eval(self, ctx) end
function Ast.SignatureExpr:evaluate(ctx) return eval(self, ctx) end
function Ast.UnaryExpr:evaluate(ctx) return eval(self, ctx) end
function Ast.BinaryExpr:evaluate(ctx) return eval(self, ctx) end
function Ast.Condition:evaluate(ctx) return eval(self, ctx) end
```

The variant methods all call into `eval.evaluate`. This is not a switch in disguise: what
distinguishes the pattern from a `switch` is that **each variant's file owns its own method**,
and adding a variant requires editing *that variant's schema entry* — not a central
dispatcher. When the differences grow, the method body grows in place; when a variant needs
to inherit an implementation from a sibling product, the schema says so.

`Ast.Stmt` follows the same shape with `:execute(ctx)`; `Ast.Decl` with `:declare(session, scope)`;
`Ast.Body` with `:run(ctx)`; `Ast.ResultSpec` with `:resolve(sc, span)`;
`Ast.SchemaMember` with `:collect(ctx, def)`; `Ast.ExportItem` with `:resolve(session, top)`.

### 2.3 The `Ir` family

`Ir.Expr`, `Ir.Stmt`, `Ir.Place`, `Ir.Arg` carry structural and analysis methods.

Structural, as in §2.1. Analysis methods are used by `check.lua`, `cabi.lua` and `lower.lua`
through a visitor object. `check.lua` currently has `M.expr` and `M.place` and a `checkList`
that switches on `stmt.kind`; each variant gains a `:check(visitor)` method and the dispatcher
collapses to `stmt:check(visitor)`.

```lua
-- wordlet/ir_methods.lua
function Ir.Stmt:check(visitor)
    D.bug("ir-stmt", "Ir.Stmt variant has no :check method: " .. tostring(self.kind))
end
function Ir.Let:check(v)
    if v:expr(self.expr) ~= self.type then D.bug("ir-type", "Let type does not match") end
    v:bind(self.value.id, self.type)
end
function Ir.Read:check(v)
    if v:place(self.place) ~= self.type then D.bug("ir-type", "Read type does not match") end
    v:bind(self.value.id, self.type)
end
-- ...
```

`visitor` carries `visible`, `storages`, `inLoop`, plus the shared checks
(`v:expr(...)`, `v:place(...)`, `v:bind(...)`). The visitor is the state; the variants are the
control flow.

The other two IR-shaped methods used by analyses and the emitter are:

```
Ir.Stmt:terminates() -> boolean     -- replaces the free `falls(stmt)` in check.lua
Ir.Stmt:effects()    -> kind        -- "pure" | "write" | "call"
Ir.Expr:pure()       -> boolean     -- whether this expression is safe to move to its use
```

### 2.4 The `Ty` family

`Ty.V` is a semantic type, so its methods are predicates and folds over structure. Each
predicate moves from `S.isX(t)` (free function) to `t:isX()` (method):

```
Ty:isInteger() | :isF64() | :isBool() | :isUnit() | :isType()
Ty:isRecord()  | :isSum() | :isTagged() | :isTaggedType()
Ty:isRef()     | :isPtr() | :isArray() | :isSlice() | :isString()
Ty:isSig()     | :isOwned() | :isView() | :isNamed()
Ty:isIndirection()  -- Ref | Ptr | Slice: one predicate for "has a representation that stops"
Ty:isRuntime()      -- has a C representation
Ty:isRepresentable() -- can appear in a Return (type is fully closed, no open cell)
Ty:hasNamed()       -- mentions an unsealed cell
Ty:environment()    -- Owned -> its environment type, else itself
```

`Ty:isIndirection()` reads `self.kind` and returns true for `"Ref"`, `"Ptr"`, `"Slice"`. It is
a predicate over three variants, not a fourth variant — Section 0.1. `S.encode`, `S.display`
and `S.list` remain free functions over the schema as a whole.

### 2.5 What was a switch, now a method

| Current site | Method |
| --- | --- |
| `Eval:evalExpr`'s `kind` chain | `Ast.Expr:evaluate(ctx)` |
| `Eval:execBlock`'s `kind` chain | `Ast.Stmt:execute(ctx)` |
| `Eval:load`'s `kind` chain | `Ast.Decl:declare(session, scope)` |
| `Eval:resolveExportItem` | `Ast.ExportItem:resolve(session, top)` |
| `Eval:execBody` | `Ast.Body:run(ctx)` |
| `Eval:evalSignature` + callers | `Ast.ResultSpec:resolve(sc, span)` |
| `Eval:newSchema`'s member loop | `Ast.SchemaMember:collect(ctx, def)` |
| `Ir.eachExpr`, `Ir.eachStmt` | `Ir.Expr:each(fn)`, `Ir.Stmt:each(fn)` |
| `check.M.expr`, `check.M.place`, `checkList` | `Ir.Expr:check(v)`, `Ir.Place:check(v)`, `Ir.Stmt:check(v)` |
| `check.falls` | `Ir.Stmt:terminates()` |
| `lower.collectExprs`, `collectPlaceExprs` | `Ir.Expr:each(fn)`, `Ir.Place:each(fn)` |
| `lower.usedStorages`, `usedValues`, `mutatedStorages`, `analyzeSharing`, `analyzeInlining` | one `Analysis` visitor that calls `:each` at nesting points, plus specific `:contains()` methods where shape matters |
| `cabi.liveInstances`' `walk` | `Ir.Stmt:each(fn)` |
| `S.runtime`, `S.representable`, `S.hasNamed`, `Eval:checkNoValueCycle`, `Eval:reachesCell` | `Ty:runtime()`, `Ty:representable()`, `Ty:hasNamed()`, `Ty:isIndirection()` |

Each of those is a place where the current code has a `switch (kind)` and the redesigned code
has a method on the variant. The signature of each method is stable; adding a variant adds a
method, not a switch arm.

---

## 3. Data structures

### 3.1 `Value` — a plain Lua tagged union

`wordlet/value.lua`. Not an ASDL sum, because many variants hold `Ir.Expr` pointers, live
environments, and references into the current activation, none of which should be interned.
The `tag` field plays the same role for `Value` that `.kind` plays for an ASDL node: it is the
constructor name, and it is what every consumer reads.

**The tags stay separate.** `word`, `method`, `closure` are three tags, not one tag with a
`.kind` subfield (Section 0.1). A function that accepts more than one is a predicate on `tag`:

```
-- Callables: three tags, not one
V.word(def, args, span)                                 tag = "word"
V.method(def, receiver, args?)                          tag = "method"
V.closure(plan, bound?)                                 tag = "closure"

-- The shared predicate
V.isCallable(v) = tag(v) == "word" or tag(v) == "method" or tag(v) == "closure"
```

Full tag list:

```
-- Scalars
V.int(ty, n)             tag = "int"
V.int64(ty, high, low)   tag = "int"
V.float(ty, n)           tag = "float"
V.f64(n)                 tag = "float"
V.bool(b)                tag = "bool"
V.unit()                 tag = "unit"
V.string(ty, bytes)      tag = "string"
V.type(ty)               tag = "type"

-- Known immutable aggregates
V.record(ty, fields, schema?)               tag = "record"
V.array(ty, items, place?, borrowed?, ...)  tag = "array"
V.variant(ty, case, payload, expr?)         tag = "variant"
V.slice(ty, source, start, count, tied)     tag = "slice"
V.ref(ty, place, schema?, tied?, record?)   tag = "ref"

-- Residual values
V.runtime(expr, ty, borrowed?, place?)      tag = "runtime"
V.object(ty, place, schema, ...)            tag = "object"

-- Callables
V.word(def, args, span)                     tag = "word"
V.method(def, receiver, args?)              tag = "method"
V.closure(plan, bound?)                     tag = "closure"

-- Static descriptors
V.schema(def)                               tag = "schema"
V.ctor(sum, case, caseType)                 tag = "ctor"
V.namespace(module, members)                tag = "namespace"

-- Result vector
V.results(values)                           tag = "results"
```

The only rename is `ir` → `runtime`: the tag was never about the value being an `Ir.Expr`, it was
about the value's representation being a residual expression.

### 3.2 `Session`

`wordlet/session.lua` (new module, extracted from `eval.lua`). One per compilation; never reused.

```
Session = {
    -- Configuration, read-only after construction.
    options = { name, inline, symbolPrefix },
    limits  = { buildDepth, staticDepth, interpretDepth, steps, keys },

    -- Descriptions. Grow with distinct types only.
    types = {
        cells      = {},   -- Ty.Named.cell -> Ty            (sealed recursive definitions)
        byMeaning  = {},   -- S.encode(ty)    -> Ty.Named     (structural identity of a knot)
        referenced = {},   -- Ty.Named.cell  -> true          (cells named through Ref/Ptr/Slice)
    },

    -- Occurrences. Grow with distinct specializations only.
    defs      = {},        -- source name -> Definition
    instances = {},        -- instance key -> Instance
    order     = {},        -- Instance[], build order
    plans     = {},        -- plan key -> closure plan
    arms      = {},        -- arm key -> tagged-arm descriptor
    modules   = {},        -- module storage entries, first-demand order
    foreigns  = { instances = {}, order = {} },

    -- Identity allocators.
    nextDef, nextFn, nextModule, nextCell,

    -- Budget counters, reset per compilation.
    steps, buildDepth, staticDepth,

    -- Compile-wide mode.
    top,        -- current top scope
    run,        -- reference interpreter: reads and writes module storage
    demanding,  -- module initializer
}
```

The constructor is the only entry point:

```
Session.new(options) -> Session
```

The current `options.session` parameter in `M.compile` is a fossil — accepted, then refused by
a `D.bug`. Delete it; sessions are always fresh.

`Session:withNesting(kind, span, fn, ...)` replaces `enterBuild`/`leaveBuild` and
`enterStatic`/`leaveStatic`. `kind` is `"build"` or `"static"`. The limit for `"static"` is
`run and limits.interpretDepth or limits.staticDepth`; the message names the scope.

### 3.3 `Frame`

One context per body construction. `residual` replaces `mode`. `Frame:arm` copies all fields
and overrides `body`, so a new field cannot be forgotten.

```
Frame = {
    session,
    residual,          -- true = emits Ir; false = normalization / interpreter
    scope,             -- lexical scope
    span,
    body,              -- Ir.Stmt list (residual only)
    builder,           -- Ir.builder (residual only)
    instance,          -- Instance under construction (residual only)
    tail,              -- is the current expression in tail position
    expectedResult,    -- a signature from an annotation context, if any
    deferFrame,        -- pending deferred actions
    terminated,        -- the current list was terminated
}
```

```
function Frame:arm(list)
    local child = setmetatable({}, Frame)
    for k, v in pairs(self) do child[k] = v end
    child.body = list
    return child
end
```

The rename and the copy-all pattern remove the current risk in `Ctx:arm` of forgetting a field
when the context grows.

### 3.4 `Instance`

The current `Instance` duplicates what `Ir.Fn` already declares. Remove the duplication: `fn`
is the source of truth; `abi` is derived once at seal time.

```
Instance = {
    key,                -- cache key
    code,               -- the code shape: { tag = "word"|"method"|"closure", def, plan?, receiver? }
    fn,                 -- Ir.Fn; the ABI is `fn.inputs`, `fn.results`, `fn.params`, `fn.hidden`
    status,             -- "building" | "done" | "failed"
    failure,            -- a Diagnostic if status == "failed"

    abi = {
        plan    = ..., -- { kind = "value"|"place", position = i }[]
        types   = ..., -- parallel Ty[] (fn.inputs, unwrapped)
        params  = ..., -- index into fn.params
        result  = ..., -- "void" | "scalar" | "tuple"
    },

    -- Tail-self bookkeeping. Present only while a body is being built.
    loopTargets, loopBack, loopHeader,
}
```

`Eval:callInstance` and `Eval:constructInstance` both read `instance.abi`; neither derives from
parallel tables that could drift.

### 3.5 `Analysis`

Per `Ir.Fn`, ephemeral, computed once by a visitor over `Ir.Stmt:each` and its variants.

```
Analysis = {
    valueUses       = {},  -- value id -> count
    storageUses     = {},  -- storage id -> true
    mutatedStorages = {},  -- storage id -> true (stored to, borrowed, addressed)
    shared          = {},  -- Ir.Expr -> true (used more than once)
    sharedDecls     = {},  -- list -> index -> { Ir.Expr, ... }
    inline          = {},  -- value id -> { stmt | place }
    paramValues     = {},  -- value id -> true (parameter binding)
}
```

`lower.lua`'s five separate walks (`usedStorages`, `usedValues`, `mutatedStorages`,
`analyzeSharing`, `analyzeInlining`) become one pass, because each walk wants the same
information and the visitor already visits each node once.

---

## 4. The supply machine

`syntax.md` §3 defines one law: evaluate the callee, evaluate the arguments left to right,
append them to the word's bound arguments, test saturation. Every call in the language follows
it. The compiler must therefore have **one function** that answers "given a callable and
arguments, what happens next", not eleven.

```
Eval:supply(ctx, callee, args, span)
    -> Word value       (partial: returns a word)
    -> Method value     (partial: returns a method with bound args)
    -> Closure value    (partial: returns a closure)
    -> the terminal's Value (saturated: runs, folds, or emits a Call)
```

`supply` dispatches on the callee's kind for the four variants that can be *called*. The
implementation moves the existing `apply`/`applyClosure`/`applyMethod` bodies under one roof.

The saturation terminal has four cases, one per way the language provides a body:

| Callee | Saturated call |
| --- | --- |
| `word` with `def.builtin` | `Eval:invokeBuiltin(ctx, def, args, span)` |
| `word` with `def.foreign` | `Eval:invokeForeign(ctx, def, args, span)` |
| `word` with a source body | `Eval:invokeSource(ctx, def, args, span)` |
| `method` | `Eval:invokeMethod(ctx, method, args, span)` |
| `closure` | `Eval:invokeClosure(ctx, closure, args, span)` |

Each of these either folds (when all arguments are known and the body's evaluation finishes
statically) or builds an instance. The four share one helper:

```
Eval:foldOrBuild(ctx, code, args, span) -> Value
```

`invokeSource`, `invokeMethod` and `invokeClosure` are the three that build an `Instance`.
`invokeBuiltin` and `invokeForeign` never build one.

The runtime-callable cases (values whose *representation* is a callable), which today are
`applyOwned`, `applyView`, `applyTagged`, become:

```
Eval:invokeRuntime(ctx, runtime, args, span) -> Value
```

dispatched by what the *type* says the runtime value is:

| `runtime.ty` | Path |
| --- | --- |
| `Ty.Owned` (known code) | project the environment, then `invokeSource`/`invokeClosure` |
| `Ty.View` (opaque code) | emit `Ir.Indirect` |
| `Ty.Tagged` (arm selection) | emit the tag switch, run the selected arm |
| `Ty.Sig` | `D.todo("opaque-callable", ...)` — a signature is not yet a callable ABI |

The current three functions `applyOwned`, `applyView`, `applyTagged` are merged under this
dispatch. The current `invoke` (used by deferred actions) and `applyAny` (used by matches)
become calls into `supply` with the same kind, because a deferred call and a match handler call
are both ordinary applications of an already-evaluated callee.

After this:

```
Eval:supply          -- one entry, dispatches on the callee's kind
Eval:invokeBuiltin   -- intrinsic
Eval:invokeForeign   -- extern
Eval:invokeSource    -- named word with a source body
Eval:invokeMethod    -- method on a receiver
Eval:invokeClosure   -- closure with an environment
Eval:invokeRuntime   -- runtime callable, dispatched on the type
Eval:foldOrBuild     -- shared fold-vs-residual decision
Eval:callInstance    -- emit a Call to a ready Instance
Eval:loopBack        -- emit a Loop back edge for a self-tail call
```

Nine functions, disjoint domains, one law. Today there are eleven with overlaps and four
duplicate dispatchers.

### 4.1 Schematic flow of a source call

```
source apply node
   │
   Ast.Apply:evaluate(ctx)
   │
   Eval:evaluate(ctx, apply)
   │
   Eval:supply(ctx, callee, args, span)
   │  ├─ callee is a static word/method/closure
   │  │     ├─ foldOrBuild decides fold vs. build
   │  │     │     ├─ fold: return the value
   │  │     │     └─ build: instanceFor + callInstance
   │  │     └─ partial: return the word with more bound args
   │  │
   │  └─ callee is a runtime callable
   │        invokeRuntime dispatches on runtime.ty
   │
   Value
```

Every edge is a method or a named function. No `switch (kind)` appears.

---

## 5. Migration order

Each step is a self-contained change that passes `tests/run.lua` before and after. Commit per
step.

### 5.1 Step 1 — schema corrections

The four fixes from the earlier ASDL review:

1. `attributes (Span span)` uniformly on every span-carrying sum (`Decl`, `Stmt`,
   `SchemaMember`, `Param`, `Binder`, `FieldSupply`). Remove the redundant `Span span` on
   their variants.
2. `Field tag` on `Ir.ConstructVariant`, `Ir.VariantMatches`, `Ir.VariantPayload`; drop the
   `string tag` field.
3. Mark `Ir.Literal` `unique`.
4. `Ast.UseDecl` loses `Name name`; the loader derives the lexical name from `path`.
5. Delete the `Ir.Bundle` sentence from the `ir.asdl` header and the unused `seen` parameter on
   `S.encode`.
6. Document the "at most one of `params`/`keyed` is non-empty" invariant on `Ast.WordDef` and
   check it in `parse.lua`.

No behavior changes. Regenerate `wordlet/schema/ast.lua` and `wordlet/schema/ir.lua`
(`luajit tools/embed.lua`).

### 5.2 Step 2 — the `Ir` methods

Install `Ir.Expr:each`, `Ir.Stmt:each`, `Ir.Place:each`, `Ir.Arg:each`, `Ir.Expr:pure`,
`Ir.Stmt:terminates` and `Ir.Stmt:effects` in a new `wordlet/ir_methods.lua`, required from
`wordlet/init.lua`. Rewrite `wordlet/ir.lua`'s `eachExpr`/`eachStmt` as dispatch through the
parent default (§2.1) and make every current caller of them call the method instead.

Rewrite `wordlet/check.lua`'s `checkList`, `M.expr`, `M.place` as `Ir.Stmt:check(visitor)`,
`Ir.Expr:check(visitor)`, `Ir.Place:check(visitor)`. Rewrite `falls` as
`Ir.Stmt:terminates`.

Rewrite `wordlet/cabi.lua`'s `liveInstances` to call `Ir.Stmt:each`.

Migration of `wordlet/lower.lua`'s five analyses onto a visitor over `Ir.Stmt:each` can happen
in the same step or the next.

### 5.3 Step 3 — the `Ast` methods and the evaluator split

Add `wordlet/ast_methods.lua` with `Ast.Expr:evaluate`, `Ast.Stmt:execute`,
`Ast.Decl:declare`, `Ast.Body:run`, `Ast.ResultSpec:resolve`, `Ast.SchemaMember:collect`,
`Ast.ExportItem:resolve`, and `Ast.Expr:each`. Each method's implementation moves to the
corresponding `Eval:` function, which is unchanged; only the dispatch changes.

`Eval:evalExpr` becomes `return expr:evaluate(ctx)`. `Eval:execBlock` calls
`stmt:execute(ctx)` in its loop. `Eval:load` calls `decl:declare(self, top)`.

This step is the one with the largest diff and the largest benefit: eleven dispatchers become
eleven functions each reached through one method.

### 5.4 Step 4 — the supply machine

Add `Eval:foldOrBuild`, `Eval:invokeSource`, `Eval:invokeMethod`, `Eval:invokeClosure`,
`Eval:invokeBuiltin`, `Eval:invokeForeign` and `Eval:invokeRuntime`. Rewrite `Eval:apply`,
`Eval:applyKeyed`, `Eval:applyClosure`, `Eval:applyMethod`, `Eval:applyForeign`,
`Eval:applyOwned`, `Eval:applyView`, `Eval:applyTagged`, `Eval:applyAny`, `Eval:invoke` as
calls into them.

The most consequential fix in this step is the one the earlier review named: `applyKeyed` must
use the parameter annotation to type an un-annotated lambda argument, exactly as
`evalArguments` does. Unifying the two paths is how that gets fixed for free.

`Eval:applyStatically`/`applyClosureStatically` collapse into `foldOrBuild`'s fold branch.

### 5.5 Step 5 — the `Session` split and `Frame`

Extract `wordlet/session.lua` and change the field group `types`/occurrences/allocators/budgets/
mode. Change `Ctx` to `Frame` with `residual` instead of `mode`, and `Frame:arm` copying all
fields.

`Eval:enterBuild`/`leaveBuild`/`enterStatic`/`leaveStatic` become `Session:withNesting`.

### 5.6 Step 6 — the `Ty` methods and the type walkers

Add `Ty:runtime`, `Ty:representable`, `Ty:hasNamed`, `Ty:isIndirection`, `Ty:environment` and
the family predicates. Rewrite `wordlet/schema.lua`'s `M.runtime`, `M.representable`,
`M.hasNamed` as method implementations. Rewrite `Eval:checkNoValueCycle` and
`Eval:reachesCell` on top of the same methods.

Replace `S.encode(a) ~= S.encode(b)` in every comparison site with `a ~= b`.

### 5.7 Step 7 — the `Value` tags and the historical cleanups

Rename `V.ir` to `V.runtime` and update every read. Rename the tags if desired but not the
union: `word`, `method`, `closure` stay three tags (§0.1).

Delete the historical comments in `eval.lua` and `lower.lua` that describe a version of the
code that no longer exists. Delete the dead fields (`signature.hidden` in `cabi.lua`,
`initialiser = true` on the module-init entry, `checkAnnotation`'s unused `ctx`, `readSlot`'s
unused `span` on non-residual branches, `M.spanFrom` in `parse.lua`).

Delete the `options.session` parameter from `M.compile` and its refusal branch.

### 5.8 Step 8 — `lower.lua` and `cabi.lua` cleanup

Split the `Layouts` registry: one table per family with one `order` list, and a
`layoutName(prefix, index)` helper.

Replace `M.typeDeclarations`' `define`/`needs`/`emit` fixpoint with a DFS over the by-value
dependency graph (`Ty` knows its by-value children; the graph lives on `Layouts`).

Make `M.unit(layouts)` be `M.source(layouts, nil)`.

Make `cabi.close` call `M.bodies` once, eagerly, and mark the layouts as closed, so
`unit`/`source`/`header`/`cdef` only read.

### 5.9 Step 9 — the analysis consolidation

Add `wordlet/analysis.lua` with `M.analyze(fn) -> Analysis`. Replace `lower.lua`'s five walks
with the single pass, and rewrite the emitter's reads to come from one object.

---

## 6. What this structure buys

- **Adding a variant is local.** It is a new ASDL entry, and one new method in the schema-owning
  or pass-owning module. Nothing centrally dispatches on the union of kinds.
- **Exhaustiveness is in the schema.** A missing variant method is a `D.bug` in the parent
  default that names the variant; nothing has to be audited.
- **The evaluator's shape matches the language's shape.** A word is a value with a `:supply`
  behavior; a sum's match is a value with a `:tag` behavior; the schema says both, the code
  implements both.
- **`Interfaces.md`'s pass order is visible.** Lex produces `Token[]`; parse produces `Ast.*`
  nodes with `:each` and `:evaluate` methods; eval produces `Ir.Fn`s with `:each` and `:check`
  methods; check, cabi and lower read methods, not `kind` fields.
- **The "written from the first day" test.** Any file that reads better as a method set than as
  a dispatcher has been placed as a method set. Any file that reads as a dispatcher has a
  schema that was not used.
