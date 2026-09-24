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

### 0.2 Methods are used sparingly, and their install is ordered

A variant *can* own behavior, and the schema is where its arm is declared. The question this
document answers is where a method is the right shape. It uses methods for two things and
nothing else:

- **Structural traversal.** `Ir.Expr:each(fn)` visits the value/place/argument children. That is
  a direct structural question, the same for every variant, and safe on the variant.
- **Intrinsic type predicates.** `Ty:isRecord()`, `Ty:isIndirection()` read only `self`, so they
  are safe on an interned node. A predicate that carries a `seen`/`visiting` set is *not*
  intrinsic and stays a free function (§2.4).

Semantic *behavior* — how an expression evaluates, how a statement completes, what a check
requires — is not moved onto the classes. It stays in the pass that owns it, reached through the
per-variant functions and explicit visitors that already exist. `ASDL.md` is explicit ("Reflection
enumerates structure, not control completion, SSA definitions, effects or borrowing. Implement
exhaustive semantic visitors for those tasks"), and `walk.lua`'s own header repeats it ("every
semantic question ... stays in an explicit visitor"). Today the project installs **no** class
methods at all; `walk.lua` is reflective and every pass is a switch.

The method sets are therefore small:

| Family | Method set |
| --- | --- |
| `Ir.Expr` | `:each(fn)` |
| `Ir.Stmt` | `:each(fn)` |
| `Ir.Place` | `:each(fn)` |
| `Ir.Arg` | `:each(fn)` |
| `Ty.V` | the intrinsic predicates of §2.4 |

No `Ast.*` methods, and no `:check`/`:pure`/`:terminates`/`:effects` methods (§2.2, §2.3).

The parent class gets a default that reports the missing override; each variant overrides it.
`ASDL.md` states the install rule more strictly than it first reads: install parent methods
first, per-variant methods second, in the schema-owning module only.

The reason is `vendor/asdl.lua`'s `DefineClass`. A class's metatable has an `__newindex` that, the
first time a new key is assigned to a parent, runs `for c in self.members do rawset(c, k, v)` — it
raw-sets that key onto *every* member, including every variant that already overrode it. A parent
method installed after the variants therefore **overwrites all of them**; it does not fill in only
the missing ones. A second assignment to the same parent key does not propagate, because the key
is then present and `__newindex` does not fire — the hazard is the first install. Correctness
depends on install order, so there must be exactly one owner.

`wordlet/schema.lua`, `wordlet/ast.lua`, and `wordlet/ir.lua` are the three schema-owning modules.
`ir.lua` installs the structural `:each` methods and `schema.lua` installs the intrinsic `Ty`
predicates; `ast.lua` installs nothing, because there are no `Ast.*` methods (§2.2). A sibling
file is allowed only if the schema module itself requires it during its own initialization
(`ir.lua` ending in `require("wordlet.ir_methods")`), so the install order is fixed by the schema
module alone; `init.lua` never loads a method file, and no pass module assigns to a class. Pass
modules contribute *visitor objects* — tables of per-variant functions the methods call through
`self` — not mutation.

### 0.3 Reflection is for the structural question, not the semantic one

`walk.lua` reads `class.__fields` reflectively. That answers "what are the children of this
node?" structurally. That is fine and stays; it is how a *generic* traversal is written.

The semantic passes must not be reflective. What a `Reference` means, what an `Apply` means, what
a `Condition` means are different askings of each variant. But the variant answer is not
automatically a class method. The evaluator already answers each one with a per-variant function —
`Eval:evalReference`, `Eval:evalApply`, `Eval:evalCondition`, and the rest — and the only `kind`
read is one router at the top of `Eval:evalExpr`, a line per variant. That router is a dispatch
table that names the variant's own function; it is not what this document is against. What it is
against is a class method whose body forwards to one shared function (indirection with no variant
meaning), or new per-variant behavior accumulated in a second, growing `switch` when the variant
is the natural owner. The real split is:

```
structure  : walk.children(node)            -- reflective, for generic traversals
dispatch   : Eval:eval<Variant>(ctx, node)  -- a router to per-variant functions
ownership  : Ir.Stmt:each(fn), Ty:isRecord() -- a method, when the variant owns the behavior
```

`walk.lua` is not deprecated by this document, and neither is a small router at a pass entry
point. The thing that must not appear is a second `switch` beside the router.

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
- The cycle-aware type folds (`S.runtime`, `S.representable`, `S.hasNamed`) hold `seen[ty]` and
  stop on a repeat; the intrinsic predicates of §2.4 have no state. There is no per-caller
  cycle-guard logic.
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

The schema-owning module installs the parent defaults first and the variant methods second, in
one ordered pass:

```lua
-- wordlet/ir.lua (or a file it requires at its end), before any pass is loaded
function Ir.Expr:each(fn)
    D.bug("ir-expr", "Ir.Expr variant has no :each method: " .. tostring(self.kind))
end
function Ir.Stmt:each(fn)
    D.bug("ir-stmt", "Ir.Stmt variant has no :each method: " .. tostring(self.kind))
end

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

All parent defaults must be installed before the first variant method, because — per §0.2 — the
first assignment of a parent key raw-sets it onto every member and would otherwise wipe the
variant methods out. That is why the two groups cannot be split across modules that load in an
unspecified order.

### 2.2 The `Ast` family: no methods

The AST does not get a method per variant, and that is a decision, not an omission. The evaluator
already dispatches to a per-variant function — `Eval:evalReference`, `Eval:evalApply`,
`Eval:evalUnary`, `Eval:evalBinary`, `Eval:evalCondition`, `Eval:evalSchema`, `Eval:evalArray`,
`Eval:evalIndex`, `Eval:evalSupply`, `Eval:evalFieldSelect`, `Eval:evalLambda`,
`Eval:evalSignature` — with the literals as a few lines in `Eval:evalExpr` itself. A method
`Ast.Apply:evaluate = function(self, ctx) return evalApply(ctx, self) end` would relocate those
twelve calls into twelve class slots while leaving the router and the functions exactly where they
are: one more layer, with the variant owning nothing new. That is the indirection §0.3 rejects,
and it is the shape `walk.lua`'s header warns against.

So `ast.lua` installs no behavior. Structural traversal stays in `walk.lua` (which reads
`__fields`), and the evaluator keeps its router and its per-variant functions. If a variant's body
later grows branches that are about that variant alone, it becomes a new `Eval:evalX`; if it grows
state that belongs to the node, that is a schema question first.

There is therefore no `Ast.Expr:evaluate`, no `Ast.Stmt:execute`, and no `ast_methods.lua`.

### 2.3 The `Ir` family: structure only

The `Ir` classes gain exactly the structural traversal methods of §2.1 — `:each` over value,
place and argument children — and nothing else. Control completion, effects and purity are the
things `ASDL.md` says reflection cannot answer and that `check.lua` already answers in an explicit
visitor (`falls`, `checkList`, `M.expr`, `M.place`). They stay there. A `:terminates`/`:effects`/
`:pure` class method would move a semantic rule onto a non-interned occurrence node and split it
from the visitor that carries `visible`/`storages`, which is the spread `ASDL.md` forbids.

So `check.lua` and `lower.lua` keep their switches; what changes is only that they iterate children
through `node:each(fn)` instead of the free `eachExpr`/`eachStmt`.

### 2.4 The `Ty` family

Only the *intrinsic* predicates move onto `Ty.V`; the cycle-aware folds do not. `ASDL.md`:
"Methods on interned objects must be intrinsic. Put use counts, source provenance, names,
initialization facts and all contextual analysis in pass-owned side tables." A predicate that
reads only `self` is intrinsic. A fold that carries a `seen`/`visiting` set is contextual state and
stays a free function with an explicit parameter.

Methods, installed in `schema.lua` (the `Ty`-owning module), in place of the current `S.isX(t)`:

```
Ty:isU32() :isU8() :isU16() :isInteger() :isNumeric() :isWide() :isSigned() :isF64()
Ty:isBool() :isUnit() :isType()
Ty:isRecord() :isSig() :isSum() :isTagged() :isTaggedType()
Ty:isRef() :isPtr() :isArray() :isSlice() :isString()
Ty:isNamed() :isOwned() :isView()
Ty:isIndirection()   -- Ref | Ptr | Slice: "has a representation that stops", a predicate over
                     -- three variants, not a fourth variant (§0.1)
```

Free functions that keep an explicit walk state, unchanged in kind:

```
S.runtime(t, seen)        -- has a C representation
S.representable(t, seen)  -- can appear in a Return (fully closed, no open cell)
S.hasNamed(t, seen)       -- mentions an unsealed cell
S.environmentOf(t)        -- Owned -> its environment type, else itself (intrinsic; may move)
```

`S.encode`, `S.display` and `S.list` remain free functions over the schema as a whole.

### 2.5 What becomes a method, and what stays a switch

| Current site | Target |
| --- | --- |
| `Eval:evalExpr`'s `kind` chain | keep the router; each arm already names `Eval:eval<Variant>` |
| `Eval:execBlock`, `Eval:execBody`, `Eval:load`, `Eval:newSchema` | keep their dispatch (per-variant `Eval:` functions, not class methods) |
| `Ir.eachExpr`, `Ir.eachStmt` | `Ir.Expr:each(fn)`, `Ir.Stmt:each(fn)` |
| `check.M.expr`, `check.M.place`, `checkList`, `check.falls` | keep as the explicit `check.lua` visitor |
| `lower.collectExprs`, `collectPlaceExprs` | `Ir.Expr:each(fn)`, `Ir.Place:each(fn)` |
| `lower.usedStorages`, `usedValues`, `mutatedStorages`, `analyzeSharing`, `analyzeInlining` | one `Analysis` visitor over `Ir.Stmt:each` (Step 9) |
| `cabi.liveInstances`' `walk` | `Ir.Stmt:each(fn)` |
| `S.isRecord` … `S.isView`, plus a new `isIndirection` | intrinsic `Ty:` methods |
| `S.runtime`, `S.representable`, `S.hasNamed` | stay free functions; they carry a `seen` |
| the four `S.encode(a) ~= S.encode(b)` sites | `a ~= b` (interned `Ty` identity) |

Each row is either a structural traversal (safe on the variant) or a place the current code has a
semantic `switch` and the redesign keeps it explicit. Only the structural traversals and the
intrinsic `Ty` predicates become methods.

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
V.callable(ty, code)                        tag = "callable"  -- Owned/View/Tagged/Sig code

-- Static descriptors
V.schema(def)                               tag = "schema"
V.ctor(sum, case, caseType)                 tag = "ctor"
V.namespace(module, members)                tag = "namespace"

-- Result vector
V.results(values)                           tag = "results"
```

The one tag rename is `ir` → `runtime`: the tag was never about the value being an `Ir.Expr`, it
was about the value's representation being a residual expression. The list above is the complete
target; `V.callable(ty, code)` (tag `"callable"`) is added under Callables.

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
    instanceCount,          -- cardinality of instances, including building/failed/module-init entries
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

The current `options.session` parameter in `M.compile` is a fossil: it is accepted and used, and
the `D.bug` fires only when the passed session already has instances. Delete it; sessions are
always fresh.

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
arguments, what happens next", not fifteen.

```
Eval:supply(ctx, callee, args, span)
    -> Word value       (partial: returns a word)
    -> Method value     (partial: returns a method with bound args)
    -> Closure value    (partial: returns a closure)
    -> the terminal's Value (saturated: runs, folds, or emits a Call)
```

`supply` dispatches on the callee's kind for the four variants that can be *called*. The
implementation moves the existing `apply`/`applyClosure`/`applyMethod` bodies under one roof.

The saturation terminal has five cases, one per way the language provides a body:

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

Ten functions, disjoint domains, one law. Today there are fifteen `apply*`/`invoke*` entry points
with overlapping saturation logic and duplicate callee dispatchers (`apply`, `applyKeyed`,
`applyClosure`, `applyMethod`, `applyForeign`, `applyOwned`, `applyView`, `applyTagged`,
`applyAny`, `invoke`, `applyStatically`, `applyClosureStatically`, `applyResidual`,
`applyMethodResidual`, `applyConversion`).

### 4.1 Schematic flow of a source call

```
source apply node
   │
   Eval:evalExpr(ctx, apply)      -- one-line router over the Ast.Expr kind
   │
   Eval:evalApply(ctx, apply)
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

Every edge is a named function or a method. The only `kind` read is the one-line router at the top
of `Eval:evalExpr`.

---

## 5. Migration order

Each step is a self-contained change that passes `tests/run.lua` before and after. Commit per
step.

### 5.1 Step 1 — schema corrections

1. `attributes (Span span)` on the three real sums that carry it: `Decl`, `Stmt`, `SchemaMember`.
   Remove the redundant `Span span` from their variants. `attributes` is sum-only (`parseSum`);
   `Param`, `Binder` and `FieldSupply` are products and keep an explicit `Span span`.
2. Keep `string tag` on `Ir.ConstructVariant`, `Ir.VariantMatches` and `Ir.VariantPayload`.
   Interning the tag as an `Ir.Field` would rewrite every construction and read to buy identity
   comparison no consumer currently needs; revisit only if one appears.
3. Mark each `Literal` constructor `unique`: `unique` is per-constructor
   (`DefineClass(c.name, c.unique, ...)`), not per-sum, so `UInt(...) unique | UInt64(...) unique
   | ...`.
4. `Ast.UseDecl` loses `Name name`; the loader derives the lexical name from `path`.
5. Delete the `Bundle` sentence from the `ir.asdl` header and the unused `seen` parameter on
   `M.encode` (`wordlet/schema.lua:253`).
6. Document the "at most one of `params`/`keyed` is non-empty" invariant on `Ast.WordDef` and
   check it in `parse.lua`.

No behavior changes. Regenerate `wordlet/schema/ast.lua` and `wordlet/schema/ir.lua`
(`luajit tools/embed.lua`).

### 5.2 Step 2 — the `Ir` structural methods

Add `Ir.Expr:each`, `Ir.Stmt:each`, `Ir.Place:each`, `Ir.Arg:each` in `wordlet/ir.lua`, after the
parent defaults and before anything requires `ir` (§2.1), replacing the current free
`eachExpr`/`eachStmt`. Make every caller use the method. This is structural traversal only:
`ASDL.md` and `walk.lua` both keep control completion, effects and borrowing in explicit
visitors, so `terminates`/`effects`/`pure` do **not** become class methods. `check.lua`'s
`falls`, `M.expr`, `M.place` and `checkList` stay as they are (tidy them if useful, but they
remain the visitor).

Rewrite `wordlet/cabi.lua`'s `liveInstances` to call `Ir.Stmt:each`.

Migration of `wordlet/lower.lua`'s five analyses onto a visitor over `Ir.Stmt:each` is Step 9.

### 5.3 Step 3 — dropped

There is no AST method step. The evaluator already routes each variant to an `Eval:evalX`
function, so the only change would be twelve class methods that call the function already being
called (§2.2). It is removed from the sequence rather than deferred.

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

### 5.6 Step 6 — the `Ty` predicates

Move the intrinsic predicates onto `Ty.V` (§2.4): the family predicates and `isIndirection`.
Leave `S.runtime`, `S.representable` and `S.hasNamed` as free functions, because each carries a
`seen`/`visiting` set — contextual state, which `ASDL.md` keeps off interned nodes. Rewrite
`Eval:checkNoValueCycle` and the new `Eval:reachesCell` (the case-cycle check) to share those
free folds rather than each carrying its own walk.

Replace the four `S.encode(a) ~= S.encode(b)` comparison sites with `a ~= b`; all four compare
interned `Ty` values, so identity is the comparison (`check.lua:176`; `eval.lua:1685`, `1883`,
`1886`).

### 5.7 Step 7 — the `Value` tags and the historical cleanups

Rename `V.ir` to `V.runtime` and update every read. Rename tags only if a name is wrong, but keep
the union split: `word`, `method`, `closure` stay three tags, and `callable` is its own tag rather
than a merge with them (§0.1).

Delete the historical comments in `eval.lua` and `lower.lua` that describe a version of the
code that no longer exists. Delete the dead fields: `signature.hidden` in `cabi.lua` (stored, never read), `initialiser = true`
on the module-init entry (`eval.lua:395`), `readSlot`'s unused `span` on non-residual branches,
and the dead `M.spanFrom = S` re-export in `parse.lua`. `checkAnnotation`'s `ctx` **is** used
(`ctx.scope`), so it stays; the earlier plan was wrong about that one.

Delete the `options.session` parameter from `M.compile`. It is not merely refused today:
`Eval.session(options)` is always called and `options.session` is used, with `D.bug` firing only
if the passed session already has instances (`init.lua:31-35`). Sessions are always fresh, so the
parameter and the branch both go.

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

- **Adding a variant is local.** It is a new ASDL entry, plus — only where a structural traversal
  exists — one `:each` arm. No central `switch` over the union of kinds grows.
- **Structural exhaustiveness is in the schema.** A missing `:each` arm is a `D.bug` in the parent
  default that names the variant. Semantic completeness stays the pass visitor's duty, as
  `ASDL.md` requires.
- **The evaluator's shape matches the language's shape.** A callable is a value the supply machine
  dispatches on; a sum's match is a value dispatched on its tag; both are ordinary functions, not
  class methods.
- **`interfaces.md`'s pass order is visible.** Lex produces `Token[]`; parse produces `Ast.*`
  nodes that `walk.lua` traverses structurally; eval produces `Ir.Fn`s whose statements traverse
  through `Ir.Stmt:each`; check, cabi and lower consume IR and their own visitors.
- **The "written from the first day" test.** A file that reads better as a data table has been
  made one. A file that reads as an unowned switch has a visitor waiting to be named.
