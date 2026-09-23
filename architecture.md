# Wordlet — target architecture

For the language in `syntax.md`. Wordlet owns its syntax. The compiler interprets an AST over
known values and runtime values, producing a structured residual program.

This is a replacement architecture, not a compatibility plan for the Lua-hosted implementation.
`syntax.md` governs the surface language; section 13 records the corresponding implementation
rules. `README.md`, `ASDL.md`, `VALIDATION.md` and the vendored tooling complete this standalone project.
No parent repository or earlier language document is required to interpret this contract.

The central commitments are words, demand-driven evaluation, static specialization, immutable
lexical bindings, mutable record fields, value copies and actual lexical receivers. ASDL defines
AST, semantic descriptors and IR eagerly. Mutable environments, registries and analysis side tables
are compiler state; it is not meaningful to claim that the AST and IR are the only data structures.

## 1. Pipeline and visibility

```text
source -> lex -> parse -> AST
                         |
                         v
                  staged evaluator <-> instance registry
                         |
                         v
                typed structured functions
                         |
                         v
                       check
                         |
                         v
                 C ABI/layout closure
                         |
                         v
                  header + source
```

Only the evaluator evaluates source expressions. Verification, ABI closure and emission see typed
compiler data, never AST bodies to reinterpret. These are distinct responsibilities even when small
implementations share a module. There is no promise that checking, use counting, layout closure and
emission constitute one traversal.

Lexing is free-form: whitespace and newlines do not produce INDENT/DEDENT. Parsing uses the explicit
`do`, `then`, `else`, `end`, delimiters and declaration syntax. A file is a module whose final export
value selects functions, types and result contracts. There is no `pub` declaration or import system
in this target until the syntax specifies one.

## 2. Structured control flow

IR contains ordered statement lists, nested conditionals and loops. A conditional's continuation is
structurally explicit; the compiler does not recover it from a Lua stack or a line number.

Consequences:

- each unknown conditional arm is elaborated once per specialization;
- effects are ordered by statement position and control nesting;
- effects in one arm execute only in that arm;
- expression results crossing an arm boundary use explicit result slots;
- no replay oracle, path enumeration, memory-token chain or general placement pass is required.

There is still a join operation: initializing result slots on each falling-through arm. Structured
control makes that operation straightforward; it does not make value/type agreement disappear.
There is still effect ordering: the ordered statements encode it.

## 3. Semantic values and storage

The evaluator distinguishes:

```
KnownScalar(type, value)
TypeValue(type_meaning)
Word(definition, lexical_bindings, static_arguments)
RecordValue(type_meaning, named_components)
Results(ordered_values)
RuntimeValue(value_id, runtime_type)
RecordPlace(root, field_path, type_meaning, actual_owner_route)
ConcreteStorage(root, field_path, type_meaning)
OwnedCallable(code_identity, environment)
BorrowedCallable(code_identity_or_signature, environment_bindings)
Sum(alternative_names_and_payload_types)
TaggedCallable(visible_signature, arms_of_code_identity_and_environment)
Ref(target_type)                        -- a checked borrow of a place, `target_type *` in C
Named(reserved_recursive_cell)          -- the identity of a recursive definition
```

A sum value is a tag plus one payload. Its alternatives are canonical (sorted by name), so two
spellings of the same alternatives are the same type and one layout. It is immutable and copies by
value, exactly like a record. There is no owning erasure and no open variant: an alternative's
payload type must be fully known, which is why a sum cannot mention itself in this version.

These are ASDL semantic variants behind the evaluator interface. A runtime value is immutable. A
place identifies mutable storage; it is not an unevaluated value read.

Immutable aggregate values may retain known and unknown components. Mutable records do not retain
compile-time field facts across arbitrary runtime calls or branches. In residual evaluation, a
mutable record has explicit storage. Its reads produce snapshots, and its writes produce stores.
This deliberately avoids making syntactic assignment analysis a correctness dependency.

### 3.1 Reading and copying

For:

```
let old = r.state
r.state = 20
return old
```

the first selection emits `Read(old_id, r.state)` immediately. The returned value references old_id,
not r.state. Later stores or calls cannot change what that value denotes.

A record constructor creates a fresh record instance. Ordinary record parameter binding, record
field assignment and record return copy data. A local alias to an existing instance preserves that
instance; selecting/copying a method view preserves its receiver borrow. Copying the record does not
retarget an already selected method.

An immutable aggregate value crossing a storage boundary is materialized once into fresh storage.
A place crossing a by-value boundary is snapshotted before installation in the destination. Scalar
reads happen when their expressions are evaluated; argument and constructor binding cannot move
those reads after subsequent effects.

### 3.2 Branch state

Expression/statement contexts, source result adjustment, and initializer evaluation order follow
syntax sections 5–8. Each arm receives a child lexical environment. Immutable bindings established outside the branch
refer to the same immutable values or storage identities. Arm-local declarations do not escape.
Building a residual arm never mutates the compiler's concrete simulation of runtime storage.

Consequently:

```
if condition then r.draw() end
```

needs no syntactic search for an assignment to r.state. The method call operates on the same explicit
runtime storage as any direct assignment. Reads after the If occur after either arm's effects.

There are no mutable lexical bindings, `mut`, or `:=`. Bare and compound assignments target record
fields, including fields found through the active method receiver.

## 4. Identity and type descriptors

### 4.1 Separate meanings from layouts

Runtime primitives are U32, Bool and Unit. Type is a static-only value category. A record's semantic
meaning includes data requirements, static supplies and executable members. Its C layout contains
only runtime data fields. Equal layouts alone do not establish source type equality.

A schema partially supplied by name binds those fields statically and makes them non-writable.
A saturated constructor's merely known arguments do not change the source mutability of its ordinary
instance fields. Canonicalization must preserve that distinction, even when both have constant initial
contents. Record fields are canonicalized by name before interning. Calling requirements are structural:
independently written equivalent input/result signatures compare equal. Executable identity is not
signature identity: two implementations with the same signature need not have the same behavior.

Multiple-result transport uses an internal ordered product descriptor. It does not add source tuple
types, positional record selection, alignment attributes or packed layout. Those are explicitly
outside `syntax.md`. Canonical records cannot request arbitrary foreign field ordering; foreign
layout interoperability needs its own specification rather than an assertion of portable C11 packing.

### 4.2 Specialization keys

A canonical key contains:

- source definition/template identity;
- checked static argument bindings, indexed by original parameter position;
- static capture bindings, including known executable identities;
- actual lexical owner meaning and occurrence path;
- residual argument, receiver and environment interfaces.

Known scalar values are typed in the key. Immutable aggregate bindings use canonical component order.
Known words have code/specialization descriptors; they are not omitted merely because the runtime
schema has no function-pointer field for them. Recursive code links use finite definition identities,
not recursively expanded environments.

Runtime addresses, current mutable field contents and caller-local IDs never enter a key. Different
receiver instances can share code while passing different receiver bindings. Different lexical
occurrences or static owner specializations must not accidentally share the wrong scope.

Intern within a compilation/session-owned context, not an immortal process-global cache holding all
source programs. Key equality is identity after canonical construction. ASDL `unique` does not sort
lists, enforce immutability or supply these semantic checks automatically.

## 5. Calls, specialization and static demand

### 5.1 Application

Application evaluates the callee and arguments left to right, checks supplied arguments, then tests
remaining requirements. It does not test saturation before appending the new arguments.

Partial application in this target means STATIC supply. Every supplied partial argument must be a
checked static value. A residual argument supplied before saturation rejects; it does not silently
create a new runtime closure representation. An explicit lambda can capture an immutable runtime
value when a residual closure is wanted. Syntax section 3 specifies this rule, including empty calls,
overapplication and exact saturation. Known code with a runtime receiver is not a static partial argument.

A saturated call may mix known and runtime arguments. Known arguments specialize automatically,
including known arguments outside a prefix. Thus f(3, x) and calling f(3) with x use the same runtime
specialization when their other bindings agree. A known executable argument retains its code identity;
its dynamic environment is passed separately rather than unnecessarily erased to an opaque callable.

### 5.2 The complete invocation determines binding time

Classify arguments, receiver and captures—not just explicit parameters. `r.draw()` has an empty
explicit argument list but still operates on a runtime receiver.

A fully static invocation is evaluated under normalization permissions. Static immutable aggregate
construction is allowed. An operation requiring runtime mutation or runtime storage must stop BEFORE
performing it. In mandatory static demand that is a rejection; in an ordinary saturated call the
compiler may abandon the static attempt and build the residual specialization instead. Other source
errors, resource failures or static cycles are not caught as permission for this fallback.

No runtime effect is performed speculatively and rolled back. Known operands do not authorize an
effect during normalization. Calls with runtime bindings immediately request a residual instance.

### 5.3 Independent residual bodies

Reserve the key before elaborating its body. Reconstruct its static arguments as known values and
its remaining arguments as runtime inputs. Build one structured function for that key. A caller
emits a Call; it does not elaborate the callee's branches in its own statement list.

Normalization has no builder at all (`interfaces.md` §4), so an abandoned static attempt cannot
leave partial IR behind: it either yields a static value or raises a private signal before performing
the operation. The residual body is then built from scratch.

There is no outline policy, first-activation exception or source inliner. C may inline the generated
functions, but compiler scalability must not depend on that optimization. A helper called twice in
one caller still has one independently elaborated body.

For an acyclic dependency the compiler may finish the callee depth-first before continuing the
caller. That execution belongs to the callee's own context, not to the caller's IR. Unknown-code
calls instead require a complete runtime signature and emit Indirect.

### 5.4 Static results and runtime effects

A residual call cannot return an unrepresented Type or word proxy in a C value slot. The evaluator
therefore records a source result description: each slot is either an exact static value or a typed
runtime result. Only runtime slots are returned by the private body's ABI. The caller reconstructs
static slots after emitting the call. A constant result is never permission to omit the call or its
possible nontermination.

Infer an exact static result only after all reachable returning arms agree on its value. Different
known scalars of the same type become a runtime result. Different static-only types cannot be joined
into a runtime Type and reject. Dynamic captures prevent a callable value from being classified as
an entirely static word.

Public and opaque-callable entries have runtime signatures. Entry adapters materialize known scalar
or aggregate results and project the source result vector into that ABI. A static-only result that
cannot be represented externally rejects at that boundary. A private helper can still return static
metadata for use during elaboration without exposing metadata in the emitted IR.

## 6. Evaluation and completion

Evaluation carries purpose, lexical environment, current instance, statement-list stack, temporary
allocator and expected result contract. It returns a value plus a completion description:

```
Continues(values)
Returns(values)
TailTransfers(target, arguments)
```

An internal summary can represent mixed branch completion. A return is not an ordinary value that
later statements may consume.

### 6.1 Conditionals

For a known condition, evaluate only the selected arm. For an unknown condition:

1. require Bool and materialize its immutable value;
2. elaborate each arm into a separate statement list and child lexical environment;
3. collect each arm's completion and result vector;
4. for an expression conditional, compare the values of arms that continue;
5. preserve a common static result where both continuing arms agree; otherwise allocate typed join
   slots and append assignments in the continuing arms;
6. append If; subsequent statements are reachable only through arms that continue.

For `if condition then return 1 end; return 2`, the true arm returns and the false arm reaches the
continuation. It needs no expression-result temporary. If both arms return, following statements
are unreachable. A missing else in statement position contributes an empty continuing arm.

Join slots are compiler storage, not source mutable bindings. After the If, a Read produces an
immutable result value. The checker proves every reachable continuation initialized each read slot.
No arm-local value definition is referenced directly from outside its scope.

Short-circuit and/or elaborate the right operand only in the appropriate arm, never eagerly.
Both operands and the result are Bool; and binds tighter than or. A known left operand may avoid
evaluating the right operand entirely. There is no operand-valued truthiness.

### 6.2 Recursion

The target requires an explicit runtime result contract for every member of a RESIDUAL recursive
component. This is an intentional simplifying language rule, not a claim that the old implementation
already imposed it. Syntax section 10 specifies the same rule.

Depth-first elaboration tracks active keys and call edges. A back edge identifies the active cycle;
all its members must have declared result signatures before provisional calls can be used. No fake
result is supplied to discover a shape. Missing contracts reject with the involved definitions.
Further SCC validation checks the completed call graph, including represented callable targets.

A fully static recursive evaluation is ordinary interpreter execution under depth/work limits, not
a residual recursive component. Changing known arguments can create distinct residual keys and is
bounded by the key budget. A source recursive definition is not necessarily a same-key runtime loop.

Declared recursive results are runtime results in this target. Recursive static-result inference or
static-result contracts are not implied. An acyclic helper's body may establish a static result as
in section 5.4. Signatures constrain every return, not merely the first branch visited.

### 6.3 Tail self-calls

Syntactic tail position identifies candidates. A saturated keyed self-call (`f { k = v, ... }`) is a
candidate exactly as an ordered call is; a partial keyed supply only returns a specialized word, so
it is not a call and not a tail position. A rewrite additionally requires the same instance
key, matching result/interface projection and safe storage lifetimes. It must not invalidate a
borrowed local receiver or callable environment.

Evaluate every next argument and capture BEFORE assigning any parameter local. Unchanged forwarded
values may omit a copy when proven unchanged. Then assign simultaneously and transfer to the loop
header. Reinitialize source by-value parameter storage for the next iteration. Uncertain lifetime
cases remain ordinary calls. Nonself tail calls are not guaranteed constant-stack by portable C11.

A loop-carried value parameter is read once at the top of the loop body, not at every mention. The
parameter is immutable, so one read per iteration is equivalent; and because reads are never
interned, a read per mention would give each mention a distinct `Ir.Value` and block sharing of
every expression built from it. Aggregate parameter storage stays a place, because a field or
element write must reach the instance the iteration owns.

The compiler performs the safe self-loop rewrite itself. GCC's ability to optimize other tail calls
is an optional benefit, not a semantic or resource guarantee.

## 7. IR vocabulary and invariants

The concrete schemas are `ast.asdl` and `ir.asdl`, both parsed by the vendored ASDL and covered by
`tests/schemas.lua`. `interfaces.md` fixes pass order, module APIs, side tables, builder state and
invariants. This section states the intent behind those schemas.

Names distinguish immutable value IDs (`Ir.Value`) from mutable storage IDs (`Ir.Storage`).
`Ir.Expr` is pure: no Read, call, trap or effect. `Addr(Place)` computes the address of a place
root plus field selections and reads nothing, which is what lets a record field hold a reference; it
is the one addition to the original "no address acquisition" wording, and it stays pure because a
place is a root plus names. `Ir.Place.Deref` is the route through a reference. `Ir.Stmt` is ordered
by list position.
`Ir.Expr` is deliberately not interned by ASDL, since `Ir.Value` IDs are function-local; the builder
interns expressions per function (`interfaces.md` §4).

Key shapes (see `ir.asdl` for the exact fields):

```
Ir.Expr  = Const | Ref | Un | Bin | Get | Make | Owned | Addr(Place) | Convert(Expr, Ty.V)
         | SliceLength(Expr, Ty.V)
Ir.Place = Local | Captured | Project | Deref | Index | SliceIndex(Expr view, Expr index, Ty.V)
`Ty.Slice(V)` is a runtime-length view: a pointer to the element and a `U32` length. `Make(Slice(T),
{data, length})` builds one from a reference and a length, `Literal.Str` is its one literal spelling,
`SliceLength` projects the length (pure, like a record field), and `SliceIndex` names an element place.
The view is an expression operand rather than a place base because a view needs no storage of its own.
It is read-only, so `SliceIndex` is reached by `Read` and never by `Store`.
Ir.Place = Local(Storage) | Captured(Bundle, slot) | Project(Place, Field) | Deref(Place)
         | Index(Place, Expr, Ty.V)
Ir.Arg   = ValueArg | BorrowArg | BundleArg
Ir.Stmt  = Let | Var | Read | Store | BundleDef | View | Call | Indirect
         | If | Loop | Next | Trap | Return
         | ConstructVariant | VariantMatches | VariantPayload
Ir.Param = ValueParam | PlaceParam | BundleParam
Ir.Fn    = (id, role, hidden, Ty.Input* inputs, Ty.V* results, Param* params, Stmt* body)
```

A reference is a type whose representation is a pointer but whose meaning is a checked borrow: the
target must provably outlive every use (section 8.2). Its implementation follows the same order as every other
family here: `Ty.Ref`/`Ty.Named` and the two IR additions first; then the `Ref` builtin, whose terminal
returns a type for a type argument and a reference for a place argument, so no new syntax is needed;
then the reservation of an open cell around a `let` type definition and the `type-cycle` rejection
when a knot closes by value, with a sealed definition canonicalising its own occurrences so one knot
stays one type; then the two lifetime rules, `ref-target` and `ref-escape`; then `cType`/`placeC` for
`T *` and `(*p).field`, which the existing forward declarations and dependency-ordered emission
already accept. The `c-order` check stays as the layout backstop for a cycle that slips past the
type-level rejection. It is the only indirection boundary that makes
a recursive layout finite, and `Named` is the identity a recursive definition reserves for itself
while its own layout is still being computed. A `Ref` field makes its holder non-retaining in one
direction and tied to its target lifetime in the other, and a by-value cycle stays rejected.

A tagged callable is the callable counterpart of a sum: a closed set of code identities that share
one visible signature, where the tag selects which code a call of the value runs and the payload is
that code's environment. It owns its environments, so it may be returned or stored, and a call
becomes a tag test per arm followed by that arm's ordinary direct call. Because a sum and a tagged
callable are both a tag plus one of several payloads, they share the three IR statements, the C
layout and the lowering; only the type family and how the arms are called differ.

A sum is the one aggregate family whose alternatives are selected by a tag rather than by a static
field name, so it has three statements of its own. `ConstructVariant(value, Ty.Sum, tag, Expr?)`
builds one alternative; the payload expression is absent for a `Unit` alternative.
`VariantMatches(value, variant, Ty.Sum, tag)` tests the tag and defines a `Bool`.
`VariantPayload(value, variant, Ty.Sum, tag)` projects the payload of an alternative that the
matching arm has already established, defining a value of that alternative's type. All three name
their `Ty.Sum`, so the checker can reject a tag or a projection that does not belong to the type,
and a match on a value that is not of that type. Nothing in the IR reads a tag without a matching
test in an enclosing arm, which is what keeps payload projection sound.

There is no separate receiver operand: a receiver is a `PlaceParam`, so `Place.Local` names it. This
replaces the earlier `Receiver(parameter_id)` sketch, which duplicated `Place.Local`.

`Ir.Fn.inputs` is the actual ABI, including the hidden owner/capture prefix; `Ty.Owned`/`Ty.View`
carry the source-visible signature. The two are related by `hidden` and the projection table, and
must not be conflated (`interfaces.md` §6.6).

Var is compiler storage. Source records are initialized before exposure. An uninitialized Var is
allowed only for a join result slot whose initialization is proven before every Read. Loop-carried
storage is declared by `Var` before its `Loop`, so `Ir.Loop` needs no parameter list. Let and Read
create immutable values; their IDs are never assigned.

A structured IR still has a join obligation: the arm that assigns a result slot. Falling through and
definite initialization are defined recursively in `interfaces.md` §6.2–6.3 rather than left implied:
`Return`, `Trap` and `Next` do not fall through, `Loop` does not fall through, and an `If` falls
through when either arm does.

Fold typed constant operations and Get(Make(...)). Known zero division rejects. Dynamic division
emits a Trap on the zero predicate, then materializes the checked quotient/remainder into an immutable
value at that point. It is not left as a freely movable division expression whose guard could be lost.
The same rule applies to any future potentially trapping operation.

`Builder:intern` unifies structurally equal expressions, so the IR is a DAG and one `Ir.Expr` node can
be referenced many times. The emitter names a node used more than once in one local. The
declaration goes in the innermost statement list that contains all of its uses, immediately before
the earliest statement in that list that uses it; in a structured IR nesting is dominance, so this
covers arms and loops with no separate dominance check. An operand shared by the node is declared
first, and a `Const` or `Ref` is never named, because duplicating a leaf is free. This is why an
`Ir.Expr` must stay pure: a trap or a read is a statement materialised at its point, so no guarded
operation is ever hoisted out of the arm that guards it.

## 8. Callables, captures and owners

Owning syntax removes host capture freezing and prototype cloning. It does not remove closure
conversion: nested words must still record lexical free-variable bindings and acquire an environment
when those bindings survive to runtime. AST lexical resolution supplies stable capture slots.

### 8.1 Owned executable values

A concrete owned callable has a code identity, user signature and inline by-value environment type.
Scalar snapshots, immutable aggregate values and other owned callable values may be captured by value.
Returning or copying that callable copies its environment. Its code is known statically; an ordinary
call can be direct.

An implicit receiver field read captures a value only if that read actually occurs before closure
creation. Capturing a receiver/record instance or a method view retains its place and is borrowed.
Lexical resolution and capture planning must distinguish these cases rather than guessing from a
shared signature.

Recursive code links are metadata, not self-pointers inside owned environments. By-value environment
layouts must be finite. A signature is not a substitute for code identity in the owned representation.

### 8.2 Non-retaining views

Unknown runtime code uses a signature-specific invocation pointer and a borrowed environment pointer.
The pointer refers to caller-owned stable storage, not a callee-local environment returned by value.
Converting an owned callable to this interface creates a local adapter with a COPY of its environment.
Selecting a method creates a view borrowing the actual receiver. No hidden allocation is introduced.

Borrowed callbacks may capture places or other borrowed callbacks in compiler-only non-retaining
bundles. This retains the intended useful borrowing capability without adding general source &T
parameters. Such bundles are not ordinary source records, cannot be stored in them and cannot return.

Every source record construction, retaining store and return checks transitive capture provenance.
Opaque callable symbols are conservatively borrowed. Local checks suffice for simple syntax nodes
only when they consult that provenance; merely banning a direct Place child is not enough.

The call ABI is non-retaining: an implementation cannot save a borrowed argument or a pointer into
its environment for later use. General owning signature-erased closures would require an additional
storage/ownership policy and are not claimed by a `const void *` field.

### 8.3 Receiver scope

Receiver borrowing is implicit in methods and is the only source borrowed-parameter position.
Internal typed borrow operands also carry captured receiver roots. The backend treats these as
ordinary typed address operands; the frontend alone decides which source selection supplies them.

Lookup uses the definition's lexical bindings and explicitly bound actual owner chain. No dynamic
caller supplies missing owners. Nested occurrence paths are retained while attached to their actual
root and detached at by-value boundaries. Definitions have no mutable parent field or hidden pointer
back to an enclosing record.

## 9. Verification

Frontend errors are source rejections. The verifier reports bugs if malformed IR survives construction.
It checks:

1. operation types, literal ranges, selectors and result arities;
2. call operands against the TARGET interface, including hidden receiver/environment bindings;
3. immutable value definitions, scope and availability at every use;
4. distinct storage identities and valid, typed receiver/capture roots;
5. definite initialization of join storage on every continuing path before Read;
6. return vector agreement and explicit completion of every reachable function path;
7. Next only under its owning Loop, with safe simultaneous parameter updates;
8. no use of a branch-local value outside its scope and no code after unconditional termination;
9. no escaping borrowed provenance through records, results or callable environments;
10. Owned and View construction against their respective code/environment contracts;
11. guards for partial operations on every path reaching their evaluation;
12. absence of Type values, source words and unresolved signatures from runtime operands;
13. completed reachable function bodies and finite by-value layouts.

A Call result ID is a definition even though no Let introduces it. Nested-list analysis tracks both
scope and completion: syntactically earlier declarations in a returning arm do not initialize the
continuation. Loop checking separately handles parameter storage and per-iteration value definitions.

Readonly pointer qualification is optional. Absence of a local Store is insufficient: calls can write
through forwarded or aliased receivers. Either compute transitive write summaries, conservatively
including unknown callable environments, or emit mutable pointers. Unsound const is not acceptable.

## 10. C closure and emission

Close types, interfaces, adapter layouts and names before printing. Header and source are views of
one closed artifact, not two independent source evaluations. Private prototypes remain in source.
Public reachability includes callable signatures and owned-result environment layouts and invocation
helpers. No historical helper names or facade signatures are compatibility requirements.

A residual instance that no call, view or adapter names is dead and is not emitted at all, and a
private function has internal linkage; only exports and the module initialiser stay external. The
private definition is spelled `WORDLET_PRIVATE`, which is `static inline __attribute__((always_inline))`
on GCC and clang and plain `static` on another C11 compiler. Forced inlining is the default because a
residual specialization usually has one caller, and it removes the out-of-line copies a cost model
keeps for the larger bodies; a host that defines `WORDLET_NO_FORCED_INLINE`, or a caller that passes
`inline = false`, gets plain `static` and the compiler's own decision instead.

The same artifact is consumable without C glue: `artifact:cdef(namespace)` renders the type
declarations and the exported prototypes for `ffi.cdef`, and a `symbolPrefix` namespaces every export
so several artifacts can be loaded in one process. `wordlet.jit` builds the shared object with the
host C compiler — in memory on Linux, through memfd — loads it with LuaJIT FFI, and returns the
exports as Lua-callable functions. It is the runtime face of this backend, not the separate LuaJIT
backend.

| Entity | C representation |
| --- | --- |
| U32 / U16 / U8 | uint32_t / uint16_t / uint8_t |
| Bool | bool |
| Unit | erased payload, while logical result positions remain tracked |
| record value | struct, by value, fields in canonical name order |
| sum value | struct with a tag plus a union of alternative payloads, by value |
| reference | `T *`, with a forward declaration for a recursive target and no allocation |
| array | a struct holding one C array, so it copies and returns by value |
| tagged callable | the same tag plus union shape, holding each arm environment |
| multiple runtime results | internal ordered result struct |
| actual receiver borrow | typed pointer, optionally proven const |
| concrete owned callable | inline environment struct; static code identity |
| capture-free callable (pure code) | invocation pointer with a null environment, exactly a view |
| non-retaining callable view | invocation pointer plus const void *environment |
| captured borrowed bindings | compiler-private local bundle with typed pointers and saved values |

Empty/all-Unit aggregates need one private padding byte in C11. Unit erasure must not accidentally
change source arity. A sum's tag is the alternative's canonical index; its union holds one member per
alternative, and a `Unit` alternative contributes no payload member. Construction is a compound
literal with the tag and the one live payload member set by name, projection reads that member, and a
tag test compares the tag word. Because the payload union is only ever read in an arm guarded by the
matching tag test, an inactive payload is never interpreted.

An integer conversion is an expression, and the cast is the whole of it: widening to a wider type is
lossless, and narrowing to a narrower one masks to that width after the value has been checked. A
narrowing of a run-time value is checked by a `Trap` in the same style as a run-time divisor or index,
so a value that does not fit aborts rather than being silently truncated. Arithmetic is computed in a
wide enough intermediate and cast to the result's own type, which is what makes a narrower width wrap
at its own width rather than at 32 bits.

A shift whose amount is a compile-time constant below the type's width prints as a plain shift, with
no run-time range guard, because that guard can never fire. An unknown amount keeps the guard, since
C leaves a shift by a value at least the width undefined.

An array is a struct holding one C array of its element type, because a bare C array cannot be
assigned or returned by value while a struct that contains one can. The element is embedded, so its
layout must be complete before the array's. `Make` builds it with the elements in canonical order and
`Ir.Place.Index` selects an element; the index travels as an expression, so a known index is a
constant and a run-time index is the value the guard checks. A run-time index is preceded by a bounds
`Trap`, in the same style as a run-time divisor: the builder emits it and the verifier does not
re-derive it.

A `Unit` parameter is erased rather than represented, exactly like a `Unit` result: it produces no
`Ty.Input`, no `Ir.Param` and no C parameter, and a call site emits no argument for it. Erasure
happens when the input plan is built, so the IR argument list, `Ty.Input*`, `Ir.Param*` and the C
signature stay positionally consistent. A view adapter casts its environment to its exact private layout, then invokes
the concrete entry with saved bindings and current arguments. Const access to the adapter does not
make its borrowed referents immutable.

Emit statements in order. Introduce C temporaries at established statement points, not at a global
expression's first textual occurrence. Read snapshots must precede later stores and potentially
mutating calls. Function argument evaluation order must be established before the C call expression.

Aggregate declarations are emitted in dependency order, with a struct tag per generated type so a
pointer to one needs only a declaration. One refinement makes a common recursive shape expressible: a
function-pointer declaration may mention an *incomplete parameter* type, so a view is not a
completeness need for its parameters, and a record may therefore hold a view that takes that record.
A result type must be complete, so a view that returns the record it sits in remains a by-value cycle
and is reported rather than emitted. A reference is exactly such a pointer, which is why a
recursive definition is finite and a by-value cycle is reported instead of emitted. A record may hold a callable view whose parameter list
mentions a record, so the by-value dependency runs in both directions and no fixed order is correct;
a genuine by-value cycle is reported instead of emitted.

A `use`d module is a file resolved next to the importing one, and each module keeps its own top-level
scope, so a name that is not exported stays private. A module's importable surface is exactly its
export list, reached through a namespace value whose members are ordinary words and types, so no new
call or supply rule is needed. The loader resolves imports before loading the module that uses them,
loads each file once, rejects a cycle, and compiles the entry module with its own scope. Every module
shares one translation unit and one initialiser, so the host still makes one call. A name is resolved
in the module that defines it: a definition records its lexical scope, and a lambda created later uses
the root of the scope chain it was written in rather than a global one.

Names use wordlet_<escaped export> and private wordletfn_<number>. Escape non-ASCII-alphanumeric bytes,
including underscore, as _XX. Numbering follows deterministic traversal, not hash-table order.
Public type aliases hide private numbered layout names. Headers have include guards and C++ linkage
wrappers. Packing and arbitrary foreign layout are not promised by the portable C11 backend.

The C compiler may perform further optimization. The Wordlet compiler still owns correctness of storage
reads, guards, argument order and the self-tail transformations it promises.

### 10.1 Arithmetic failures

The syntax excludes configurable traps. The target therefore has one defined arithmetic rule:
known zero division/remainder rejects during evaluation; a dynamic zero divisor aborts at runtime.
No `traps` section, handler function or unchecked precondition is part of this architecture.

IR Trap records the reason and failure predicate. The emitter uses the specified runtime failure
behavior and includes the necessary C declarations. Adding library-configurable failure handling is
a separate language/module-interface decision, not something the backend invents.

## 11. Limits and diagnostics

The owned interpreter can count its own work without host debug hooks. Bound static call depth,
static evaluator steps, expanded aggregate size/depth, residual statements per key, and keys per
program. A static loop or expression recursion consumes evaluator steps even when it emits no IR.
There is no replay path budget. This does not imply unlimited AST nesting or constant compilation
cost: nested syntax, specialization growth and generated statements still consume resources.

Every diagnostic has a source span. User mistakes are reject; exhausted structural budgets are
resource; intentionally unavailable facilities are registered todo; malformed compiler state is bug.
Unexpected implementation exceptions are internal failures, not user type errors. The new CLI statuses are reject=1, bug=2, todo=3, resource=4, internal=2, as specified in
VALIDATION.md. They are not constrained by a previous compiler's statuses.

TODO witnesses test intentionally absent mechanisms, not placeholders that emit wrong code. New tests
are written against this architecture's rules. Old tests are useful examples to inspect, but keeping
the old suite green, retaining its IR shapes or reproducing incidental rejection behavior is not an
acceptance condition.

## 12. Modules and ASDL discipline

```
wordlet/init.lua   facade: load, compile, diagnostics and public API
wordlet/lex.lua    free-form tokens and spans
wordlet/parse.lua  expressions, declarations, blocks and module export syntax
wordlet/ast.lua    loading/building ast.asdl nodes; AST helpers
wordlet/resolve.lua lexical scopes, bindings, capture classification and tail positions
wordlet/schema.lua ASDL semantic types, values, identities and interface descriptors
wordlet/builtins.lua bootstrap definitions for U32, Bool, Unit and Type
wordlet/value.lua  knownness, immutable components and storage distinctions
wordlet/env.lua    lexical bindings and explicit actual-owner bindings
wordlet/key.lua    canonical partitions, instance registry and active dependency graph
wordlet/eval.lua   source evaluation, calls, conditionals, completion and capture planning
wordlet/ir.lua     loading/building ir.asdl nodes, per-function interning, semantic visitors
wordlet/check.lua  types, completion, scopes, initialization and borrow invariants
wordlet/cabi.lua   representation closure, entry/adaptor layouts and names
wordlet/lower.lua  ordered emission, local temporaries, header/source assembly
wordlet/diag.lua   source diagnostics and resource reporting
wordlet/cli.lua    command-line entry point (optional CLI module for the bundler)
```

The namespace is `wordlet`; `require("wordlet")` resolves through `wordlet/init.lua`. The bootstrap
toolkit uses the separate `wordletkit` namespace, so compiler module names never collide with it.

`resolve.lua` and `builtins.lua` were absent from the earlier file list. Without a resolution pass
standing between parsing and evaluation, capture classification and receiver-field binding had no
home; without bootstrap primitives, `U32`/`Bool`/`Unit`/`Type` had no definitions before evaluation.
Per-module contracts, including each module's exported functions, are in `interfaces.md` §2.

Dependencies flow from orchestration through the evaluator to semantic data, and separately from
IR through checking and lowering. No backend module imports eval or resolves source expressions.
Registry state is not smuggled onto immutable ASDL nodes.

ASDL sum methods are installed only in their defining schema module, parents before children.
The actual ASDL implementation copies parent methods into variants and does not freeze interned
objects/lists. Constructors copy/canonicalize inputs; clients must not mutate interned data.
Product nodes need explicit classification where dispatch requires it; not every ASDL class has a
variant kind automatically.

Reflection can enumerate structural fields. Semantic visitors for value uses, definitions, places,
completion and referenced targets are explicit and exhaustive. Contextual state—use counts, emitted
names, initialization facts and provenance—lives in pass-owned side tables scoped by function.

Owning syntax removes host environment inspection, Lua proxy metamethods, replay, capture freezing
and debug-stack reconciliation. It does NOT remove lexical capture planning, result contracts,
borrow checking, effect order or ABI layout. Those are properties of the language and its runtime.

## 13. Resolved frontend contracts

The source rules are defined in syntax.md, not inferred from implementation conveniences:

1. Lambdas always use pipes, including `|x| -> ...` and `|| -> ...`, and `->` introduces only a
   lambda body. A result is written `:` after the parameter list (`let f(x: U32): U32`), and a
   signature parenthesizes its inputs (`(U32): U32`). `:` after a name stays an annotation, so a
   signature inside a lambda's parameter list is unambiguous: `|f: (U32): U32| -> f`. Missing
   lambda parameter types require an expected signature; explicit annotations are checked.
2. Named parameters may share an annotation; ordinary result-binding names have individual optional
   annotations. Requirements are checked left-to-right, including dependencies on earlier Type inputs.
3. Partial application accepts static supplies only. Saturated calls may have runtime arguments.
   Empty calls preserve an incomplete word, invoke a nullary terminal, and never invent missing code.
   Overapplication rejects rather than automatically applying a returned word.
4. Expression bodies forward result vectors. Explicit-return blocks have no implicit final value.
   Expression conditionals require else; statement conditionals have end and may omit else.
5. Multiple-result annotations use `(T1, T2)`; binding uses `let a, b = ...`. These are result lists,
   not general tuple values/patterns. Scalar contexts and explicit grouping select the first result.
   Final expressions expand in argument/return/binding lists; bindings alone fill missing slots with
   Unit. Preserve source slots separately from runtime Unit erasure.
6. Saturated call statements discard their result vector. An unused partial word is not a call for
   effects. Arbitrary arithmetic is not an expression statement.
7. and/or/not operate on Bool, short-circuit where appropriate, and preserve the specified precedence.
   There is no Lua truthiness, proxy comparison protocol or implicit Bool/U32 conversion.
8. Keyed schemas and named initializers have different grammatical roles. Keyed partial supply is
   static; complete construction creates an instance. Module export configuration is a third,
   deliberately separate grammar, not a general runtime table language.
9. Field assignment evaluates its target once then its RHS. A compound store reads the old field
   before evaluating the RHS, then computes/stores. Only the arithmetic/bitwise compounds enumerated
   in syntax section 7 exist; assigning to an immutable local rejects even if it shadows a field.
10. Top-level names are registered together, initializers are demanded once in source order with
    dependency-driven early demands, and eager value cycles reject. Local declarations are sequential;
    only a named local word sees its own binding in its body. No implicit runtime module globals exist.
11. Residual recursive components need complete result contracts. Callable shape annotations do not
    magically determine an owned recursive environment layout; unresolved representations reject.
12. Export configuration has functions/types/results only. Public aliases and duplicate checks are
    explicit. There are no pub/import/traps declarations or implicit foreign layout facilities.

The lexer/parser must turn these into executable grammar tests, including postfix continuation across
whitespace, arrow/type-list grouping, nested conditional forms and the module-only configuration
notation. The checked ASDL compiler schemas and parser are implementation work, not supplied by the
bootstrap toolkit.

## 14. New validation obligations

- Parse free-form one-line and multiline versions identically; test precedence and arrow ambiguity.
- Elaborate N sequential unknown conditionals without enumerating 2^N continuations.
- Compile a branching helper called twice into one independently elaborated specialization.
- Preserve a scalar/record snapshot across direct stores and receiver-mutating calls.
- Put a receiver call inside one conditional arm and observe exactly the selected effects.
- Check early-return arms, nested expression conditionals and definite initialization of join slots.
- Share equivalent explicit/automatic static bindings; distinguish known implementations and captures.
- Reject an unannotated residual recursive component; compile annotated mutual and self recursion.
- Preserve swapped tail arguments; refuse tail replacement when a local receiver/environment remains live.
- Return and copy an owned closure after its creator returns; reject escaping borrowed views/bundles.
- Lower a repeated expression used in disjoint scopes without invalid temporaries or unsafe hoisting.
- Compile/run C with strict warnings, arithmetic edge cases, dynamic divisor guards and ordered effects.
- Emit a header/source pair and consume it from a separate C translation unit.
- Diagnose infinite static computation by interpreter work limits, independently of emitted IR count.

Compare interpreter results and ordered effects with generated C. Schema construction and IR checks
are separate test layers; passing a parser or interning test is not proof of compiler semantics.
