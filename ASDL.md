# Vendored ASDL and List contract

Load from the project root:

```lua
local A = require("vendor.asdl")
local L = A.List
local c = A.NewContext()
c:Define([[
module T {
  Type = U32 | Bool
  Field = (string name, Type type) unique
  Expr = Literal(number value) | Add(Expr left, Expr right)
}
]])
local x = c.T.Literal(3)
local sum = c.T.Add(x, c.T.Literal(4))
assert(c.T.Expr:isclassof(sum))
assert(sum.kind == "Add")
assert(c.T.Field("x", c.T.U32) == c.T.Field("x", c.T.U32))
```

## Schema syntax

`module Name { ... }` namespaces definitions. A product is `Name = (type field, ...)`.
A sum is `Name = Constructor(...) | Other(...)`. `unique` follows a product/constructor to request
interning. Bare constructors such as U32 above are singleton VALUES; use `c.T.U32`, not `c.T.U32()`.
`attributes (...)` after a sum appends those fields to each variant.

Fields may be optional (`Type? field`) or lists (`Type* fields`). Lists require `A.List` objects,
not plain Lua arrays. Qualified field types use dots. Types are declared before their fields resolve,
so mutually referential schemas parse; that does not authorize cyclic runtime layouts.

Built-in field checks include number, string, boolean, table, function, userdata, cdata, thread,
nil and any. They check Lua categories, not semantic ranges. IDs need integral/range checks; U32
literals need 0..4294967295 checks. `c:Extern(name, predicate)` installs a custom field check before
Define. Do not use any to bypass important compiler invariants.

Field names must not be Lua keywords. `end`, `function`, `local`, `repeat`, `not` and friends are
valid identifiers in ASDL but produce `node.function`, which is not valid Lua source. Prefer
`callee` over `function`, `condition` over `if`, and so on.

Schema comments start with `#` and end at a newline. Keep a final newline, including after a final
comment. Constructor/product names share a namespace: two sums cannot both define Unknown in the
same module. Namespacing must be designed, not inferred from an enclosing union.

## Interning is not immutability

Interning compares ordered constructor fields. Unique lists are interned by SEQUENCE; keyed schemas
must sort fields before construction. Canonical list storage may be shared between nodes. ASDL does
not prevent mutation of nodes or lists. Copy external lists and prohibit mutation after construction.
There is no weak-cache lifetime guarantee: contexts have strong caches. Scope contexts to sessions
or compilations so old source programs can be collected. Do not put source-bearing contexts in an
immortal module global.

Intern immutable type/key/expression descriptions. Do not intern call/store/read/allocation occurrences.
Function-local IDs require function-scoped analysis tables, even if an interned ID wrapper is shared.
A pointer-equal expression description does not establish a legal evaluation point or dominance.

## Methods, reflection and dispatch

Sum variants have `.kind`; products do not automatically have it. The class's `__fields` list describes
field names, types, optionality and listness. Reflection enumerates structure, not control completion,
SSA definitions, effects or borrowing. Implement exhaustive semantic visitors for those tasks.

Class behavior is copied rather than inherited through a normal lookup chain. Installing a NEW parent
method after a child override overwrites that override. Install parent methods first, child methods
second, in the schema-owning module only. Do not spread class mutation across analysis modules.

Methods on interned objects must be intrinsic. Put use counts, source provenance, names, initialization
facts and all contextual analysis in pass-owned side tables. The library permits an init method;
it must not attach per-use state to interned nodes.

## List

`L{...}` wraps the provided table; it does NOT copy it. Standard table helpers and map/filter/fold,
indexed variants, concatenation, partition and related helpers are provided. Higher-order methods
accept functions or selector/operator strings. Prefer explicit functions in compiler-critical logic.
The local equality selector correction is recorded in THIRD_PARTY.md and checked by tests/run.lua.

## Working check versus future compiler

`luajit tests/run.lua` exercises the actual vendor constructor/interner/method behavior and its bundled
form after relocation. It does not validate the proposed Wordlet AST or IR, which have not been implemented.
Before implementing either, write a concrete schema and constructor/visitor coverage tests against
this library. The architecture's schematic vocabulary is not itself valid ASDL source.
