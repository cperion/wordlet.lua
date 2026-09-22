# Wordlet — standalone compiler project seed

This directory can be copied to an empty repository. No file above this directory is required.
The implementation host is **LuaJIT 2.1**, not the speculative LuaJIT 3.0 syntax referenced in earlier
language discussions. Wordlet source (`.let` files) is parsed by its own future frontend. The target
backend is C11.

## What exists

The compiler is being built in vertical slices; `syntax.md` and `architecture.md` are the target, and
this section states exactly how much of it runs today.

| Area | Status |
| --- | --- |
| Lexer, parser, AST (`ast.asdl`) | implemented; `tests/parse.lua` |
| Semantic types, structured IR (`ir.asdl`) | implemented |
| Evaluator: static, normalization and residual execution | implemented for the subset below |
| Verification (`check.lua`) | implemented: types, scope, definite initialisation, fall-through |
| C ABI closure and C11 emission | implemented for scalars, Bool, Unit and multiple results |
| Single-file bundle and CLI | implemented; `dist/wordlet.lua` |
| Records, schemas, methods and field stores | implemented, including compound stores and by-value copy |
| Integers (`U8`, `U16`, `U32`, `I32`, `U64`, `I64`) | implemented: a literal that does not fit a word is 64-bit, arithmetic wraps at the width its type names, a literal adapts to another operand's type when it fits, mixed widths of one signedness widen, mixing signed and unsigned rejects, changing signedness reinterprets, and a width-changing conversion rejects a known value that does not fit and aborts a run-time one that does not. `I32` is two's complement with truncating division and an arithmetic shift |
| Arrays (`Array(T, N)`, `[e, ...]`, `a[i]`) | implemented: the length is part of the type, so a known index is checked while compiling and a run-time index is guarded. A struct holding a C array, so an array copies by value on pass, return and field store, while a local binding aliases |
| References (`Ref(T)`) and recursive types | implemented: a reference names a place and lowers to `T *`. Legal targets are module storage (untied) and a place belonging to an enclosing activation (tied, so `ref-escape` rejects an escape); a local, a copy or a temporary rejects (`ref-target`). A recursive definition reserves its own identity while its layout is computed, so a knot compares by identity, a by-value cycle rejects (`type-cycle`), and a cycle through a reference is finite |
| Sum types (variants) | implemented: `OneOf(schema)` builds one, `T.case {...}` constructs, `value { case = handler }` matches. A known tag selects its handler statically; an opaque tag becomes a C tag test with the payload projected inside the arm. C layout is a tag plus a union, and a `Unit` alternative carries no payload |
| Closures and higher-order words | implemented: by-value environments, direct calls, and capture-free lambdas as pure code — an invocation pointer with a null environment, which may cross a boundary but needs no adapter |
| Passing a method to a callable parameter | implemented: the parameter takes a view whose local adapter holds the borrowed receiver |
| Borrowed captures (a captured receiver or method) | implemented as a non-retaining place input. Such a closure cannot escape, be stored or be captured again (`borrow-escape`), but it may be passed to a callable parameter, where a local adapter holds the borrowed place |
| Nested borrowed closures (a closure capturing another borrowed closure) | **rejected** (`borrow-escape`); needs a callable environment |
| Opaque runtime callables (`Ty.View`) | implemented: an invocation pointer plus an environment. An exported function with a callable parameter takes a view, and a view call goes through `Ir.Indirect` |
| A callable stored in a signature-typed field | implemented through the borrowed callable ABI: the field holds `{ invoke, environment }` built from a local adapter, so the record is non-retaining and cannot escape (`borrow-escape`) |
| Partial application of a closure | implemented: `add(5)` yields a closure with a static argument bound |
| Contextual lambda parameter types | implemented: a binding annotation, a parameter requirement or a result contract supplies them. A lambda with no expectation anywhere is still rejected (`lambda-annotation`) |
| `F64` | **specified in `syntax.md` §1, not implemented**: an IEEE-754 double, so division by zero is an infinity or a NaN rather than a trap, a NaN comparison is false, and the integer conversions round one way and truncate the other. It also needs a float literal, which this syntax does not have yet |
| Imports (`use util.helper`) | implemented: the dotted name is a file next to the importing one, the last segment is a namespace over that file's export list, a name that is not exported stays private, each file loads once, a cycle rejects, and all modules share one translation unit and one initialiser |
| Two different callables selected by one conditional | implemented as a tagged callable: a tag plus a union of the arm environments. A call tests the tag and runs that arm's own code directly, so it needs no function pointer. The same code identity in both arms needs no tag |
| Erasing a runtime-tagged callable into a signature (`callable-erase`) | **rejected**: a view does not retain the environment that carries the tag. Call it where it was selected, or select the arm first |
| Self-tail calls (`Loop`/`Next` back edges) | implemented; tails run at constant C stack depth |
| Module-level mutable records captured by runtime code | implemented as named file-scope storage plus an exported `wordlet_init()`. The host owns initialisation order; nothing is called implicitly |

Working end to end today: U32/Bool/Unit, `let` bindings, named definitions with parameter and result
annotations, arithmetic/comparison/bitwise/logical operators, expression and statement conditionals,
multiple results and result-list binding, static partial application, automatic static
specialisation, calls compiled to independently elaborated bodies, recursion with an explicit result
annotation, records with methods, borrowed receivers, field reads and compound stores, sum types with
exhaustive matching, callables that borrow or are selected at run time, and references with recursive
types.

A `Unit` parameter is erased rather than represented: it produces no ABI slot, exactly like a `Unit`
result, so a handler for a `Unit` alternative takes no C argument.

A result is written with `:` after the parameter list; `->` introduces a lambda body and nothing
else; a signature's inputs are parenthesized, so `(U32): U32` is a word from U32 to U32.
A call to the instance currently being built, in tail position, becomes a back edge: a `for (;;)`
loop with a `continue`, with every next argument evaluated before any parameter is rebound. Calling
it with different static arguments is a different instance and stays an ordinary call.

A lambda becomes a closure: captures that are static join its code identity, and the remaining ones
form a by-value environment passed to the compiled lambda as leading hidden inputs. Because the code
identity lives in the value's type, calling a closure stays a **direct call** — no function pointer is
needed while the code is known.

An unannotated lambda takes its parameter types from the context it is written in — a binding
annotation (`let inc: (U32): U32 = |x| -> x + 1`), a parameter requirement
(`twice(|y| -> y + 1, x)`) or a result contract (`let adder(n: U32): (U32): U32 = |x| -> x + n`,
where the signature also becomes a checked requirement on what the body returns).

A lambda that captures a mutable instance or a method view keeps a **borrow** rather than a copy, so
it observes later mutation — unlike a captured scalar field, which is a snapshot. The borrow travels
to the compiled lambda as a place input, and because the closure is tied to the activation that made
it, returning, storing or re-capturing it is rejected.

A callable whose code is not known in this compilation — an exported callable parameter or a
callback supplied by C — uses the invocation-pointer ABI: `Ty.View(sig)` lowers to
`{ invoke, environment }`, and calling it emits `Ir.Indirect`. A call to *known* code is still a
direct call, so `internal(x) = apply(|y| -> y + 1, x)` emits no indirection.

A module-level `let` that binds a mutable record and is used from runtime code becomes **named
storage**: the artifact emits one file-scope object per such binding and an exported
`void wordlet_init(void)` that assigns their starting values. The host calls it explicitly before
using any exported function, so initialisation order stays visible rather than implicit.

A field declared as a signature is represented by the **borrowed callable ABI**: assigning known code
emits a local adapter that binds its hidden inputs, and the field stores the resulting
`{ invoke, environment }`. Reading the field and calling it goes through `Ir.Indirect`. Because the
adapter lives in the assigning activation, the record holding it is non-retaining: it may be used,
copied and called locally, but returning it or storing it in module state is rejected.

`tests/eval.lua` (203 checks) and `tests/c.lua` (245 checks, 18 programs) cover this.


- [syntax.md](syntax.md): Wordlet source syntax and semantic decisions.
- [architecture.md](architecture.md): structured evaluator/IR implementation contract.
- [interfaces.md](interfaces.md): pass order, module APIs, side tables, builder state, facade API.
- `ast.asdl`, `ir.asdl`: concrete ASDL schemas, parsed and checked by `tests/schemas.lua`.
- `vendor/asdl.lua`, `vendor/terralist.lua`: working ASDL and list implementation.
- `tools/bundle.lua`: working manifest-driven single-file Lua bundler.
- `wordletkit.lua`: a tooling API exporting ASDL, List and U32, NOT the Wordlet compiler.
- `wordletkit/u32.lua`: checked exact concrete U32 operations; [U32.md](U32.md) explains host/C rules.
- `examples/*.let`: source acceptance fixtures, not programs runnable by the bootstrap.
- `tests/run.lua`: executable bootstrap and relocation checks.
- [ASDL.md](ASDL.md): the actual vendored API, limitations and integration rules.
- [VALIDATION.md](VALIDATION.md): tooling tests and future compiler acceptance obligations.
- [THIRD_PARTY.md](THIRD_PARTY.md): verified Terra origins, local changes and MIT attribution.
- [LICENSE](LICENSE) and [vendor/LICENSE](vendor/LICENSE): project and upstream MIT notices.
- [AGENTS.md](AGENTS.md): local implementation and validation instructions for coding agents.

The `wordlet` namespace is the compiler. `wordletkit` remains the bootstrap toolkit (ASDL, List and
the U32 reference kernel) and is not the compiler.

## Run the working tooling

From this directory, using LuaJIT and POSIX utilities:

```sh
luajit tests/run.lua
luajit tools/bundle.lua
luajit -e 'local k = dofile("dist/wordletkit.lua"); print(k.List{1,2,3})'
```

The default bundle is `dist/wordletkit.lua`. It exports the bootstrap API. It does not compile Wordlet.
Running tests requires `cp`, `mkdir`, `rm`, and GNU-compatible `timeout`. `LUAJIT` may name the LuaJIT
executable. Future C tests additionally need a C11 compiler, preferably selected through `CC`.
The bootstrap has no LuaRocks, network, external Lua library or C compiler dependency. Its bit module
is supplied by LuaJIT itself.

The builder locates its default manifest beside the project, not relative to the invocation cwd:

```sh
cd /tmp
luajit /path/to/project/tools/bundle.lua
```

Copy this entire directory to start the new repository; do not create symlinks back to the old one.
Initialize Git there normally. Generated `dist/` output is ignored. The project uses MIT, like Terra;
retain the project and vendored copyright/license notices when redistributing. The default bundle
embeds them, so single-file distribution keeps the attribution.

## Bundler contract

`bundle-manifest.lua` is a trusted Lua table with these fields:

```lua
return {
    entry = "wordletkit",              -- required module whose value the bundle returns
    output = "dist/wordletkit.lua",    -- default output, relative to manifest
    licenses = {"LICENSE", "vendor/LICENSE"}, -- embedded as comments in the bundle
    modules = {
        wordletkit = "wordletkit.lua", -- every bundled module is explicitly listed
        ["wordletkit.u32"] = "wordletkit/u32.lua",
        ["vendor.asdl"] = "vendor/asdl.lua",
        ["vendor.terralist"] = "vendor/terralist.lua",
    },
    external = {"bit"},                -- built into LuaJIT; used by wordletkit.u32
    -- cli = "wordlet.cli",            -- OPTIONAL; add only once that module exists
}
```

Module source paths must remain inside the manifest directory (no absolute paths or parent traversal).
The build includes all listed modules in sorted name order. It does not scan source with regular
expressions pretending to discover every require. List dynamically required internal modules too.
An unlisted require fails at runtime unless explicitly external; it never accidentally loads code
from the surrounding checkout. This is loader isolation, not a sandbox against arbitrary Lua.

```sh
luajit tools/bundle.lua path/to/manifest.lua path/to/output.lua
```

An explicit output argument is relative to the caller's cwd (or absolute). The default manifest output
is relative to the manifest. Parent directories are created with safely quoted POSIX mkdir. Module
syntax and assembled syntax are checked before output is written. License notices are validated and
embedded as comments. A failed write reports nonzero; output replacement is not promised atomic.
Manifests and module source are trusted build inputs.

Factories receive local `require`, local `package` with a private `loaded` table, and the module name
as `...`. Modules should return their API. Legacy `package.loaded[...] = value` is supported inside
the private table. Failed loads clear private state so a later attempt can retry. Cycles reject unless
a module deliberately installs a usable value before requiring the cycle. False module results follow
Lua require's reload behavior. Global side effects, `module()`, source-relative runtime asset loading,
searcher customization and arbitrary manipulation of the host package table are not isolated APIs.

An optional CLI module must return `function(api, argv) -> exit_status`. The generated bundle invokes
it only when executed as the script; require/loadfile usage otherwise returns the entry API. CLI tests
exercise this using fixtures, not a fictitious compiler. Normal executable dispatch expects the usual
LuaJIT `arg[0]` and chunk filename agreement; custom launchers can call the CLI module explicitly.

When the real compiler exists, change the release manifest's entry to its `wordlet` facade module,
list its modules, add `cli = "wordlet.cli"`, and choose `dist/wordlet.lua`. Do not ship empty compiler
modules simply to make that manifest appear ready.

## Document authority

The syntax document defines source behavior. The architecture defines how compiler data preserves it.
Both are self-contained; numbered sections refer to those local files only. Algorithm changes must
update both where they alter a language rule. Old implementations/tests are not a compatibility gate.
The validation document distinguishes working tooling checks from unimplemented compiler obligations.
