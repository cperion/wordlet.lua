# Working on this standalone Wordlet project

Read README.md, syntax.md, architecture.md, interfaces.md, ast.asdl, ir.asdl, ASDL.md, u32.md and
VALIDATION.md before implementing
compiler components. These files are local authorities, not links to an old checkout. THIRD_PARTY.md
records verified Terra origins and local changes. The project and vendored code use MIT; preserve
LICENSE and vendor/LICENSE, including in generated bundles.

## Status and tests

The compiler is implemented and works end to end for the subset listed in README.md's status
table: lexer, parser and AST (`ast.asdl`), semantic types and structured IR (`ir.asdl`), a
static/normalization/residual evaluator, verification, and a C11 backend. Implemented and covered
by tests: records, schemas, methods and field stores; the integer types (`u8`..`i64`) and `f64`
as IEEE-754 double with float literals; arrays, slices and strings; references and recursive
types; `ptr` and `null`; sum types; closures, borrowed captures and tagged callables; `defer`;
foreign declarations (`extern`); imports; and self-tail calls. Some shapes are deliberately
rejected rather than miscompiled: nested borrowed closures, erasing a runtime-tagged callable
into a signature, and the `ref-target`/`ref-escape` rules raise diagnostics.

`wordletkit.lua` is NOT the compiler. The `.let` examples under `examples/` compile and run today;
the expected values in VALIDATION.md are the reference-interpreter oracle. Do not claim that
toolkit/schema checks validate a parser, evaluator or C backend.

Run `timeout --kill-after=2s 180s luajit tests/run.lua` for everything (it bundles, generates C and
runs the C under strict warnings). `tests/eval.lua` and `tests/c.lua` can also be run alone. Report actual results and
wall time. Add new compiler tests against the documented semantics as compiler phases are built;
there is no old-suite compatibility requirement. Never emit a fake success, stub or provisional
value for an unimplemented phase.

## Architecture boundaries

- Wordlet owns its syntax: no Lua proxy/metamethod frontend, replay oracle or debug-stack reconciliation.
- Use ASDL from the beginning for AST, semantic descriptors and structured IR. Canonicalize/copy lists;
  interned does not mean immutable. Keep effects/storage reads as occurrences.
- Traverse AST and IR through `wordlet/walk.lua`, which reads the generated `__fields`, not a
  hand-written child table; a new variant must not be silently skipped. Semantic visitors stay explicit.
- Separate immutable values from mutable places. Snapshot reads immediately; preserve call/store order.
- Compile each residual specialization independently. Known code identity is not a borrowed receiver
  address, nor proof that an invocation is static or effect-free.
- Check real lexical owners, result contracts and transitive borrowed captures. Do not invent heap
  ownership for a signature-erased environment pointer.
- Checking/ABI/emission consume compiler data, not source expressions to evaluate again.
- Source choices are in syntax.md. If a rule changes, update the architecture and tests with it.

## Standalone distribution

All project dependencies must live here or be documented external host tools/modules. Never reach into
an enclosing checkout. Keep bundled modules explicit in bundle-manifest.lua; use its host allowlist for
built-ins such as bit. The isolation test copies this project to a temporary directory and clears Lua
search paths. If you add required project files, update its copy manifest too. The `editor/` tree
is editor support, not a compiler dependency, so it is deliberately absent from that manifest.

Keep compiler code separate from the vendored libraries. Record any vendor edits and provenance in
THIRD_PARTY.md. Preserve upstream attribution. Do not install process-global ASDL caches retaining
source programs forever.
