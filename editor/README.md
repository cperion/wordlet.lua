# Wordlet editor support

A plain Vim-syntax grammar for Wordlet, living with the language rather than in a
personal configuration. It is deliberately regex-based for the moment: there is no
language server, and this directory is a normal Vim runtime directory.

```
editor/nvim/
  ftdetect/wordlet.vim    *.let -> filetype wordlet
  ftplugin/wordlet.vim    iskeyword+=_, commentstring=--, suffixesadd=.let
  syntax/wordlet.vim      the grammar
```

## Wiring it up

Without a plugin manager, add the runtime directory before `filetype` processing
runs (for example in `options.lua`, which Neovim loads early):

```lua
vim.opt.runtimepath:append(vim.fn.expand("~/dev/wordlet.lua/editor/nvim"))
```

With lazy.nvim, a local directory is an ordinary plugin spec:

```lua
return {
  {
    dir = vim.fn.expand("~/dev/wordlet.lua/editor/nvim"),
    name = "wordlet-editor",
    lazy = false,
  },
}
```

`plugin/` is intentionally absent: a plugin script is only needed to register the
filetype when the directory joins `'runtimepath'` after startup. The `ftdetect`
file covers the normal case, and `vim.filetype.add` is not required.

## Design

Wordlet is not C with different punctuation, so the mapping is not the usual
keyword/type/function/identifier one. Its core is the *word*: a word with ordered
or keyed requirements, an optional result contract and an optional terminal. A
signature is a word with no implementation; a record schema is a word with keyed
requirements and an intrinsic construction terminal; a method is a word with an
implicitly bound receiver. Types are ordinary words too — `Ref(T)`, `Array(T, N)`,
`OneOf({...})` — and a type expression is an expression. See `syntax.md` and
`ast.asdl`.

Two invariants decide every rule.

1. **Role comes from position, never spelling.** `syntax.md` §1: capitalization
   never distinguishes a type from a value or a signature from a lambda. So the
   grammar never treats `ALLCAPS` or `snake_case` as a type. A name is classified
   by the keyword that introduces it (`let`), by the punctuation it follows
   (`.` `:`), or by the token it precedes (`(`).

2. **Never lie where the resolver is needed.** A regex cannot see a receiver's
   schema. Where a distinction requires the type checker, the grammar uses a
   neutral group and leaves the refinement to a future language server and its
   semantic tokens. It does not guess.

### Role to group

| Wordlet role | Group | Why |
| --- | --- | --- |
| `let` | `Keyword` | declaration introducer |
| `extern` | `StorageClass` | foreign linkage, exactly C's `extern` |
| `do` `end` `return` `defer` | `Statement` | statement and block forms |
| `if` `then` `else` | `Conditional` | control |
| `and` `or` `not` | `Operator` | logical operators |
| `true` `false` | `Boolean` | Bool literals |
| `U8`..`F64` `Bool` `Unit` `Type` | `Type` | predefined type bindings |
| `OneOf` `Ref` `Array` `Slice` `Ptr` `Null` `String` | `Special` | predefined constructor words, kept distinct from the type names a program declares |
| name after `:` | `Type` | annotation, parameter requirement, result or schema-field type |
| word definition and call, method | `Function` | executable words |
| `let` binder | `Identifier` | a bound name |
| name before `:` | `Identifier` | a keyed requirement (parameter or schema field) |
| name after `.` | `Identifier` | member: field, method, alternative or namespace entry |
| `types` `functions` `results` | `Identifier` | module-configuration keys |
| `use <dotted name>` | `Include` | module import, like Vim's `Include` |
| `+` `-` `*` `/` `%` `^` `&` `\|` `<<` `>>` `->` `=` `==` … | `Operator` | `\|` is one token in both its lambda and its bitwise role, so it is one group |
| `(` `)` `{` `}` `[` `]` `,` `;` `:` `.` | `Delimiter` | structure |
| integers, floats, strings, bytes | `Number` `Float` `String` `Character` | |

### Why `Special` for constructors

They are the one place where a language-provided name and a user-declared name
must not look alike. `Type`, `Structure`, `Typedef`, `Constant`, `Keyword` and
`StorageClass` all resolve to the same default colour, so any of them would be
indistinguishable from `Type`; `Special` does not. It is also honest to Wordlet's
model: a constructor is a word the program applies (`OneOf({...})`, `Array(T, N)`,
`Ref(x)`), so sharing the applied-word colour is not a lie.

If you prefer a different default, relink it:

```vim
hi! link wordletConstructor Structure
```

### Groups deliberately not used

Wordlet has no construct for them, and decoration that misinforms is worse than
sparse highlighting:

- `Repeat` — recursion and tail calls, not loops.
- `Exception` — no exceptions; `defer` is a statement, not `finally`.
- `Label` — no `goto` or `case`; the export sections are keys, not labels.
- `Structure`, `Typedef` — no `struct` or `typedef` keyword. Rust maps its own to
  `Keyword`/`Type` for the same reason.
- `PreProc`, `Define`, `Macro` — no preprocessor.
- `Debug`, `Underlined`, `Title`, `Tag` — nothing to attach them to.

### Mechanism

Vim tries a syntax item only where scanning resumes, so a rule cannot begin with
`let`, `:` or `.` once those are already matched. The positional rules therefore
use `nextgroup` on the introducing keyword or delimiter, which is how the built-in
`rust.vim` and `go.vim` do it. Vim keeps the last item that matches at a column, so
the plain delimiters and keywords are declared first and the refining `nextgroup`
rules later. The helper groups reached through `nextgroup` are `contained`, and the
word form is defined after the plain binder it refines because a `nextgroup` list
with two matching groups keeps the later one.

### Blind spots, left to the resolver

- `r.value` (field) vs `r.draw()` (method) vs `Opt.some()` (alternative): one
  member group, because only the receiver's schema decides.
- `Point { ... }` (schema construction) vs `value { ... }` (a match on a sum
  value): the base name is not classified.
- a signature input list `(T): U` cannot be told from a parameter list
  `(x: T) : U` by `)` alone, so only names after `:` are marked `Type`.
- `Ref(x)`, `Ptr(x)` and `Slice(x)` take a type or a place depending on the
  resolver, so their argument is not guessed; nor is a user element type inside
  `Array(T, N)` (the predefined ones are keywords anyway).
- bare parameters that share a later annotation, as `a` and `b` in
  `(a, b, x: U32)`, have no local marker and stay default.
- a word bound to a lambda or a partial application, as
  `let next32 = xorshift(13, 17, 5)`, is a binder at its definition and a
  `Function` at its call site; only the resolver knows the binding denotes code.

### Turning the guesses off

Every positional rule is a heuristic over a free-form grammar. Setting

```vim
let g:wordlet_highlight_heuristics = 0
```

keeps only what cannot be wrong — keywords, operators, literals, comments and
imports — and leaves every other name at the default `Identifier`. The flag is
read when the syntax file loads, so set it before a buffer's filetype is set.

## Tests

The compiler test suite does not load these files. They are checked by opening the
`examples/*.let` fixtures and the compiler's own sources in Neovim with
`filetype=wordlet` and confirming there are no syntax-script errors; the role
mapping above was verified with a token-position probe over a fixture built from
`syntax.md`.
