# Designing and Writing Software in Wordlet

This is the design and naming guide for the language specified in `syntax.md`. It is about how to
think, name and structure Wordlet software, not about grammar. The compiler in this repository is
written in this style, and `examples/*.let` are small programs that follow it; where a rule below has
a hard edge, the section says so rather than promising more than the implementation does.

## Contents

- The Wordlet paradigm
- 1. One semantic vocabulary
- 2. Names carry meaning the type system does not check
- 3. Name the what and the why
- 4. Requirements are the architecture
- 5. Contract first, implementation later
- 6. Continuations are ordinary requirements
- 7. CPS without callback hell
- 8. Continuations first, real input last
- 9. Components are wired words
- 10. Parent/child architecture becomes continuation wiring
- 11. Use sums when the choice is data
- 12. Partial supply is specialization
- 13. There is no separate comptime programming style
- 14. The program is the outermost word
- 15. Runtime values should have runtime provenance
- 16. `ptr` marks the edge of the runtime world
- 17. Unsafe is capability-shaped, not scope-shaped
- 18. `ref`, `defer` and CPS form the safe-facing resource pattern
- 19. Arity is still part of the contract
- 20. Tail position matters architecturally
- 21. The fastest abstraction is the one that disappears
- 22. The text editor as a complete Wordlet architecture
- 23. Design from the user inward
- 24. Design so binding time is visible without annotations
- 25. Avoid importing foreign abstractions literally
- 26. A Wordlet code review should ask semantic questions
- 27. Wordlet naming rules
- 28. Modules should expose vocabulary, not implementation debris
- 29. Handlers as requirements: hierarchical continuation wiring
- 30. The central Wordlet instinct

---

## The Wordlet paradigm

Wordlet is easiest to understand by forgetting many of the categories inherited from conventional
languages. Do not begin with classes, interfaces, templates, callbacks, compile-time functions,
runtime functions, unsafe blocks, dependency injection or type-level programming.

Begin with **words**.

A word has requirements. Requirements may be ordered or keyed. Supplying requirements produces a
more specific word. When all remaining requirements are supplied, the word is saturated and its
terminal may execute: a call, a construction, or a match.

That simple model is the center of the language. The syntax contract describes the core in exactly
these terms: words have ordered or keyed requirements, an optional result contract and an optional
terminal; signatures describe requirements without an implementation; a schema is a word with keyed
requirements and a construction terminal; a method is an executable word with an implicitly bound
receiver (`syntax.md` §2, §3, §4).

The important consequence is that many things which are separate mechanisms elsewhere become
different uses of one idea:

- a **generic** is a word requiring a type;
- a **configured algorithm** is a word whose policy requirements have been supplied;
- a **component** is a keyed word whose continuation requirements have been wired;
- a **constructor** is a schema reaching saturation;
- a **program** is the outermost word, whose remaining requirements come from the runtime world.

So the central question when designing Wordlet software is:

> **What are the words, what do they require, and which requirements become known when?**

---

## 1. One semantic vocabulary

Wordlet deliberately weakens the conventional division between types and values. Types are
compile-time values, and a word can simply require one:

```text
let identity(t: type, x: t) = x
```

Generic programming therefore needs no template or generic subsystem. A generic is an ordinary word
whose requirements include a value of `type` (`syntax.md` §10). There is no implicit generic
parameter mechanism, and no way for a runtime value to supply a type.

This has a stylistic consequence that runs through the whole guide. A name should describe the
**concept**, not advertise which syntactic category the concept currently occupies. Wordlet does not
need:

```text
Document
IDocument
DocumentImpl
DocumentType
DocumentValue
```

to tell the reader what they are looking at. It needs:

```text
document
editable_document
document_byte_offset
document_cursor_position
```

The surrounding use already says whether a word is being used as a type, a value, a schema, a
signature or an executable word. Capitalization carries no meaning in Wordlet, so it should not be
spent as if it did.

The language's own vocabulary is therefore lowercase, and there is no second spelling of any of it:

```text
u8  u16  u32  u64  i32  i64  f64
bool  unit  type
string  null  ref  ptr  array  slice  oneof
```

Those are the representation-level words, and they are reserved at module level: a module-level
`let`, `extern` or word declaration may not rebind `u32` or `oneof` (`reserved`), because that would
silently change what the program's own vocabulary means. A local binding inside a body may shadow
one, like any outer name (`syntax.md` §1).

Wordlet's vocabulary is deliberately small, and that is the point. It should not own the word
`document`, and a program should not keep saying `array` and `u8` long after it knows what the thing
means. The pressure is:

> **A primitive name tells you how something is represented. A program name tells you what it
> means.**

The programmer should spend most of their naming effort in the second vocabulary:

```text
let document_byte_offset = u32
let document_line_number = u32
let terminal_column = u32
let unicode_codepoint = u32

let document_bytes = array(u8, 4096)
let terminal_cells = array(terminal_render_cell, 80 * 24)
let visible_text = slice(document_character)

let editor_mode = oneof { normal: unit, insert: unit, visual: unit }
```

A type is just another value in the word system, so `let document_byte_offset = u32` reads as ordinary
Wordlet. The surface language ends up agreeing with the semantics instead of teaching a second,
typographic one.

---

## 2. Names carry meaning the type system does not check

A text editor is full of values a machine would happily store as integers:

```text
document_byte_offset
document_line_number
document_column
terminal_row
terminal_column
viewport_line_offset
unicode_codepoint
```

These should not become interchangeable merely because their representation is identical. Naming
them separately is how the distinction stays visible:

```text
let document_byte_offset = u32
let terminal_column = u32
```

It is important to be precise about what that buys, because it is easy to assume more.

**Type equality in Wordlet is structural, with a reserved identity only for recursive definitions**
(`syntax.md` §8.2). Two record schemas with the same fields are the same type. A definition that
names a primitive is an alias, not a new type. So this is accepted:

```text
let document_byte_offset = u32
let terminal_column = u32

let advance(offset: document_byte_offset): u32 = offset

let n: u32 = 4
let ok = advance(n)                    -- a bare u32 is accepted

let c: terminal_column = 7
let also_ok = advance(c)               -- so is a different alias
```

That is worth stating plainly, because a guide that claimed otherwise would be describing a language
Wordlet is not:

> **A descriptive name documents a distinction. It does not enforce one.**

### Why identity follows meaning

This is not an oversight, and it is not only a simplification. It follows from three properties of
the language, and it is worth understanding them before wishing for nominal aliases.

**A type is a value, and equal values are equal.** `Ty` is an interned token: two structurally equal
types are one value, and `==` is the whole comparison (`structure.md`). `S.encode` exists only to
build a key string. That is what lets the compiler ask "is this the type I need?" with one operation
instead of three.

**Types specialize, so sharing them is not free to give up.** A generic is a word requiring a `type`
(section 1). With meaning-based identity, `identity(u32)` is one specialization no matter how many
names a program gives to `u32`. Under nominal identity every alias would be its own instantiation:
more emitted functions, more compile time, and no way to notice that the two instantiations were the
same code.

**Equal shapes are one layout.** The C backend keys its layout registries per family by the type that
asked for them, so equal shapes emit one struct. The same reasoning gives `oneof` its canonical rule:
alternative order is canonical, not written order, so two spellings of the same alternatives are the
same type and one layout (`syntax.md` §8.1, §8.2). Nominal aliases would make that rule quietly
false whenever two spellings differed only in which alias they mentioned.

Identity is still nominal in one place, deliberately: a recursive definition reserves a cell for
itself, because otherwise the type written inside the definition and the type of an instance built
from it would not compare equal — and only one such cell is kept per structural meaning. So the
language is not "structural everywhere". It is nominal exactly where a hole has to be filled by
identity, and meaning-based everywhere the question is really about shape.

### When you do need it checked

Naming is still architecture — the reviewer, the reader and the search box all see the distinction,
and the name is what stops a real mistake from looking plausible. But where a distinction must be
*checked*, it has to be paid for in structure. Four shapes do it:

- **different shape**: a record with named fields (`document_byte_offset` travels as a record, not a
  `u32`);
- **different guarantee**: `ref(T)` and `ptr(T)` are deliberately different types
  (`syntax.md` §8.5), as are `array(T, N)` and `slice(T)`;
- **different alternative set**: a `oneof` whose alternatives cannot be confused;
- **different behaviour**: a word that takes a `document_byte_offset` and validates it.

There is a fifth answer that costs nothing, and it is usually the right one inside a large program:
**move the arithmetic behind a boundary**. If one component is the only code allowed to add two
offsets, the distinction is enforced by the structure of the program rather than by the type. That is
the same move section 17 makes for `ptr`, applied to a unit of measure: keep the raw representation
inside the layer entitled to it, and let everything above speak in domain words.

So the two halves of this section pull in the same direction:

> **Representation may be shared. Meaning should stay visible in the name — and where it must be
> enforced, it needs a shape, a guarantee or an alternative set, not a longer word.**

This is also why the compiler's own diagnostics print the *type*, not the alias: `Expected u32 but
found bool` is a statement about representation, which is what was actually checked.

---

## 3. Name the what and the why

A useful naming discipline is **what_why**. It does not mean every identifier contains exactly two
grammatical words. It means a name should usually communicate:

> **What is this thing, and why is it distinct here?**

For types:

```text
document_byte_offset
terminal_render_cell
validated_document
file_load_error
search_match_range
```

The qualifier carries the semantic reason for the distinction.

For operations, verb-object names are often clearest:

```text
move_cursor
insert_text
delete_selection
open_document
save_document
render_viewport
```

For continuations and outcomes, name the event or condition that explains why control arrives there:

```text
document_changed
save_requested
file_load_failed
search_match_found
command_cancelled
quit_requested
```

Avoid names that explain only programming machinery:

```text
callback  handler  done  next  manager  context  data  info  result
```

when a domain name is available. This matters especially in continuation-passing architecture,
because a continuation name is effectively the name of an exit from the current computation. Instead
of:

```text
success
failure
```

prefer:

```text
document_loaded
document_load_failed
```

The program should read as the domain, not as the machinery used to implement the domain. Section 27
collects these rules as a checklist.

### Prefer explicit names over short names

Long names are acceptable when they remove ambiguity.

Prefer:

```text
production_configuration
payment_authorization_policy
validated_customer_address
inventory_reservation
on_payment_authorization_failed
```

over:

```text
cfg  pol  addr  res  cb
```

unless a short name is genuinely obvious in a tiny local scope:

```text
let distance(x, y: f64): f64 =
    if x < y then y - x else x - y
```

is perfectly clear, but:

```text
let connect(c, p, t, r) = ...
```

is poor if the parameters actually mean `configuration`, `port`, `transport` and `retry_policy`.

> The wider the scope and the more architectural the concept, the more explicit its name should be.

### Specialized words should name what has been fixed

Specialization creates meaningful architectural concepts. Name them for the knowledge they carry:

```text
let production_renderer = renderer {
    format = html,
    policy = production_policy,
}

let authenticated_request_handler = ...
let jpeg_thumbnail_encoder = ...
let database_backed_session_store = ...
```

not `specialized_renderer_1`.

---

## 4. Requirements are the architecture

A Wordlet word is best understood through what it requires.

Ordered application uses `()`. Keyed application uses `{}`. They express two kinds of identity:
position, and name.

Use ordered requirements when position is meaningful:

```text
resize(width, height, image)
encode(format, quality, image)
authorize(policy, user, request)
```

Use keyed requirements when the names are the meaningful identity:

```text
run {
    database = database,
    logger = logger,
    retry_policy = retry_policy,
    clock = clock,
    on_processing_failed = processing_failed,
    on_processing_completed = processing_completed,
}
```

The aggregate documents its own requirements, and independent specialization becomes natural. Two
useful design signals:

> If you are constantly asking what argument number five means, the requirements probably want keys.

> If you are imposing an order on requirements that do not depend on each other, that is also a
> sign they want keys.

Keyed words are especially suitable for configuration, capabilities, environments, policies, sets of
handlers, protocol operations, continuations and the construction of structured data. Field order
does not define schema identity, so a keyed supply may be written in any order and two spellings of
the same fields are the same schema.

A schema is the same mechanism with a construction terminal, so `distance { ... }` and
`server { ... }` are one thing:

```text
let server = {
    host: host,
    port: u32,
    logger: logger,
    clock: clock,
    retry: retry_policy,
}

let production_server = server {
    logger = production_logger,
    retry = production_retry,
}
```

This gives Wordlet a component model without introducing a component system:

> **Requirements are the interface. The word or schema is the component. Partial keyed supply is
> wiring. Saturation creates the runtime instance.**

---

## 5. Contract first, implementation later

Because signatures describe callable requirements independently of any implementation, architecture
can be designed before bodies exist.

For a text editor, begin at the visible behaviour:

```text
let editor_input = oneof {
    key_pressed: key_event,
    terminal_resized: terminal_size,
}
```

Then say what the editor may ask of its parent:

```text
let editor_component = {
    document_changed: (editable_document): unit,
    save_requested: (editable_document): unit,
    quit_requested: (): unit,

    document: editable_document,
    cursor: document_cursor_position,
    mode: editor_mode,

    handle_input(input: editor_input): unit = ...
}
```

Before `handle_input` has a body, the architecture already says a great deal. The editor owns local
state. It receives real runtime input. It does not save files directly. It does not terminate the
process directly. It reaches outward through named continuation requirements, and the parent decides
what those requests mean.

That permits a top-down workflow:

```text
user-visible behaviour
        ↓
component contracts
        ↓
continuation wiring
        ↓
domain operations
        ↓
safe system wrappers
        ↓
extern / operating system
```

Implementation fills in a structure that is already meaningful, and the architecture is executable
long before every body is interesting. Section 23 works this workflow through in full.

---

## 6. Continuations are ordinary requirements

Continuation-passing style is not a special Wordlet feature. That is precisely why it fits.

A continuation is simply another callable requirement:

```text
let load_document(
    document_loaded: (document): unit,
    document_load_failed: (file_load_error): unit,
    path: file_path,
): unit = ...
```

There is no callback subsystem, no listener hierarchy, no promise object, and no special syntax for
control transfer. It is supply.

Two properties make this cheaper than it sounds elsewhere. First, a callable requirement is a
*signature*, so it constrains the callee without forcing a representation on it. Second, when the
callee is known code, its code identity stays known: a known handler specializes into the call site,
and only a handler that actually arrives from the runtime world needs the invocation-pointer ABI.
Known code does not automatically decay into an indirect call.

Borrowed closures and method values can be passed through non-retaining callable interfaces, but they
cannot be returned or stored as though they owned their environment (`syntax.md` §9). So the
capability a child keeps past its owner's activation has to be owned code or a value it returns. That
is not friction; it is the type system enforcing the containment the pattern is trying to express,
and `borrow-escape` and `ref-escape` fire exactly when a child tried to keep authority past its
owner's lifetime.

---

## 7. CPS without callback hell

JavaScript-style callback nesting comes largely from making continuations part of the *syntax*:

```text
load(path, document => {
    parse(document, syntax => {
        analyze(syntax, result => {
            ...
        })
    })
})
```

Wordlet does not need to express CPS that way. Continuations can be named requirements, and the wiring
can happen where components are composed:

```text
let document_loader = {
    document_loaded: (document): unit,
    document_load_failed: (file_load_error): unit,

    load(path: file_path): unit = ...
}

let application_document_loader = document_loader {
    document_loaded = application_document_loaded,
    document_load_failed = application_document_load_failed,
}
```

Runtime use is then an ordinary call:

```text
application_document_loader.load(path)
```

The control graph is expressed in the architecture rather than in indentation:

> **Name continuations by domain transition, and wire them where components are composed.**

Use CPS because controlling where computation continues is clearer than transferring ownership of
intermediate state — not because it is fashionable. The compiler uses the same shape for its own
recursion: `search`-style passes and threaded dispatch are CPS because the state belongs to the
enclosing owner.

---

## 8. Continuations first, real input last

Ordered supply makes parameter order architectural. Supplying fewer than the remaining ordered
requirements produces a specialized word, and those supplied requirements must be static
(`syntax.md` §2). Saturation happens only when exactly the remaining requirements are supplied.

So ordered words naturally want stable architectural requirements before varying runtime input:

```text
let process(
    completed: (process_result): unit,
    failed: (process_error): unit,
    input: process_input,
): unit = ...
```

Then:

```text
let application_process = process(
    application_process_completed,
    application_process_failed,
)

application_process(input)
```

The source itself communicates binding time. A useful default ordering:

```text
structural / least variable
        ↓
type
algorithm
policy
configuration
        ↓
owned state
        ↓
per-call input
most variable
```

or, more compactly:

> **Contract first, input last.**

Requirements are evaluated left to right, and an earlier parameter may determine a later requirement
(`syntax.md` §2):

```text
let identity(t: type, x: t) = x
```

Here `t` must be known before `x` can be checked. This is ordinary type demand, not an implicit
generic parameter or a `static` keyword. The ordering is a heuristic, not a law: if two requirements
are independent enough that ordering them is artificial, use keys and let them be independent.

---

## 9. Components are wired words

For stateful software, keyed supply gives the same pattern a cleaner form. First wire the outward
contract; those supplied fields belong to the specialized component and their values are statically
known:

```text
let application_editor = editor_component {
    document_changed = application_document_changed,
    save_requested = application_save_requested,
    quit_requested = application_quit_requested,
}
```

Then create the runtime instance by supplying its state:

```text
let editor = application_editor {
    document = initial_document,
    cursor = initial_cursor_position,
    viewport = initial_viewport,
    mode = editor_mode.normal(),
}
```

The conceptual sequence is:

```text
define contract
      ↓
wire known continuations
      ↓
supply runtime state
      ↓
feed runtime input
```

Or, naming the stages: `editor_component` is the contract, `application_editor` is the component
wired for this application, and `editor` is the runtime instance. That vocabulary is worth keeping
explicit, because it makes the binding-time structure visible in the names themselves.

The pattern generalizes well beyond editors. A parser, protocol engine, game object, UI widget,
compiler pass, storage subsystem or network service can all be structured as a word with known
outward continuations, owned local state, and runtime input.

One caveat about the boundary: a word with a `type` requirement has no closed runtime ABI, so it
cannot itself be exported as a function. Specialize it first and export the specialization
(`syntax.md` §10):

```text
let identity_u32 = identity(u32)   -- export this, not `identity`
```

---

## 10. Parent/child architecture becomes continuation wiring

A larger application can be organized as nested stateful words. The parent owns its children, children
own local mutable state, and a child does not need global access to the parent. Instead, the parent
supplies exactly the continuations each child may invoke:

```text
let search_component = {
    search_match_found: (search_match): unit,
    search_not_found: (): unit,
    search_cancelled: (): unit,

    query: search_query,

    handle_input(input: editor_input): unit = ...
}

let editor_search = search_component {
    search_match_found = editor_move_to_search_match,
    search_not_found = editor_show_search_not_found,
    search_cancelled = editor_restore_search_origin,
}
```

The child therefore does not need `application`, `global_event_bus`, `service_locator`,
`parent_pointer` or `editor_manager`. Its outward authority is exactly its requirements.

```text
parent
 ├─ owns child state
 ├─ supplies child capabilities
 └─ supplies child continuations

child
 ├─ owns local state
 ├─ consumes local input
 └─ transfers meaningful outcomes outward
```

Downward flow is requirements, configuration, capabilities and input. Upward flow is named
continuation transfer. The topology is explicit and local, and section 29 works out the details —
including the capability property that follows, and the places where it is honest about its limits.

---

## 11. Use sums when the choice is data

CPS does not replace sums; they answer different questions.

If a computation naturally produces a value whose alternative must survive as data, use a sum:

```text
let file_load_result = oneof {
    loaded: document,
    failed: file_load_error,
}

let result = load_document(path)

result {
    loaded = handle_document_loaded,
    failed = handle_document_load_failed,
}
```

If the choice exists only to decide where control goes next, direct continuations express the intent
more directly:

```text
let load_document(
    document_loaded: (document): unit,
    document_load_failed: (file_load_error): unit,
    path: file_path,
): unit = ...
```

> **If the choice is data, use a sum. If the choice is control, continuations can express it
> directly.**

Choose by meaning, not by anticipated machine code. A sum is also the right answer when the outcome
must be deferred, stored, returned across a boundary, or handled exhaustively by someone else, and it
is the reason `oneof` exists rather than a hierarchy of classes: a match on a known tag selects its
handler while compiling, an opaque tag becomes a C `switch` on the tag with the last alternative as
`default`, and a small opcode set becomes a couple of compares rather than a chain.

---

## 12. Partial supply is specialization

Partial application in Wordlet is not primarily a closure convenience. It is specialization:

```text
let affine(a, b, x: u32): u32 = a * x + b
let transform = affine(4, 3)
```

`transform` is a word whose structural choices have already been supplied. Partial ordered arguments
must be static, because the result is a compile-time specialization rather than an implicitly
allocated closure (`syntax.md` §2).

The same is true of partial keyed supply, which makes supplied members *statically known*:

```text
let point = {
    x: u32,
    y: u32,
}

let at_x3 = point {
    x = 3,
}
```

`x` is part of the specialized schema, so a use of that field can resolve to the known value instead
of becoming a runtime load: for `at_x3 { y = 4 }.x`, the compiler emits the constant directly.

Be precise about what "known" means here, because it is easy to overstate. A partially supplied schema
is not frozen. Once the instance is constructed, its fields are ordinary mutable instance storage, and
a store is honoured:

```text
let configured = session { limit = 100 }
let c = configured { attempts = 0 }
c.limit = 200          -- allowed; the field is instance storage
```

What partial supply gives you is *knowledge at compile time*, which the compiler may use where it is
still valid — not `readonly` fields. The mental model is:

```text
partial keyed supply
    → structural knowledge

saturated construction
    → runtime instance
```

which leads to the design instinct:

> **Supply structure early. Supply changing data late.**

---

## 13. There is no separate comptime programming style

Wordlet does not make the programmer continually classify code as compile-time or runtime code. The
compiler follows what is actually known.

If everything a computation needs is known, the computation can proceed. When it meets genuine
runtime uncertainty, that part remains residual. The implementation reflects this directly:
normalization and residual evaluation share the same evaluator rules; normalization simply has no IR
builder, while residual evaluation emits into the runtime IR (`architecture.md`).

```text
program
  ↓
supply known architecture
  ↓
evaluate
  ↓
specialize
  ↓
reach runtime uncertainty
  ↓
emit residual control flow
```

Think of it as **comptime tracing**: the compiler traces through everything it can know and emits the
specialized residual control-flow graph for everything it cannot know yet. There is no `static`,
`comptime`, `constexpr` or `dyn` to scatter through ordinary architecture, because binding time
emerges from provenance rather than annotation.

So do not ask:

> Is this expression a specialization or a call?

Ask:

> Which parts of this invocation are known, and which parts must survive to runtime?

---

## 14. The program is the outermost word

Taken far enough, the entire application is a progressively supplied word.

At the top, the program contains an enormous amount of known structure: component topology,
continuation wiring, types, algorithms, rendering strategy, keymap policy, protocol rules, foreign
bindings. Compilation supplies and follows those choices.

Eventually it reaches things that cannot be known yet:

```text
a key the user has not pressed
bytes the operating system has not returned
the current terminal dimensions
a packet that has not arrived
mutable state changed by previous input
```

Those are the remaining runtime requirements. A `.let` file may define `main` as its program entry,
in which case `main` is the sole export when no explicit export configuration is given
(`syntax.md` §11).

So rather than asking:

> Which parts of my program did I mark compile-time?

ask:

> Why is this value runtime?

That is the more revealing question, and it is usually answerable. The next two sections are about
answering it: runtime values should have runtime provenance, and unchecked memory should have `ptr`
provenance.

---

## 15. Runtime values should have runtime provenance

In ordinary application software, genuine runtime uncertainty has surprisingly few roots. For a text
editor:

```text
keyboard input
terminal resize
file contents
filesystem results
clock / OS state
foreign calls
```

Everything derived from those values may naturally remain runtime, and mutable state remains runtime
because it is the accumulated history of previous runtime interactions:

> **Mutable state is memory of uncertainty.**

The document buffer is runtime because the user has edited it. The cursor is runtime because previous
input moved it. The active mode is runtime because previous commands changed it. The viewport is
runtime because it depends on the document, the cursor and the terminal size.

But the implementation of normal mode does not need to be runtime. The keymap policy does not need to
be runtime. The continuation used when saving succeeds does not need to be runtime. The rendering
algorithm does not need to be runtime.

> **Stable structure specializes. Evolving state residualizes.**

That is the whole of section 13 stated as a slogan, and it is also a review test. For any value, ask
where it came from. If the answer is a chain of twelve steps ending in "a key event", fine — but if it
ends in "a configuration decision made before the program started", the value is probably a
specialization that has not been noticed yet.

`extern` is the clearest single boundary: a foreign call is an effect the compiler cannot see into, so
it is never folded, and even constant arguments do not make it foldable (`syntax.md` §8.6). Anything
that crosses that boundary is runtime by construction, which is exactly why the next section is about
`ptr`.

---

## 16. `ptr` marks the edge of the runtime world

There is an interesting convergence here. Unsafe memory enters from the same places as runtime
uncertainty: operating systems and foreign libraries hand the program addresses, buffers, mappings,
device memory and packet memory.

```text
extern / operating system
        ↓
ptr / bytes / scalar result
        ↓
safe domain wrapper
        ↓
runtime domain value
        ↓
mutable application state
```

So `ptr` is important in two ways at once. It marks unchecked memory, and it usually sits very near
the origin of values that genuinely have to remain runtime.

The language is explicit about the first meaning. `ptr(T)` is an address the compiler does not track:
it may be null, stored in module storage, captured, returned, copied and compared, and it may outlive
the storage it points at (`syntax.md` §8.5). That is the point of the type — this is the part of the
language where the programmer is responsible, and the compiler says so by offering no rule to break.

`ptr(place)` is the only conversion that drops a lifetime, deliberately, and there is no conversion in
the other direction: `ref(p)` rejects, because an unchecked address must not become a checked borrow:

```text
let xs = [1, 2, 3]
let p = ptr(xs[0])          -- ptr(u32); the lifetime is written off here, deliberately
```

That gives two questions worth asking about any value that reaches deep into a program:

> **Where did this runtime value come from?**

> **Where did this unchecked pointer come from?**

Both answers should be short. If either one is long, that is the design telling you where a boundary
is missing.

---

## 17. Unsafe is capability-shaped, not scope-shaped

Wordlet does not use an `unsafe { ... }` block as its primary safety model. The unsafe thing is the
`ptr`, and that is valuable: the dangerous capability has a concrete type and a spelling, so it can be
grepped for.

The preferred architecture is therefore not to spread `ptr` through domain code, but to wrap it
immediately:

```text
ptr(u8)
   ↓
file_read_memory
   ↓
decode_file_contents
   ↓
document_text
```

```text
ptr(terminal_render_cell)
   ↓
terminal_frame_storage
   ↓
terminal_renderer
```

The primitive describes representation; the wrapper restores domain meaning. And because the wrapper
is where the length and lifetime obligations are discharged, the wrapper is also where the review
should happen.

> **`ptr` should be rare, shallow, and immediately enclosed behind a more meaningful interface.**

One honest limit belongs here. A wrapper named `file_read_memory` is not by itself safer than the
`ptr` it wraps; the name is a promise the wrapper's code has to keep. What makes the design work is
that there is exactly one place to check.

---

## 18. `ref`, `defer` and CPS form the safe-facing resource pattern

A raw pointer may be needed internally while higher-level code should interact through a constrained
borrowed interface. The resource owner can acquire the pointer, schedule cleanup with `defer`, expose
checked operations, and invoke the computation that needs temporary access through a continuation:

```text
acquire ptr
    ↓
construct constrained resource interface
    ↓
invoke continuation
    ↓
continuation finishes
    ↓
defer releases ptr
```

`defer` is the release point: it attaches an action to the end of the block it appears in, its
arguments are snapshotted where it is written, deferred actions in one block run in reverse order, and
a conditional's arm is its own block (`syntax.md` §8.8). It is a statement form and not a type, so it
tracks nothing: it does not prevent the resource from escaping through the pointer. It defines *when*
cleanup happens, not *whether* access was legal.

The `ref`/CPS half supplies what `defer` cannot. Because a borrowed reference to a local cannot escape
its activation (`ref-escape`, `syntax.md` §8.2), keeping the computation that needs access *inside* the
owner's lifetime is the way to keep the borrow checked. The high-level pattern is:

> **Keep `ptr` inside the unsafe implementation. Expose a checked borrowed interface. Use CPS to keep
> the computation requiring access inside the resource's lifetime. Use `defer` to define cleanup.**

That keeps unsafe memory local without requiring a syntactic unsafe region, and it is the same
containment argument as section 6, applied to memory instead of capability.

---

## 19. Arity is still part of the contract

Partial supply does not mean Wordlet gives up useful arity errors. The semantics distinguish three
cases:

```text
fewer than remaining requirements
    → specialized word

exactly remaining requirements
    → saturation

more than remaining requirements
    → error
```

The third case is a real diagnostic: over-application rejects (`arity`), because a word has a fixed
contract rather than variadic behaviour.

The first case is the interesting one, because "too few arguments" is not locally illegal. A
partially supplied word is still a precise contract, so accidentally leaving requirements unsatisfied
changes the *shape* of the resulting value. If the surrounding context expects
`(editor_input): unit` and the programmer produced a word that still requires one more value, the
mismatch appears at the contract boundary — when that word is used, not where it was supplied.

That is what gives partial supply its flexibility without turning calls into unchecked variadic
behaviour: the compiler is not counting arguments, it is checking shapes.

---

## 20. Tail position matters architecturally

CPS encourages code where one computation transfers control to another rather than returning through
many suspended callers. That makes tail position meaningful: if a word has no work remaining after
transferring control, there is no conceptual reason to retain the current frame.

The implementation goes further than self-recursion. It recognizes **safe tail components** — sets of
residual functions whose tail calls to each other reuse one activation — and lowers them to jumps
rather than calls, including scalar mutual recursion, nested diamonds and multi-member swaps. The
proof is deliberately conservative: it requires scalar by-value formals and results and scalar owned
representation, and exposure through an address, borrow, view or indirect binding prevents it. Where
the proof does not hold, the call stays an ordinary call, so an unproved lifetime is compiled
correctly rather than miscompiled for speed (`VALIDATION.md`).

Two things follow. First, write the transfer in tail position when nothing remains to do; mutual
recursion between known words is a supported shape, not a trap. Second, remember that `defer`
intentionally prevents the rewrite, because deferred work must happen after the call returns
(`syntax.md` §8.8).

### Threaded dispatch is reified-continuation CPS

For an interpreter or any dynamic dispatch, the continuation should be **data**. A keyed match whose
handler lambdas call the loop is a *different code instance*, so that call is an ordinary call and the
stack grows one frame per step. Return the next state from the handlers instead, and let one tail call
in the loop word's own body drive it:

```text
let advance(m: machine): machine =
  m.code[m.pc] {
    push = |value: u32| -> do ... return m end,
    add  = |unit: unit| -> do ... return m end,
    halt = |unit: unit| -> do m.done = true return m end,
  }

let run(m: machine): u32 = do
  let next = advance(m)
  if next.done then return next.result end
  return run(next)
end
```

`run(next)` is in `run`'s own tail position, and the handler lambdas only return a machine, so their
frames do not stay on the stack. `examples/dispatch.let` is this shape.

Prefer the hot state as the loop's **parameters** rather than a record: a code `ptr`, the `pc`, a
stack `ptr` and `sp` are one word each, so a step copies no aggregate at all, and the handlers return
the transition instead of the machine. `examples/interpreter.let` is that form — one back edge, no
per-step copy.

As the opcode set grows, an opaque match lowers to a C `switch` on the tag with the last alternative
as `default`, so the branch is total and a dense tag range becomes one `jmp *` jump table rather than
a chain of compares. The choice is binding time, not syntax: a handler set known at compile time
becomes direct specialized code, while a handler set that arrives at run time becomes the callable
ABI.

---

## 21. The fastest abstraction is the one that disappears

Wordlet's performance philosophy follows from the same architecture.

A traditional language asks:

> How can this abstraction become cheaper at runtime?

Wordlet should often ask:

> Why does this abstraction need to exist at runtime at all?

A continuation whose implementation is statically known does not need generic callback machinery. A
component whose wiring is statically known does not need a runtime dependency container. A policy
selected at compile time does not need a runtime strategy object. A type supplied to a generic does
not need a runtime descriptor. A sum whose alternative is already known does not need runtime tag
dispatch at that occurrence. Known aggregate members can resolve to constants.

> **The fastest code is code you do not run.**

Rich architecture at the source level is not opposed to low-level output when the architecture itself
is known early enough to specialize away. But be honest about the boundary: this only holds while the
knowledge reaches the point of use. Once a handler crosses an export, once a value arrives from the
host, once a policy comes from mutable storage, the abstraction is real and the runtime
representation is real. That is the binding-time lever, and it is the subject of section 24.

---

## 22. The text editor as a complete Wordlet architecture

A Wordlet text editor can be designed almost entirely from domain types, stateful words and
continuation contracts before any low-level implementation appears.

Start with semantic types:

```text
document
editable_document
document_byte_offset
document_line_number
document_column

document_cursor_position
document_selection_range
document_viewport

terminal_row
terminal_column
terminal_size
terminal_render_cell

key_event
editor_input
editor_mode

search_query
search_match
editor_command

file_path
file_load_error
file_save_error
```

Define the mode as data, because a mode is something other code will need to inspect:

```text
let editor_mode = oneof {
    normal: unit,
    insert: unit,
    visual: unit,
    command: unit,
}
```

Define the components. Each is a keyed word whose continuation requirements are its outward
authority, and whose remaining keys are its owned state:

```text
let editor_component = {
    document_changed: (editable_document): unit,
    save_requested: (editable_document): unit,
    quit_requested: (): unit,

    document: editable_document,
    cursor: document_cursor_position,
    viewport: document_viewport,
    mode: editor_mode,

    handle_input(input: editor_input): unit = ...
}

let search_component = {
    search_match_found: (search_match): unit,
    search_not_found: (): unit,
    search_cancelled: (): unit,

    query: search_query,

    handle_input(input: editor_input): unit = ...
}

let command_line_component = {
    command_submitted: (editor_command): unit,
    command_cancelled: (): unit,

    command_text: command_text,

    handle_input(input: editor_input): unit = ...
}

let terminal_renderer_component = {
    frame_ready: (terminal_frame): unit,

    terminal_size: terminal_size,

    render(
        document: editable_document,
        cursor: document_cursor_position,
        viewport: document_viewport,
    ): unit = ...
}
```

Then wire the application. The child contracts are supplied where the components are composed, so the
control graph is written down rather than implied:

```text
let application_search = search_component {
    search_match_found = editor_move_to_search_match,
    search_not_found = editor_show_search_not_found,
    search_cancelled = editor_restore_search_origin,
}

let application_editor = editor_component {
    document_changed = application_document_changed,
    save_requested = application_save_requested,
    quit_requested = application_quit_requested,
}
```

And only much further down does the architecture reach the operating system:

```text
extern let terminal_read(fd: u32, buffer: ptr(u8), capacity: u32): u32
extern let terminal_write(fd: u32, buffer: ptr(u8), length: u32): u32
extern let file_read(fd: u32, buffer: ptr(u8), capacity: u32): u32
```

Those `ptr(u8)` values should be wrapped immediately in domain vocabulary, as in section 17:

```text
terminal_input_memory
terminal_output_memory
file_read_memory
```

The top of the program therefore talks almost exclusively about editing, and the bottom talks about
representation and the machine. That separation emerges from vocabulary rather than from a heavyweight
framework — which is the practical payoff of sections 1 through 3.

This sketch is a design, not a compiled program: this repository's `examples/` contain the dispatch,
interpreter, pipeline and reference examples, not the editor. Its purpose is to show the shape a real
program takes when the sections above are followed in order.

---

## 23. Design from the user inward

The practical workflow is to begin with what the user can observe. For the editor, ask:

```text
What can happen?
What state changes?
What can each component request?
What information must cross each boundary?
```

Then name those concepts, define the types, define the continuation contracts, define component state,
wire parents to children, and only then fill in algorithms. Finally descend to `extern`, raw memory and
operating-system interaction.

This reverses the usual systems-programming instinct to start from representation. Wordlet's
primitives are powerful enough that representation can come later; the first job is to discover the
semantic vocabulary.

When faced with an empty project, avoid beginning with containers:

```text
manager  controller  service  factory  repository  processor  context
```

Start by naming the actual operations, which already reveal much of the architecture:

```text
lex  parse  check  lower  emit          -- a compiler
resize  crop  encode  save              -- an image pipeline
authenticate  authorize  route  respond -- a network service
```

Then state their requirements:

```text
resize(width, height, image)
encode(format, quality, image)
authorize(policy, user, request)
```

The program now has structure without a class hierarchy, a dependency-injection container or an
architectural framework. Larger structures should emerge when repeated requirements reveal that they
belong together — and when they do, they will usually emerge as a *word with requirements*, not as a
category of object.

---

## 24. Design so binding time is visible without annotations

Good Wordlet architecture naturally exposes which things change frequently and which do not:

```text
application_editor        continuations fixed once for the program
editor                    state that changes throughout execution
editor.handle_input(input)  the genuinely new runtime information
```

The source mirrors the binding-time hierarchy:

```text
component definition
        ↓
application wiring
        ↓
runtime instance
        ↓
runtime input
```

That is preferable to sprinkling staging keywords through the program. The programmer expresses
meaning, and binding time follows from meaning.

The lever for changing binding time is always the same: make a value come from a parameter, a foreign
result or mutable storage, and it moves to runtime; make it come from a definition, and it specializes
away. Use it deliberately — moving a *dimension* to run time is a real architectural decision with a
real runtime cost, not a detail.

---

## 25. Avoid importing foreign abstractions literally

Many familiar abstractions are solutions to constraints Wordlet does not necessarily have. Before
introducing a conventional pattern, ask what problem it was originally solving.

| The pattern was for | Wordlet's answer |
| --- | --- |
| dynamic dispatch through a class hierarchy | a sum if the alternatives are data, continuation requirements if they are control |
| a callback interface because functions were not ordinary typed values | a callable requirement |
| a dependency-injection framework because wiring could not participate in compilation | partial keyed supply |
| a resource object with a destructor to delimit lifetime | an owner word, a borrowed interface, a CPS body and `defer` |
| a template system because types could not be ordinary compile-time values | a requirement of type `type` |
| a runtime strategy object because configuration was assumed dynamic | supply the policy before runtime input |
| an `unsafe { ... }` block as the safety boundary | the `ptr` type itself (section 17) |
| a listener or event-bus hierarchy for upward notification | named continuation requirements (section 29) |

Do not translate patterns mechanically. Translate the **problem** into Wordlet's ontology, and if the
problem does not exist here, do not import its solution.

An important special case: model–view–update works well in its own setting, but its single global
model and untyped message routing are a poor fit. Wordlet's equivalent is hierarchical
continuation wiring under lexical ownership (section 29), and it is worth reading that section before
reaching for an event bus.

---

## 26. A Wordlet code review should ask semantic questions

When reviewing Wordlet code, ask:

- Does every important type name explain what the value means and why it is distinct?
- Are primitives converted into domain vocabulary early enough?
- Where a distinction must be *checked*, does it have a shape, a guarantee or an alternative set —
  rather than only a descriptive alias (section 2)?
- Are stable requirements supplied before frequently changing inputs?
- Should ambiguous ordered requirements actually be keyed?
- Are continuation names domain events rather than generic callback names?
- Can a child request an action through an explicit continuation instead of reaching into unrelated
  state?
- Does every runtime value have an understandable runtime provenance?
- Is mutable state representing genuine evolving state, rather than hiding architecture that could
  have specialized?
- Is `ptr` confined to a small, obvious boundary, wrapped immediately, and is the wrapper actually
  keeping the promise its name makes?
- Is a sum representing persistent data, or merely encoding a control transfer that continuations
  would express more directly?
- Is a call truly in tail position when no work remains, and is a `defer` really needed here?
- Does a partially supplied word accidentally still require something, so that the mistake will
  surface at the wrong boundary?
- Does every exported name belong to a subsystem's vocabulary, and is any `type`-requiring word being
  exported without a specialization?
- Does a runtime abstraction exist because it must, or only because another language would have
  needed it?
- Is the program naming its domain, or naming programming machinery?

The goal is not maximum cleverness. The goal is for the architecture, the safety boundaries, the
binding time and the domain meaning to all be visible in the same source.

---

## 27. Wordlet naming rules

A compact checklist.

### Spell names in lowercase `snake_case`

Wordlet's own words are lowercase, and so are the names a program introduces. Capitalization is not
carrying a category, so there is no reason to spend it: a name spelled `DocumentByteOffset` would
suggest a type/value distinction the language does not make.

### Name the meaning, not the representation

Two values can share a machine representation and still be different ideas. Even when an alias
resolves to the same `u32`, the name is what keeps them from being substituted by mistake — and
section 2 explains when the distinction also needs to be checked.

### Let the containing type supply the context

An alternative lives inside its sum, so it does not need to repeat it:

```text
editor_mode.normal
editor_mode.insert
```

not `EDITOR_MODE_NORMAL`, `NormalMode` or `EditorModeNormal`. The containing type already said which
mode this is.

### Name outcomes for why control arrived

`save_requested`, `document_saved`, `document_save_failed` — not `on_save`, `callback` or
`save_handler`. The first group describes the occurrence; the second describes the plumbing.

### Let scope decide how much qualification is needed

`column` inside terminal-specific code is clearer than `terminal_column` repeated everywhere;
`terminal_column` is better when the file also deals with document columns. Qualify against a
confusion the reader could actually make.

### Avoid machinery suffixes

`manager`, `factory`, `impl`, `interface`, `base`, `abstract`, `dto`, `controller`, `service`,
`callback`, `handler`, `object`, `class` describe the implementation language, not the domain. Use
them only when they are genuinely part of the domain architecture; prefer a capability name —
`load_customer` and `store_customer` over `customer_repository`.

### Prefer domain names over technical wrappers

`validated_order` over `order_result_record`.

### Name keyed requirements for what they mean

`retry_policy`, `database`, `clock`, `on_inventory_unavailable` — not `config1`, `service2`,
`handler`, `callback`.

### Name specializations for the knowledge they contain

`production_renderer`, `jpeg_thumbnail_encoder`, `strict_json_parser`.

### Do not be afraid of long names

Wordlet removes a great deal of structural ceremony. Use some of that saved visual space for names
that communicate meaning.

### A descriptive name is not a guarantee

Naming is architecture, but it is not checking. A callable field named `save_requested` is still just
a callable that may return normally; its name does not make it asynchronous, nor does it prove it
never returns to its caller. A `ptr(u8)` called `terminal_input_buffer` is named better and is exactly
as unchecked as before. Use names to make intent obvious, and use types, ownership rules and tests to
make it true.

---

## 28. Modules should expose vocabulary, not implementation debris

A module exports exactly the names it chooses to expose; non-exported names stay private. Used modules
are reached as namespaces, and modules compiled together share one translation unit and initialization
machinery (`syntax.md` §11).

Treat a module's export list as the public vocabulary of a subsystem:

```text
parse  validate  compile  document  compilation_error
```

not every helper introduced during implementation. A module boundary should make the system easier to
speak about, and the names at that boundary become the language other modules use to describe the
subsystem.

Two practical reminders:

- a generic word taking `type` cannot itself be exported; export a specialization (section 9);
- the export configuration is compile-time module metadata, not a runtime record, and its sections are
  only `types`, `functions` and `results`.

---

## 29. Handlers as requirements: hierarchical continuation wiring

An Elm-style architecture centers on one global model, messages and an update function:

```text
Model → View → Message → Update → Model
```

That predicts beautifully and converges on a fairly global notion of state and message routing.
Wordlet's shape is different:

```text
Parent word
├── owns parent state
├── owns and wires ChildA
├── owns and wires ChildB
├── supplies requirements downward
└── supplies continuations downward

Child
├── owns its local state
├── computes locally
└── reaches the outside only through supplied continuations
```

So the architecture is not "data flows one way". It is **hierarchical control-flow composition under
lexical ownership**. The child does not emit an untyped message into a global update; it receives an
explicit contract, and the parent decides what each exit means:

```text
editor {
    document_changed = update_document_state,
    save_requested = save_current_document,
    close_requested = close_editor,
}
```

The property that follows is stronger than "messages flow upward":

> A child can only affect the outside world through capabilities the parent explicitly supplied.

That is a capability property — the absence of *ambient authority*. A child cannot reach navigation,
persistence or a sibling unless it is given a word that provides that capability. It is a discipline
rather than enforcement: nothing stops a parent from supplying too much, so a review question is
whether each child receives exactly the capabilities its named exits mention.

### This is the handler-in-scope half of algebraic effects

A child's requirements *are* an effect signature, and the parent's supply is the handler:

```text
let admit(
    request: request,
    on_admitted: (accepted): unit,
    on_denied: (rejected): unit,
): unit = ...
```

`on_admitted` and `on_denied` are the operations the child may perform; the parent supplies their
meaning. Keyed application is the `match` that dispatches an outcome, and keyed supply is how a handler
set is built. What Wordlet does *not* add is a resumable, first-class continuation: the child's
"perform" is an ordinary call, so no continuation is captured, and a handler whose identity is known
specializes into the call site — an inlined effect handler.

### The two directions are duals

Capabilities travel downward and outcomes travel upward, and both are continuations:

- **Downward:** the parent supplies words and the child calls them. Use it when the exit happens
  inside the owner's activation.
- **Upward:** the child returns a sum and the parent dispatches it. Use it when the exit must be
  deferred, stored, or cross a boundary.

The ownership model decides which is available, because a borrowed closure cannot escape (section 6).
`examples/pipeline.let` shows one child serving both directions through an `r: type` parameter:
`settle` supplies exits that yield a scalar, `evaluate` returns the outcome as a sum, and `summarize`
dispatches it.

### State ownership and architectural ownership point the same way

A child can own real mutable state without every transition becoming a global message:

```text
let editor = {
    cursor: u32,
    selection: u32,
}
```

and operate on it directly; only what is architecturally meaningful crosses the boundary. You do not
have to choose between "everything is globally immutable data" and "everything has a pointer to
everything else". You get **local mutable ownership with explicit continuation boundaries**.

Methods borrow actual receivers, and nested lexical owners use the actual enclosing records rather than
invented parent pointers, so the architecture tree and the storage tree are the same tree. Siblings
share only through an owner reference or module storage, and both reintroduce the coupling the pattern
otherwise keeps out — which is why they should be deliberate.

### Where it is honest about its limits

- **Componentized source, connected control flow — while handlers are known.** Once a handler crosses
  an export or arrives from the host it becomes the callable ABI, an invocation pointer. The design
  survives; the erasure does not. That is the same binding-time lever as section 24.
- **Continuation chains are stack, not loops.** Parent → child → parent is mutual recursion between
  instances. A recognized safe tail component reuses one activation (section 20), but a deeply nested
  synchronous chain that is *not* recognized still needs a trampoline.
- **Sums are closed, which is both the point and the limit.** A child's outcome set is exhaustively
  handled, which is what makes the wiring readable. Open extension — plugins, third-party messages —
  needs a signature or ABI boundary and gives up the exhaustive match.
- **A child's state is tree-shaped by value.** Records copy on pass and return, so a parent that wants
  a child to mutate shared state passes a place — a method receiver or an enclosing owner — not a
  copy. A `ref` to a sibling local is rejected on purpose (`syntax.md` §8.2).
- **Capabilities are a discipline, not a sandbox.** The compiler enforces lifetimes, not authority. A
  parent can hand a child more than its exits require.
- **Nominal naming is not enforced.** Section 2: aliases are structural, so a distinctive name is a
  documentation and review tool, not a checked distinction.

### The same shape outside UI

This repository's own compiler is the pattern: modules own state, private words are the children, and
the outward vocabulary is limited to what each pass needs. `examples/pipeline.let` is the smallest
complete instance of the shape, and `architecture.md` describes the same structure for the evaluator
and the backend.

---

## 30. The central Wordlet instinct

The deepest Wordlet design instinct can be summarized as:

> **Name the domain. Define its requirements. Supply what is known. Let the compiler follow that
> knowledge until it reaches the real world.**

From that one instinct much of the rest follows.

Types become semantic values. Requirements become interfaces. Partial supply becomes specialization.
Keyed supply becomes wiring. Schemas become components. Continuations become named control exits. CPS
becomes ordinary composition rather than callback syntax. Mutable state becomes memory of runtime
uncertainty. `ptr` marks unchecked access near the external boundary, and `ref`, scoped continuations
and `defer` let safe-facing interfaces contain that boundary. The program becomes a compile-time trace
through known architecture toward a small residual graph rooted in actual runtime input and state.

And optimization stops being something applied after abstraction. The abstraction disappears
precisely because Wordlet understood it.

> **Stable structure specializes.**
> **Evolving state residualizes.**
> **Runtime values have runtime provenance.**
> **Unsafe memory has `ptr` provenance.**
> **Names carry meaning.**
> **Contracts carry architecture.**
> **Only what is runtime is runtime.**
