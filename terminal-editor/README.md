# Terminal editor (working vertical slice)

Build from this directory with `./build.sh`, then run `./editor FILE`. `./test.sh` exercises
scripted editing, a 20,000-key loop at `-O0` with a 256 KiB stack, oversized-file refusal and raw
terminal restoration in a pseudo-terminal. Dependencies: LuaJIT, a C11 compiler, POSIX terminal and
file APIs, GNU `timeout`, and Python 3 for the pseudo-terminal check. The main
`tests/run.lua` runs `test.sh --smoke` from an isolated relocated checkout without Python. Generated `editor.c`, `editor`
and `editor-o0` are ignored.

- **Normal mode:** `h`/`l` move left/right, `i` enters insert mode, `s` or Ctrl-S saves,
  `q` or Ctrl-Q quits without saving.
- **Insert mode:** printable ASCII inserts at the cursor, Backspace deletes before it, Escape
  returns to normal, Ctrl-Q quits. Save after leaving insert mode.
- The document is a **single line of printable ASCII** of at most 4096 bytes. Larger files,
  control bytes (including newline and terminal escape), or an I/O failure opening a file are refused with exit status 2, rather than overwritten from a truncated
  buffer. Missing files start empty and are created when saved. A failed save returns exit status 3
  instead of claiming success; a save without a path also fails. There is no Unicode editing,
  multiline layout, vertical scrolling, search, status bar, undo or asynchronous resize handling yet.
  A bounded horizontal viewport follows the cursor and reads the current terminal width at each key.
- Non-TTY input is accepted for scripts; ANSI clearing and cursor positioning only happen when
  stdout is a TTY. During a scripted run each rendered frame is written sequentially to stdout.

`editor.let` owns the state transitions and a self-tail `run` loop. Its `document_component`
contains a bounded document descriptor; a host-allocated, process-lifetime byte buffer is acquired
inside `main` and enclosed there. `editor_component` owns the document, mode and cursor. The
application partially wires its `save_requested` continuation before supplying runtime data; the
component never opens a file itself. `terminal_renderer_component` handles drawing. The editor
returns `editor_outcome` to its parent rather than calling a parent-owned loop from a handler.
Fields select their declared component interfaces, and child methods borrow actual child places.
This is the executable beginning of GUIDE.md §21/§22/§28, not yet the complete editor sketched
there. Its one-line scope is intentionally explicit.

`host.c` owns POSIX layouts, the process entry, termios, bounded file I/O and the process-lifetime
allocation. `main` uses `defer` to restore raw mode on normal exits; the host additionally restores
at process exit, and handles SIGINT/SIGTERM/SIGHUP by requesting a clean EOF so `defer` runs. No
program can restore terminal state after SIGKILL, a power failure or `abort` (which skips `defer`).
The host exposes no `wordlet_init` call because this program has no runtime module storage.
`emit.lua` invokes the checkout compiler directly rather than depending on `dist/`.
