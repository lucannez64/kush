# Todo terminal app

[examples/todo.kush](../examples/todo.kush) is a Kush terminal app with an ANSI
redrawn task board. It accepts commands followed by Enter, using the terminal's
normal line editing. It does not change terminal modes or hide the cursor.

A Linux x86-64 binary built on Boat is available in this checkout:

```sh
./target/kush-todo
```

Build and run from source on a machine where compilation is allowed:

```sh
cargo run -p kush -- build examples/todo.kush -o /tmp/kush-todo
/tmp/kush-todo
```

In this workspace, compile and test on Boat as required by `AGENTS.md`.

| Command | Action |
| --- | --- |
| `a Buy milk` | Add a task |
| `t 1` | Toggle task 1 between open and done |
| `d 1` | Delete task 1 |
| `f all` | Show all tasks |
| `f open` | Show open tasks |
| `f done` | Show completed tasks |
| `q` | Quit |

IDs stay stable until deletion; adding a task reuses the first free slot.
The board holds 32 tasks with titles of up to 96 printable ASCII characters.
Control characters and non-ASCII titles are rejected before changing state,
so task titles cannot inject terminal control sequences. Invalid commands leave
the board intact and display a message. EOF also exits normally. Input exceeding
the 1024-byte command buffer or an I/O failure exits with status 1.

This first version is session-only: tasks are not saved. It needs an ANSI terminal
and enough space for the board; it has no raw arrow-key handling, scrolling,
resize detection, Unicode display-width handling, or file persistence. These
limits are shown in the app where relevant.

The application uses a preallocated owned vector, mutable slice updates,
last-use borrow release, effect annotations, ordinary `Result` propagation and
deterministic cleanup. The UI allocates frame/message buffers; it does not claim
to be allocation-free. Input uses the bounded, allocation-preserving
`IO.read_line` operation. No Python or Rust UI wrapper is needed at runtime.


Validation: the full remote workspace suite passes 469 tests, formatting and
Clippy. Scripted sessions compare native/reference output and balanced cleanup.
A remote pseudo-terminal test also verifies that the initial prompt appears
before EOF, adding and toggling work interactively, and quitting exits normally.
