# Panics that unwind to a boundary

Status: **implemented** (all nodes below done, 2026-11-15; section 8 says
how each was built). Decided with the user:
full unwinding, a cleanup per linear type spelled `#[linear(unwind = f)]`,
`Task.catch` with uncaught task panics propagating to the joiner, and
structured cancellation (done, TASK-CANCEL-PROPAGATE). Implementation nodes: PANIC-UNWIND-EVAL,
PANIC-UNWIND-NATIVE, PANIC-LINEAR-CLEANUP, PANIC-UNWIND-USE.

## 1. Today

A panic (checked arithmetic, an index or byte out of range, an allocation
refused, `panic()`) aborts the process. WEB-PANIC-500 added a narrow
exception: a task that called the std-only `sys.task_isolate` is finished
by the runtime at its panic, without running any frame's cleanup. What it
owned leaks, the exit ownership check is skipped, and a task with children,
a thread or `main` cannot recover. This design replaces that with real
unwinding.

## 2. What unwinding does

A panic inside a **catch boundary** leaves every frame between the panic and
the boundary through the same cleanup as `?` and as an abortive perform
(docs/abortive-handlers.md 3.6): every live affine value is dropped once,
closure environments and pending temporaries are released, handler frames
pushed inside are popped. Live **linear** values run their type's unwind
cleanup (section 5), or are leaked and named in the report when the type has
none. A `Task.scope` left by unwinding first cancels its unjoined children
and joins them, as when its lambda returns `Err`, so no child outlives its
parent. At the boundary the panic becomes a value (section 6).

A panic with **no** catch boundary still aborts the process at once, with no
unwinding: there is nothing to keep alive, and the fast failure stays the
same as today. The runtime knows, per task and per thread, how many catch
boundaries are active.

Stack exhaustion stays fatal: it is detected in a signal handler, where no
frame can be left safely.

## 3. Mechanism: the abort word

Unwinding reuses E-ABORT-PROPAGATE's channel. A panic sets the thread's
abort word to `KUSH_PANIC_WORD` (1: never the address of a handle's payload
buffer, which every abortive activation uses) and returns; every caller that
may see a panic tests the word after the call and, when it is set, leaves
through its cleanup and returns. Abortive scopes compare the word with their
own buffer, so a panic passes through them like any other foreign abort.

- **Which calls are tested.** `suspend::mark_abort_calls` already wraps
  calls that may abort in `AbortCall { exits, propagates }`. With unwinding,
  every call (any function may panic, so no row rules one out) and every
  call to a runtime helper that can panic is wrapped with `propagates` (or, inside an
  abortive scope, with its exits too). A call that cannot panic costs
  nothing; one that can costs a load, a test and a branch (measured within
  noise for abortive calls).
- **Panic sites in generated code** (the few `abort()` sites of the
  lowering, and checked operations lowered inline) set the word and take the
  same exit: `cleanup_all` then return.
- **Panic sites in the C runtime.** About 120 `kush_panic()` calls. Each one
  is classified:
  - **recoverable** (a precondition on the program's values: an index, a
    byte value, a capacity, a refused allocation, invalid UTF-8): replaced by
    `KUSH_FAIL(value)`, which sets the word and returns a harmless value
    without touching the operands, so the generated caller's test leaves
    before using it;
  - **fatal** (the runtime's own invariants: a double free, a corrupted
    header, a broken task table): still abort, since unwinding over corrupted
    state is not safe.
  A runtime helper that calls another one that can fail checks the word and
  returns too.
- **The evaluator** (the MIR machine) runs the cleanup blocks the MIR
  builds, as native code does: a panic unwinds frame by frame to the next
  cleanup block, a task's entry or a `Task.catch`. The end-of-run ownership
  check stays strict.

## 4. Checker rules

The ownership pass checks an `AbortCall` that propagates like `?`: affine
values get drop flags. For the abort exits of declared operations it also
rejects pending linear values ("linear value is not consumed before an
abortive call"). Panic exits cannot reject them, or no function holding a
`File` could do arithmetic. Instead:

- a panic exit **records** the live linear values, and the backends run
  their unwind cleanup (section 5) instead of rejecting the program;
- an exit that may be a declared abortive operation keeps today's rule.

So the checker distinguishes "may panic" from "may abort with `F`" on each
`AbortCall` (a `panics: bool` beside `exits`), and only the second carries
the linear-value obligation.

Grades: a panic exit is a path on which an exact grade `@[1]` is not met.
Like linear values, those values are listed for the unwind cleanup, not
rejected.

## 5. Linear types: a cleanup for unwinding

A linear type may name a function the runtime calls on a live value of it
when a panic unwinds past it. Spelling (confirmed 2026-11-15), on the type:

```kush
#[linear(unwind = discard)]
pub struct File { fd: i64 }

fn discard(file: File) -> Unit ! {io} { let _ = close(file); }
```

- The function takes the value by move and returns `Unit`; it is in the same
  module as the type (it may read private fields). Its row may include `io`,
  `alloc` and `suspend` (a `Responder` answers 500, which writes to a
  socket), but not declared operations. Since FND-ROWS-PANIC (2026-11-24)
  `panic` is not an effect, so a cleanup may panic: that panic ends the
  cleanup and unwinding goes on, in both backends (`unwind_cleanup` in the
  evaluator, `kush_unwind_hold`/`restore` natively). A panic in an
  allocator release callback or an arena strategy aborts instead.
- Without `unwind = ...` the value is leaked, and the report printed with
  the panic names its type.
- std uses it for `std.file.File`, `std.net.Conn` and `Listener` (close the
  descriptor), and `std.web.Responder` (answer `500` unless it already
  started) and `Stream` (end the connection).

Values are cleaned up in reverse order of creation, as `?` drops them.

## 6. Catch boundaries

Two places stop a panic:

1. **A catch call** in a task or `main`:

   ```kush
   match Task.catch(fn() -> i64 ! {io} { risky() }) {
       Result.Ok(value) => value,
       Result.Err(panicked) => -1,
   }
   ```

   `Task.catch(f)` runs `f` in the calling task and returns `Result<T,
   Panic>`; `Panic` carries the panic's kind and source position. It is a call boundary, not a task, so it costs no
   stack and no spawn: `std.web` uses it around each handler instead of an
   isolated task.
2. **A thread body.** `Thread.join` of a thread whose body panicked reports
   it (today the process aborts), so a server per thread survives a
   panicking request the same way.

A task without a catch around the panic propagates it out of the task: its
join reports the panic to the parent, whose own `Task.join` site then panics
in turn, unless a catch is around it. This keeps "a panic is never silently
dropped".

`Task.catch` and propagation to the joiner were confirmed on 2026-11-15;
the fields of `Panic` and how `Thread.join` reports a panic are settled in
PANIC-UNWIND-USE.

## 7. Cost

- Calls that may panic: one load, test and branch each (the abort word is a
  thread-local global, as for abortive operations).
- Code size: every panic site gains a cleanup exit. The lowering already
  shares nothing between exits; if size grows too much, exits with the same
  live set can share one block (follow-up).
- Runtime helpers: a failing precondition returns instead of aborting; the
  normal path is unchanged.
- No unwind tables, no landing pads, no change to calling conventions, the
  LLVM translation or the bridge ABI.

## 8. As built

**PANIC-UNWIND-EVAL (2026-11-15).** The evaluator needed no marking: a
panic is still an `Err` diagnostic, and owned temporaries already live in
hidden frame slots. When a panic error leaves a function and a catch
boundary will stop it, the frame runs its normal cleanup (every active
slot, in reverse) before the error moves on; a `Task.scope` the panic leaves
cancels its unjoined children before its epilogue joins them. The boundary
is still WEB-PANIC-500's isolated task until `Task.catch` exists. The
end-of-run ownership check is strict again in the evaluator. Tests: the
`/owned` (owned locals, a vector, a pending temporary) and `/scoped` (a
waiting child task) handlers in `crates/kush/tests/web_server.rs`, which
must leave the heap empty. Live linear values are dropped like affine ones
for now; their unwind cleanup is PANIC-LINEAR-CLEANUP.

**PANIC-UNWIND-NATIVE (2026-11-15).** Simpler than section 3 planned: the
lowering already tracks every live value (`cleanup_all` works at any
point), so no checker marking was needed. In a program with a catch
boundary (`Executable::uses_unwinding`, set when `kush_sys_task_isolate` is
called; the runtime gets `-DKUSH_UNWIND`):

- `abort()` (every inline check: overflow, division, bounds, `panic()`)
  calls `kush_unwind_panic`, which aborts unless the current task is
  isolated and otherwise sets the panic word (1) and returns; the frame then
  drops its live values and returns.
- After every direct call, every call of a function value that may panic,
  handler and vector-callback calls, and the runtime helpers in
  `FAILING_RUNTIME`, generated code tests the word and leaves the same way.
- Those helpers' precondition failures use `KUSH_FAIL`: bytes and vector
  indexing, byte values and reserved capacity in `Bytes.push` (which frees
  the buffer moved into it), negative capacities, UTF-8 scalar access. A
  failing element store leaves the item with the caller's cleanup. So do a
  `Task.scope` nested too deep and a failed write in `print_*`. The other
  `kush_panic` sites abort the process even under a boundary: they check
  the runtime's own invariants (a double free, a corrupted header, the task
  table), or fail after an owner was moved into C code that cannot drop it
  (`Vec.reserve` with a negative count, the handler stack overflowing), or
  report memory exhaustion, which aborts as in Rust. WEB-PANIC-500's
  leaking recovery is gone, so the exit ownership check is always strict.
- In optimized builds an invalid byte in an inline `Bytes.push` goes to the
  runtime call, which frees the moved buffer, instead of the inline guard.
- `Task.scope` tests the word after its body: it clears the word, cancels
  and joins the children (other tasks run meanwhile), sets it again and
  unwinds.
- The isolated task's entry clears the word and finishes the task with its
  mark.

Programs without a boundary compile as before. With one, a 100-million-call
loop ran in the same time (0.38-0.39 s); every call site gains a load, a
compare and a branch, and an exit block. Tests: the panic cases of
`crates/kush/tests/web_server.rs` run natively too, with the strict exit
check, on Cranelift and LLVM.

**PANIC-LINEAR-CLEANUP (2026-11-15).** `#[linear(unwind = f)]` names a
function of the type's module taking the value by move and returning
`Unit`; the checker rejects a missing function or another signature
(`Executable::unwind_functions`, by layout). Such a layout counts as owned
for tracking, so a live value of it, and any value holding one (a
`Result<File, i64>`), is in a frame's cleanup. Natively its drop glue
calls `f` between `kush_unwind_hold` and `kush_unwind_restore`, which keep
the panic word clear while `f` runs (a panic inside `f` ends `f`, and
unwinding goes on). Normal paths never reach that glue: a linear value is
always consumed before its frame ends. The evaluator's frame cleanup drops
each value with its type (`drop_typed`), so it finds a linear value nested
in a record, an enum payload or a box and calls `f` on it, like the native
glue. std uses it for `std.file.File` and `std.net.Conn`/`Listener`
(close the descriptor), `std.web.Responder` (answer 500 with `Connection:
close`) and `Stream` (send nothing more; the client sees the body cut
off). Tests: `unwinding_closes_linear_resources` (five panicking handlers
holding an open file inside a `Result` leave the process's descriptor count
unchanged, natively and in the evaluator, run as its own process)
and `unwind_cleanups_are_checked` in `crates/kush/tests/web_server.rs`.

**PANIC-UNWIND-USE (2026-11-15).** `Task.catch(lambda)` is a `TaskScope`
with a `catch` shape: `Result<T, std.task.Panic>` (`Panic` is an empty
record, the message having gone to standard error). The checker finds
`std.result.Result` and `std.task.Panic` and turns on unwinding for the
program. Natively the catch counts itself (`kush_catch_enter`/`leave`, per
task, or per thread on an OS thread); after the body it clears a set panic
word, cancels and joins the children, and yields `Err`; a child's panic
that the scope epilogue raises is caught the same way. The evaluator keeps
a catch depth per task and turns a panic error into `Err` there.

When a panic unwinds (`kush_panic_unwinds`, the evaluator's `unwinding`):
on an OS thread and in any spawned task always, since the join raises it
again; in `main` only inside a catch. A task or thread whose body unwound is
marked panicked; `Task.join`/`Thread.join` (status 2) and the scope
epilogues raise it in the joiner with `kush_unwind_rethrow` (no second
message), which aborts when nothing can stop it. `web.serve` uses
`Task.catch` around each handler instead of an isolated task, and
`sys.task_isolate`/`sys.task_mark` are gone. Tests:
`crates/kush/tests/panic_catch.rs` (owned values, a box and a vector freed
on both backends; nested catches; checked arithmetic and `panic()`; a
child's panic at its join and at the scope epilogue, with a waiting
sibling cancelled; a thread's; an uncaught one still aborting) and the
server tests.

## 9. Order

1. PANIC-UNWIND-EVAL: the evaluator (the oracle) unwinds with exact cleanup.
2. PANIC-UNWIND-NATIVE: marking, runtime `KUSH_FAIL`, lowering, both
   native backends; differential tests against the evaluator, including
   allocation balance after caught panics.
3. PANIC-LINEAR-CLEANUP: `#[linear(unwind = f)]`, std's cleanups.
4. PANIC-UNWIND-USE: `Task.catch`, threads, `web.serve` on it; remove
   `sys.task_isolate` and the leak-tolerant exit check.
