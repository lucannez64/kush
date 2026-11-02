# Structured async and cooperative cancellation

Status: implemented initial direct-style task system for the executable subset.
This is a usable cooperative runtime, not a claim of the full v0.1 async design
or of a formal soundness proof. The native backend executes compiled Cranelift
function bodies; the reference evaluator has its own scheduler and never runs
compiled code.

## Surface API

```rust
use std.task.TaskExit;

Task.scope(fn() -> T ! {e} { ... }) -> T ! {alloc, panic, suspend, e}
Task.spawn(fn() -> T ! {e} { ... })  -> Task<T> ! {alloc, panic, suspend, e}
Task.yield()                        -> Bool ! {suspend}       // true: cancel requested
Task.join(task: Task<T>)            -> TaskExit<T> ! {suspend}
Task.cancel(&task: &Task<T>)        -> Unit ! {}
Task.check_cancel()                 -> Bool ! {}
```

`Task.scope` takes an inline, explicitly typed lambda. It runs that lambda once in
the current task and owns a fresh scope frame. `Task.spawn` is only legal
lexically inside such a scope lambda; ordinary functions and nested function
values cannot spawn. Its body must be a statically known named function or an
inline lambda so that cancellation cleanup can be checked. This is checked
statically, not only at runtime.

There is no `async fn`, `await`, or implicit spawning. A suspending call uses
ordinary call syntax. `Task.yield`, `Task.join`, and `Task.scope` require the
`suspend` effect. `Task.spawn` additionally requires `alloc` and `panic` because
it acquires a task stack/control block and allocates the task result buffer.
`Task.cancel` and `Task.check_cancel` do not themselves suspend.

`Task<T>` is an opaque, affine, one-word handle. It cannot be stored in a record,
enum payload, array, `Box`, `Vec`, or union, returned from a function, or captured
by a function value. Those restrictions prevent a child handle from escaping its
scope through data or a generic return. A handle may be a local, a function
parameter, or a direct argument to `Task.join`/`Task.cancel`.

A child task result may be a record with borrowed slice fields when those leaves
derive from storage the scope body captured from outside the scope. `Task.join`
carries the per-field provenance through the conventional `TaskExit<T>` value;
matching `Completed(record)` keeps each loan checked until the record is
consumed or dropped. A borrowed `TaskExit<T>` is lexical to the joining scope
and cannot cross a function or callable boundary. If a cancelled child has
already computed a result, that value is dropped in the worker: owned metadata
is freed exactly once and borrowed descriptors never free caller storage.

`TaskExit<T>` is the conventional enum required by `Task.join`:

```rust
enum TaskExit<T> { Completed(T), Cancelled }
```

`Task.join` consumes the handle. A task that returned normally yields
`Completed(value)`. If the body completed with an owning or intrinsically linear
payload under a `@[1]` contract, the payload is transferred as `Completed` even
when a cancellation request was observed; the handle is linear and must be
joined explicitly. An affine (ungraded) owning payload for which cancellation
was requested yields `Cancelled` and is dropped exactly once. A copyable `@[1]`
task result is rejected. A task body that panics aborts the process, as
elsewhere in the current panic policy. See
[linear task results and cancellation cleanup](linear-task-results.md).

An expected `Task<U>` type or explicit `Task.spawn::<U>(...)` may widen the
callable's result to a supertype. Representation changes, such as injecting an
integer or owner into a union, use a checked callable adapter before the result
is stored. The task result buffer always uses the adapted result layout.

## Scheduling contract

The deterministic reference contract and the native runtime use the same rules:

1. The root task is `main`. It runs first.
2. `Task.spawn` evaluates the closure in the parent, transfers the owned closure
   (including its environment) to the new task, appends the new task to the tail
   of the ready queue, and returns its handle immediately. The parent continues;
   it does not switch to the child at spawn.
3. A task runs until it calls `Task.yield`, blocks in `Task.join`, finishes, or
   its scope completes. There is no preemption.
4. `Task.yield` appends the running task to the tail of the ready queue and runs
   the task at the head. With no other ready task the same task resumes.
5. `Task.join` blocks the caller until the target finishes. When the target
   finishes, the waiter is appended to the tail of the ready queue. Other ready
   tasks may run first.
6. `Task.scope` joins every child spawned in its frame that was not already
   joined, in spawn order, before the scope expression returns. This happens on
   normal completion and on an early `return`/`?` from the scope lambda, because
   the lambda is a separate function and the scope epilogue always runs.
   If the scope lambda returns the conventional `Result<T, E>` and its result is
   `Err`, the scope first requests cancellation of every unjoined child, then
   joins them. This is the explicit fallible-scope policy; a non-`Result` scope
   result simply joins and returns.
7. A joined task's result buffer, stack, and control block are released exactly
   once. An ignored handle is still joined at scope exit; its result is discarded
   after cleanup. Dropping a handle never blocks or suspends.

The reference evaluator implements these rules with one OS thread per task and
strict handoff through scheduler channels: only one task evaluates at a time, and
the scheduler chooses the next runnable task. The native runtime uses stackful
coroutines (`ucontext` in the trusted C shim) on one OS thread. Both are
cooperative and deterministic for the same program; they do not claim parallel
execution or cross-thread `Send`/`Sync` semantics.

## Cancellation

Cancellation is cooperative and explicit:

- `Task.cancel(&t)` sets a request bit. It does not stop, preempt, or destroy a
  task, and it does not itself suspend.
- `Task.check_cancel()` reads the bit.
- `Task.yield()` returns the bit after resuming, so a loop can react at every
  yield point.
- A cancellation request is observed by the task's own code. A noncooperative
  task may delay its scope indefinitely. There is no bounded shutdown time and
  no arbitrary thread termination.
- Cancellation is never delivered while a language frame is paused. A task
  suspended in `yield` or `join` is resumed first; only then can its code observe
  the request. Consequently the runtime never frees a suspended task stack
  containing live owners and never has to unwind an arbitrary paused frame.
- When a task observes cancellation at a checkpoint and returns or propagates
  `?`, ordinary lexical cleanup runs exactly once for every exited frame. The
  ownership checker already requires every linear `#[linear]`/`@[1]` obligation
  to be consumed on that exit path. A completed result that carries such an
  obligation is transferred to the joiner as `Completed` rather than discarded;
  handles for such tasks are linear and must be joined explicitly.
- Automatic destruction never suspends. Task handles are affine; dropping one is
  a no-op at the runtime level. Scope completion is an explicit control phase
  (`Task.scope` epilogue), not a suspending destructor.

This policy allows owned and borrowed values to live across suspension: the task
stack is retained until the task reaches a normal exit. Shared and exclusive
slice views, including checked `Slice.split_at_mut` children, and borrowed
records with shared or exclusive fields may therefore be held across `Task.yield`/`Task.join`, and a
checked borrowed return may cross a same-task suspension point. A scoped
borrowed-capture closure may also be held and called across same-task suspension.
Borrowed records and borrowed-capture closures still cannot be captured by a
task body.

### Scoped borrowing

Because a scope joins every child before it returns, scope bodies and spawned
children may borrow slice views:

- A `Task.scope` body may capture shared or exclusive views, like an
  immediately called closure. The loans last until the scope expression,
  including its final join, completes.
- A spawned child may capture a view only if every source is a view the scope
  body captured from outside the scope, or a view derived from one (sub-slices
  and `Slice.split_at_mut` halves). The scope body's own locals and owned
  captures are freed before the final join, so lending them is rejected.
- After a spawn, each lent view stays borrowed for the rest of the scope body,
  since the child may run at any later suspension point. The parent may keep
  reading a shared view it lent, may use a split half it did not lend, but
  cannot write through, reborrow exclusively, or reuse the parent of a lent
  view. Overlapping exclusive views cannot go to two children.
- Joining a child early does not release its loans before the scope ends
  (conservative).

```rust
let (first, second) = Slice.split_at_mut(output, 1);
Task.spawn(fn() -> Unit ! {panic} { Slice.set(first, 0, sum(&input[0..3])); });
Task.spawn(fn() -> Unit ! {panic} { Slice.set(second, 0, sum(&input[3..6])); });
```

See [task-borrows.kush](../examples/task-borrows.kush). Execution is still
cooperative on one OS thread; this is not a claim of parallel data-race
freedom across threads. Linear captures are therefore allowed, and a cancelled task must return through
a checked path that consumes or transfers them. A task result type may carry an
owning/linear obligation when the handle is linear and explicitly joined; a
copyable must-use result stays rejected because `TaskExit.Cancelled` has no
place to deliver it.

If a future implementation adds forced cancellation delivery, it must add
per-frame unwind metadata or masking; this document does not claim that feature.

## Task I/O

The initial task system does not add nonblocking standard-stream operations.
`IO.read_all`/`IO.write` remain synchronous and may block the whole OS thread, so
the native scheduler does not claim nonblocking I/O. Task bodies may use the
existing `io` effect (for example `print_i64`) because the runtime is a single
OS thread and interleaving is still cooperative and deterministic. A blocking
read stalls every task; this is documented, not hidden.

The public reference `evaluate_with_io` API is unchanged. For a task program the
reference evaluator reads host input to EOF up front and buffers program output,
because its task threads must not require non-`Send` I/O trait objects. That mode
is not interactive streaming; it preserves the deterministic empty-input
behavior and ordinary finite-input tests.

## Ownership, effects, and allocation

- `suspend` is a normal effect bit and composes by row union. It propagates
  through direct and indirect calls, function values, and effect-polymorphic
  rows.
- `#[nosuspend]` rejects a declared `suspend` effect and rejects an
  unconstrained effect-row variable in its signature, because that variable could
  be specialized with `suspend`. It is a static whole-body contract, independent
  of optimization.
- `Task.spawn` transfers the owned once callable exactly once. Capturing
  closures allocate their environment and require `alloc`/`panic`; noncapturing
  function pointers are adapted to the once ABI without allocation.
- Task stacks and control blocks are charged as allocations in both backends;
  the native backend also charges each task result buffer. The reference backend
  charges one control unit and one stack unit per task and releases them when the
  handle is joined; it does not count the host OS thread stack byte-for-byte.
  Native stacks use a guard page so exhaustion faults instead of corrupting
  adjacent heap. `--stats` keeps the existing stable line and normal exit remains
  balanced (`allocations == deallocations`).
- `Vec.map_in_place` fusion only accepts callbacks whose effect row is exactly
  empty. A suspending callback is never fused as pure.

## Current limits

- Single OS thread, no parallelism, no cross-thread handles, no atomics or
  networking.
- Cancellation is cooperative; no masking regions or cancellation handlers yet.
- No nonblocking stream API; blocking I/O may stall the scheduler.
- Task bodies may return owning/linear results only through explicit `@[1]` (or
  intrinsically linear) contracts; those handles are linear and must be joined.
  Copyable must-use task results remain rejected. Handles still cannot escape
  their scope through data.
- Fixed native limits: 255 spawned tasks per program execution (joined task IDs
  are not reused), 16 nested scopes per task, 64 children per
  scope frame, 256 KiB task stacks. Exceeding a limit panics rather than
  corrupting memory.
- The ABI and the exact scheduling implementation are private and unstable.
