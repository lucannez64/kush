# Linear task results and cancellation cleanup

Status: implemented for the executable subset and both backends. Task bodies may
now return an owning or intrinsically linear payload under an explicit `@[1]`
contract, and cancellation never silently discards a completed payload that
carries such an obligation.

## Contract

```kush
use std.task.TaskExit;

fn make() -> Box<i64> @[1] ! {alloc, panic} { Box.new(42) }

fn main() -> i64 ! {alloc, panic, suspend} {
    Task.scope(fn() -> i64 ! {alloc, panic, suspend} {
        let task: Task<Box<i64>> = Task.spawn(make);
        match Task.join(task) {
            TaskExit.Completed(b) => Box.take(b),
            TaskExit.Cancelled => 0,
        }
    })
}
```

- `Task.spawn` and `Task.scope` accept an owning/linear result when the body
  returns it through `@[1]` or when the type is intrinsically `#[linear]`.
- The resulting handle is linear: it must be joined on every normal path. An
  ignored handle, a wildcard binding, or an unjoined local at scope exit is
  rejected by the ownership pass. Scope-end auto-join therefore cannot discard
  the payload.
- `Task.join` produces `TaskExit<T>`. When `T` carries the obligation, the
  completed arm's payload is linear and must be consumed; the cancelled arm has
  no payload.
- A copyable `@[1]` task result carries a must-join/must-use obligation: the
  handle is linear, joining produces a must-use `TaskExit<T>`, and a joined
  exit must be matched or observed. Cancellation delivers a completed copyable
  payload as `Completed(payload)` so the observation is never lost. The
  obligation is tracked by the grade pass in the same way as any other copyable
  exactly-use result, so it survives `let`, blocks, branches, match arms, and
  loop exits.
- `Task.scope` itself runs in the current task, so its result may carry a linear
  or copyable must-use obligation directly; the enclosing result rules apply.

## Cancellation policy

Cancellation remains cooperative and explicit. The body only leaves through a
normal return/`?` path after whatever checkpoints it chooses. Ownership already
requires every captured or local linear resource to be consumed or transferred
on that exit path.

When a cancellation request is set and the body still completes with an owning,
intrinsically linear, or copyable must-use payload, the runtime returns
`Completed(payload)` instead of `Cancelled`. The joiner must consume or observe
the payload. This is the explicit cleanup/transfer contract; no obligation is
dropped merely because a cancellation bit was set.

```kush
fn make() -> Box<i64> @[1] ! {alloc, panic, suspend} {
    let cancelled = Task.yield();
    Box.new(if cancelled { 7 } else { 9 })
}
// cancel before join: join yields Completed(Box.new(7)), not Cancelled
```

The same rule preserves a linear capture that the body returns:

```kush
let b = Box.new(11);
let task: Task<Box<i64>> = Task.spawn(fn() -> Box<i64> @[1] ! {alloc, panic, suspend} {
    let _cancelled = Task.yield();
    b
});
Task.cancel(&task);
// join -> Completed(b); the caller consumes it
```

Affine (ungraded) owning results keep the previous behaviour: a cancellation
request after the body returns turns the outcome into `Cancelled` and the
affine payload is dropped exactly once. Existing tests for that path remain
unchanged.

## Runtime notes

- Reference evaluator: the scheduler carries a `preserve` flag with each spawned
  task and returns `Completed(value, true)` when cancellation is set. The scope
  epilogue rejects an unjoined preserved result defensively; the static checker
  makes that path unreachable.
- Native runtime: `kush_task_spawn` stores the flag, the entry trampoline marks
  a preserved task completed, and `kush_task_join` refuses a transfer-less
  (`out == NULL`) join of a preserved task. The same static linear-handle rule
  makes that a defensive check only.
- Both backends keep allocation/deallocation balance, deterministic scheduling,
  and one OS thread. Linear task payloads are ordinary values; no new tag or
  runtime check is added to `Task<T>`.
- Cancellation delivery is still cooperative. After a forced-cancellation
  implementation is added, it must first define per-frame unwind metadata or
  masking; this document does not claim forced unwinding.

## Tests

`crates/kush/tests/linear_tasks.rs` covers normal join transfer, cancellation
transfer (owning and copyable), linear captures, rejected ignored/unjoined
handles, linear scope results, copyable must-use scope results, and must-use
join results in both backends. `crates/kush/tests/async.rs` and
`linear_resources.rs` retain the affine cancellation and linear-result
boundaries.
