# Tasks on handlers (design, E5)

Status: **accepted** with decisions T1-T5 (section 8, user, 2026-11-27).
Plan node FND-TASKS-ON-HANDLERS, steps TASKS-BENCH to TASKS-DELETE. Decision E5 of
[foundations-review.md](foundations-review.md) (user, 2026-11-24): tasks
(`Task.scope`, `spawn`, `yield`, `join`, `cancel`) move to std on top of
handlers, and `suspend` becomes a handled effect. This document says what that
needs, because today's handlers cannot carry it.

## 1. Today

Two mechanisms suspend a computation, and they share nothing.

**Tasks** ([async.md](async.md)) are stackful coroutines in the C runtime:

- `kush_task_*` in `runtime/kush.c` (19 entry points: spawn, yield, join,
  scope begin/end, cancel and its propagation, generations, handles) on
  `ucontext`, 256 KiB stacks with a guard page, one scheduler and one epoll
  reactor per OS thread.
- The evaluator runs one OS thread per task (`mir/machine/tasks.rs`, 735
  lines).
- The checker owns the rules in `executable/concurrency.rs` (862 lines),
  plus about 90 sites in `ownership.rs`: a `Task<T>` cannot escape its
  scope, `spawn` only lexically in a scope lambda, children may borrow
  views the scope captured from outside, linear results need explicit joins.
- Because a task has its own stack, **anything** can be live across a
  suspension: borrows, views, `return`/`?` after a yield, calls through
  function values and trait objects. std relies on that: `std.web` runs a
  task per connection, holding views and calling handler closures across
  `wait_ready`.

**Handlers** ([effect-handlers.md](effect-handlers.md)) are compiled by a
CPS / state-machine transform (`suspend.rs`, 4,122 lines, plus `implicit.rs`):

- A continuation is a closure over the values live at the perform.
- Hence the limits: no borrow across a perform (one narrow exception), no
  `return`/`?`/outer `break` after one, no capture through function values,
  trait objects, `Task.scope` or vector callbacks, and nested non-tail
  handlers. Every called function on the path needs a resumable entry.
- The token is linear and **cannot outlive the handler**: it cannot be
  stored in a value that leaves the handler clause.

A scheduler written as a handler must do exactly what the second list
forbids: keep the continuations of many suspended tasks in a queue and
resume them later, from another clause, with arbitrary code (and borrows)
live in each. So E5 cannot be "rewrite `Task.*` in std with today's
`handle`". It needs a handler whose continuation is a suspended **stack**.

## 2. The model

**Fiber handlers.** A third lowering of `handle`, next to tail-resumptive
and CPS:

```text
handle Suspend: Request -> Reply with fiber fn(request: Request, k: Resume<Reply, T>) -> T ! {..} {
    ...
} {
    body
}
```

- The body runs on its own stack (a fiber). Entering the `handle` creates
  the fiber and switches to it.
- `perform Suspend(r)` anywhere in the body's dynamic extent, through any
  call (function values and trait objects included), switches back to the
  handler's stack and calls the clause with `r` and `k`.
- `k: Resume<Reply, T>` is a first-class, **linear**, one-shot value: the
  suspended fiber. Unlike today's token it may be stored in a vector or a
  record, returned and passed on. It must eventually be consumed exactly
  once:
  - `Resume.resume(k, reply)` switches to the fiber. The resumer runs again
    when the fiber performs or finishes, and gets `Step.Performed(request, k2)`
    or `Step.Finished(t)`. This is the shallow form (as in OCaml's
    `Effect.Shallow` and WasmFX); a scheduler is a loop over it.
  - `Resume.discontinue(k)` unwinds the fiber with the panic machinery
    (docs/panic-unwinding.md): its frames free what they own, linear values
    run their unwind cleanup, and the stack is released. This is what
    cancelling a suspended task means.
- Nothing is restricted across a perform: it is a stack switch, so borrows,
  views, `return`, `?` and calls through values behave as across a call.
  This is the task semantics of today, generalized.

**Tasks in std.** With that, `std.task` holds the scheduler:

- `suspend` becomes the declared operation `Suspend` (keeping the row name
  `suspend`). `Task.yield`, `Task.join` and `sys.wait_ready` perform it with a
  request (`Yield`, `Join(id)`, `Wait(fd, events, deadline)`).
- `Task.scope(f)` and `Task.catch(f)` install the scheduler's handler, or
  join the innermost one, and run `f` as the root fiber.
- `Task.spawn(g)` performs `Spawn(g)`: the scheduler creates a fiber for
  `g`, keeps its `Resume` in the ready queue and returns a handle.
- The run queue, join waiters, cancellation bits and their propagation,
  generations and slot reuse, and the reactor are Kush code. The reactor is
  `epoll` and timer syscalls in `std.sys`.
- `main` and each OS thread get a root scheduler from the runtime prologue,
  so `main` can still `wait_ready` without a scope.

**What stays in the compiler.** The static rules that make tasks safe
(scope confinement of `Task<T>`, lexical spawn, borrowed captures from
outside the scope, linear results) are about lifetimes the type system
cannot express yet (section 1 of the review, lifetime-bounded closures). Two
options, decision T3:

- **T3-A (recommended):** keep `Task.scope`/`spawn`/`join`/`cancel` as
  checked surface forms whose code is std. The checker's rules stay; only
  the runtime moves.
- **T3-B:** a scope token with a lifetime (`Scope<'s>`, as Rust's
  `thread::scope`) and closures bounded by `'s`, all in std. This needs
  lifetime-bounded closures first and changes every program that uses
  tasks.

## 3. Why programs observe the same thing

- **Scheduling contract** (async.md rules 1-7): the std scheduler is the
  same FIFO ready queue and the same spawn, yield, join and scope order, so
  the deterministic interleaving is unchanged. The existing task tests
  (`task_*`, `web_reactor`, `linear_task_results`, threads) are the oracle.
- **Cancellation** stays cooperative: `Task.cancel` sets a bit and the task
  observes it at `yield`/`check_cancel`/`wait`. `discontinue` is used only
  for a fiber that can no longer be resumed (a scope abandoned by a panic),
  which today aborts or unwinds the same frames.
- **Handlers seen by a task** (D3 of one-handler-model.md): today a child
  inherits the innermost contiguous run of copyable frames at the spawn.
  Under E4 a declared operation is an implicit capability parameter, so a
  spawned closure captures the capabilities of its lexical context, which
  is the same set in every program that does not panic today. The rule
  becomes "a task sees the handlers its body captured", with no run-time
  "did not inherit" panic. Decision T4.
- **Panics** cross a fiber like a task today: an unwinding panic in a fiber
  finishes it; `join` re-raises it in the joiner.

## 4. What changes for users

- Nothing in the surface API under T3-A. Under T3-B, every `Task.scope`
  body takes a scope parameter.
- New: user code can write its own fiber handlers: generators that keep
  borrows across `yield`, actors, alternative schedulers, deterministic
  test schedulers. This is the gain E5 is for.
- `suspend` in rows is unchanged; a function that suspends still needs it,
  and a `handle Suspend` discharges it like any declared operation.

## 5. Representation

- A fiber is a stack (mmap, guard page, size as today's task stacks, pooled)
  plus a control block: saved registers, parent fiber, and the result or
  pending request slot.
- `Resume<A, T>` is one word, the control block address. Linear, not
  `Send` (a fiber never leaves its OS thread, as tasks today).
- Switching is the existing hand-written swap, not `ucontext`
  (`swapcontext` saves the signal mask with a syscall). A switch saves the
  callee-saved registers and the stack pointer: about ten instructions.
- The evaluator gets fibers for free: its call stacks are already explicit
  per task (`mir/machine.rs`), so a fiber is one more stack, and the
  thread-per-task model and its I/O buffering go away.

## 6. Lowering

- `handle ... with fiber fn` lowers to a runtime call `kush_fiber_new(entry,
  env)` and a first `resume`. The body becomes a closure (as `Task.scope`
  lambdas are today), so no CPS transform runs for it.
- `perform Op` for an operation whose capability is a fiber handler is
  `kush_fiber_suspend(request)`: it stores the request and switches to the
  parent. The capability (E4) says which kind of handler it is, so the
  other two lowerings are unaffected.
- `Resume.resume`/`discontinue` are runtime calls. `discontinue` sets the
  fiber's panic word and resumes it, so the unwinding that exists today
  does the rest.
- Stack overflow in a fiber hits its guard page, as tasks today.

## 7. Steps (plan sub-nodes)

1. **TASKS-BENCH.** A task benchmark before anything moves: yield ping-pong
   between two tasks, spawn and join of 100k tasks, a reactor echo over a
   socket pair. It sets the budget (decision T5).
2. **FIBER-RUNTIME.** `kush_fiber_*` in the C runtime (new, switch,
   suspend, resume, discontinue, pooled stacks), and evaluator fibers.
   Unit tests in C and through the evaluator.
3. **FIBER-HANDLERS.** Surface (`with fiber fn`, `Resume<A, T>`, `Step`),
   checker rules (linear `Resume`, not across threads, no fiber perform
   across a thread boundary), MIR and native lowering, docs in
   effect-handlers.md and the reference chapter on effects, with
   `kush reject` examples for the limits.
4. **STD-SCHEDULER.** `std.task` scheduler, cancellation propagation, slot
   generations, `std.sys` epoll and timers, reactor. Tested against the
   C runtime with both in the tree.
5. **TASKS-SWITCH.** `Task.*` and `suspend` go through std; the existing task
   tests must pass unchanged on both backends. Benchmarks against step 1.
6. **TASKS-DELETE.** Remove `kush_task_*`, the evaluator's task threads, and
   the inheritance rule of D3 (replaced per T4).
7. Later, if T3-B: lifetime-bounded scope tokens, then the checker's task
   rules move to types.

Steps 1 and 2 are useful whatever the decisions below. Step 3 is the
language change.

## 8. Decisions (user, 2026-11-27)

Each recommendation below was accepted: T1 fibers, T2 shallow resumption
for fiber handlers, T3-A, T4 captured handlers, T5 the budget as stated.

- **T1, mechanism.** Fiber handlers: a handled body on its own stack, a
  first-class linear `Resume`. The alternative, extending the CPS transform
  until a scheduler fits, would have to lift every limit in section 1
  (borrows, `return` after a perform, performs through values, tokens
  stored in data), and would still copy live values at each switch.
  Recommended: fibers.
- **T2, continuation form.** Shallow (`resume` returns
  `Step.Performed(request, k)` or `Step.Finished(t)` to the resumer) or deep
  (the clause is reinstalled around the resumed fiber, as Kush handlers
  are today). A scheduler is a loop in the shallow form and needs tail
  calls in the deep form. Recommended: shallow for fiber handlers only;
  the other two lowerings stay deep.
- **T3, where task safety lives.** T3-A (checked surface forms, std code)
  now, T3-B (scope tokens with lifetimes) after lifetime-bounded closures.
  Recommended: T3-A.
- **T4, handlers in tasks.** A task sees the handlers its body captured
  (capabilities, E4), replacing D3's run-time inheritance. Only programs
  that panic today with "did not inherit" change: they are rejected at
  compile time instead. Recommended: yes.
- **T5, cost budget.** Yield and join within 10% of today's runtime, spawn
  and join within 20%, the web reactor benchmark within 5%. Deleting the C
  scheduler waits until the budget is met.
