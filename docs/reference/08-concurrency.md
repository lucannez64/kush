# 8. Concurrency

Planned change (decided, FND-TASKS-ON-HANDLERS): tasks move to a std library
built on effect handlers, and `suspend` becomes a handled effect.

## Structured tasks

Tasks are cooperative and run on one OS thread, with direct-style code: a
suspending call is an ordinary call whose row includes `suspend`. There is
no `async`/`await`.

| Call | Result | Effects |
| --- | --- | --- |
| `Task.scope(fn() -> T ! {e} { ... })` | `T`, after every child has finished | `alloc, panic, suspend, e` |
| `Task.spawn(fn() -> T ! {e} { ... })` | `Task<T>` | `alloc, panic, suspend, e` |
| `Task.yield()` | `Bool`: `true` if cancellation was requested | `suspend` |
| `Task.join(task)` | `TaskExit<T>` (`Completed(T)` or `Cancelled`) | `suspend` |
| `Task.cancel(&task)` | `Unit`: requests cancellation | none |
| `Task.check_cancel()` | `Bool` | none |
| `Task.catch(fn() -> T ! {...} { ... })` | `Result<T, Panic>` | `alloc, panic, suspend` |

`Task.spawn` is legal only lexically inside a `Task.scope` lambda. A
`Task<T>` handle is affine and cannot be stored, returned or captured, so no
task outlives its scope. Cancellation is cooperative: a task sees it at
`Task.yield` or `Task.check_cancel` and decides how to stop.

```kush eval
use std.task.TaskExit;

fn worker(id: i64) -> i64 ! {io, suspend} {
    print_i64(id * 10 + 1);
    Task.yield();
    print_i64(id * 10 + 2);
    id
}

fn main() -> Unit ! {io, alloc, suspend} {
    Task.scope(fn() -> Unit ! {io, alloc, suspend} {
        let a: Task<i64> = Task.spawn(fn() -> i64 ! {io, suspend} { worker(1) });
        let b: Task<i64> = Task.spawn(fn() -> i64 ! {io, suspend} { worker(2) });
        match Task.join(a) {
            TaskExit.Completed(v) => print_i64(v),
            TaskExit.Cancelled => print_i64(-1),
        }
        match Task.join(b) {
            TaskExit.Completed(v) => print_i64(v),
            TaskExit.Cancelled => print_i64(-2),
        }
    })
}
```

```output
11
21
12
22
1
2
```

A spawned task may borrow slice views and borrowed records that its scope
captured from outside the scope; the loans last until the scope ends. A
child's linear or owning result must be joined explicitly.

`Task.catch` makes panics unwind to it, freeing owned values and running
`#[linear(unwind = f)]` cleanups on the way; without a catch, a panic aborts
the process.

### Task I/O

`std.sys.wait_ready`, `std.net` (`Listener`, `Conn`) and `std.time.wait_ms`
suspend only the calling task on an epoll reactor. Other I/O (`std.io`,
`std.fs`, `print_*`) blocks the whole thread.

## Fibers

A fiber is a body that runs on its own stack and can stop in the middle of
any call, then go on later. `Fiber.new::<Op>(body)` makes one; `Op` is a
declared operation (`effect Op: A -> R;`). A `perform Op(a)` anywhere in the
body, including in functions it calls, suspends the fiber and hands `a` to
whoever resumed it.

| Call | Result | Effects |
| --- | --- | --- |
| `Fiber.new::<Op>(fn() -> T ! {Op, e} { ... })` | `Fiber<A, R, once fn() -> T ! {e}>`, not started | `alloc` |
| `Fiber.start(&mut f)` | `FiberStep<A, T>` | `e` |
| `Fiber.resume(&mut f, reply)` | `FiberStep<A, T>`; `reply: R` is the perform's result | `e` |

`std.fiber.FiberStep<A, T>` is `Performed(A)` when the body suspended and
`Finished(T)` when it returned. The resumer loops over the steps:

```kush eval
use std.fiber.FiberStep;

effect Emit: i64 -> i64;

fn count(limit: i64) -> i64 ! {Emit} {
    let mut i = 0;
    let mut total = 0;
    while i < limit {
        total = total + perform Emit(i * 10);
        i = i + 1;
    }
    total
}

fn main() -> Unit ! {io, alloc} {
    let mut f = Fiber.new::<Emit>(fn() -> i64 ! {Emit} { count(3) });
    let mut step = Fiber.start(&mut f);
    let mut done = false;
    while !done {
        match step {
            FiberStep.Performed(request) => {
                print_i64(request);
                step = Fiber.resume(&mut f, request + 1);
            },
            FiberStep.Finished(total) => {
                print_i64(total);
                done = true;
            },
        }
    }
}
```

```output
0
10
20
33
```

A `Fiber` is an owned value: it may be moved, stored in a `Vec` or a record,
and resumed from there, also by another task of the same OS thread. A thread
body cannot capture or return one. Dropping a fiber that has not finished unwinds it as
a panic would, so its frames free what they own; a fiber that never started
has its body dropped. A panic inside a fiber unwinds to the fiber's entry and
is raised again in the code that resumed it. A fiber may perform `suspend`
(`Task.yield`, `Task.join`, task I/O) between its suspensions; that switches
tasks as it would outside the fiber.

Resuming a fiber that has finished panics. In `kush eval`, dropping a fiber
that is suspended stops with an "unsupported" error; native programs unwind
it.

The operation is named explicitly:

```kush reject
effect Emit: i64 -> i64;
fn main() -> Unit ! {alloc} { let _f = Fiber.new(fn() -> i64 ! {Emit} { 1 }); }
// error: Fiber.new names the operation its body suspends with
```

The body may perform no other declared operation, since the handler of that
operation could end before the fiber is resumed:

```kush reject
effect Emit: i64 -> i64;
effect Other: i64 -> i64;
fn main() -> Unit ! {alloc} {
    let _f = Fiber.new::<Emit>(fn() -> i64 ! {Emit, Other} { perform Other(1) });
}
// error: a fiber's body may perform only 'Emit' among declared operations
```

A fiber may outlive the frame that made it, so its body captures no borrows,
and its types hold none:

```kush reject
effect Emit: i64 -> i64;
fn main() -> Unit ! {alloc} {
    let values: [i64; 2] = [1, 2];
    let view = &values[..];
    let _f = Fiber.new::<Emit>(fn() -> i64 ! {Emit} { Slice.len(view) });
}
// error: a fiber's body cannot capture
```

An abortive operation (one whose result is `Never`) cannot suspend a fiber:

```kush reject
effect Stop: i64 -> Never;
fn main() -> Unit ! {alloc} { let _f = Fiber.new::<Stop>(fn() -> i64 ! {Stop} { 1 }); }
// error: the abortive operation 'Stop' cannot suspend a fiber
```

### A scheduler on fibers: `std.sched`

`std.sched` is a task scheduler written in Kush on fibers, with the
scheduling rules of `Task`: one FIFO ready queue, `spawn` queues the new task
and the parent goes on, `yield_now` queues the running task, `join` waits
until the target finishes. A task is a `std.sched.Job`, a fiber whose body
performs `Sched` and has the row `{Sched, io, alloc}`; its result is an
`i64`. `sched.run(root)` runs the tasks until none is ready and returns the
root's result.

```kush eval
use std.sched;
use std.sched.Sched;

fn worker(id: i64) -> i64 ! {io, Sched} {
    print_i64(id * 10 + 1);
    sched.yield_now();
    print_i64(id * 10 + 2);
    id
}

fn main() -> Unit ! {io, alloc} {
    let root = sched.run(Fiber.new::<Sched>(fn() -> i64 ! {Sched, io, alloc} {
        let a = sched.spawn(Fiber.new::<Sched>(fn() -> i64 ! {Sched, io, alloc} { worker(1) }));
        let b = sched.spawn(Fiber.new::<Sched>(fn() -> i64 ! {Sched, io, alloc} { worker(2) }));
        sched.join(a) + sched.join(b)
    }));
    print_i64(root);
}
```

```output
11
21
12
22
3
```

A handle is joined once, from another task; a bad join panics. A task that
yields inside a fiber of its own (a generator it runs) cannot reach the
scheduler: that fiber's body performs only its own operation. Cancellation,
I/O waits and the panic of a task raised at its join are not in `std.sched`
yet; the built-in `Task` has them.

## Threads

`Thread.scope` / `Thread.spawn` / `Thread.join` have the shape of the task
API, but each child runs on its own OS thread. A thread body captures values
by move and slice views by borrow; the loans last until it is joined.

```kush eval
fn part(v: &[i64], from: i64, to: i64) -> i64 ! {} {
    let mut sum = 0;
    let mut i = from;
    while i < to { sum = sum + v.get(i); i = i + 1; }
    sum
}

fn main() -> Unit ! {io, alloc} {
    let data: [i64; 4] = [1, 2, 3, 4];
    let v = &data[..];
    let total = Thread.scope(fn() -> i64 ! {alloc} {
        let a = Thread.spawn(fn() -> i64 ! {} { part(v, 0, 2) });
        let b = Thread.spawn(fn() -> i64 ! {} { part(v, 2, 4) });
        Thread.join(a) + Thread.join(b)
    });
    print_i64(total);
}
```

```output
10
```

A thread body cannot capture arenas, allocator contexts, closures, trait
objects or fibers, cannot return a fiber, and starts with an empty handler stack. Shared mutable state goes
through atomics or channels, shared as views `&[Atomic]` / `&[Channel<T>]`:

| Operation | Result |
| --- | --- |
| `Atomic.new(v)`, `Atomic.value(a)` | make a cell / consume it |
| `Atomic.load(view, i)`, `Atomic.store(view, i, v)` | read / write |
| `Atomic.fetch_add(view, i, v)`, `Atomic.swap(view, i, v)` | previous value |
| `Atomic.compare_exchange(view, i, expected, new)` | `Bool` |
| `Channel.new(capacity)` | a bounded channel of plain-data messages |
| `Channel.send(view, i, m)`, `Channel.recv(view, i)`, `Channel.close(view, i)` | blocking send; `Option` receive; close |

Atomics are sequentially consistent. Channel messages are plain data
(scalars and records of scalars) in this version.

```kush eval
fn bump(c: &[Atomic]) -> Unit ! {} { Atomic.fetch_add(c, 0, 1); }

fn main() -> Unit ! {io, alloc} {
    let mut cells: Vec<Atomic> = Vec.with_capacity(1);
    cells = Vec.push(cells, Atomic.new(0));
    let c: &[Atomic] = &cells[..];
    Thread.scope(fn() -> Unit ! {alloc} {
        Thread.spawn(fn() -> Unit ! {} { bump(c); });
        Thread.spawn(fn() -> Unit ! {} { bump(c); });
    });
    print_i64(Atomic.load(c, 0));
}
```

```output
2
```
