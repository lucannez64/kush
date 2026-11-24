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

fn worker(id: i64) -> i64 ! {io, panic, suspend} {
    print_i64(id * 10 + 1);
    Task.yield();
    print_i64(id * 10 + 2);
    id
}

fn main() -> Unit ! {io, alloc, panic, suspend} {
    Task.scope(fn() -> Unit ! {io, alloc, panic, suspend} {
        let a: Task<i64> = Task.spawn(fn() -> i64 ! {io, panic, suspend} { worker(1) });
        let b: Task<i64> = Task.spawn(fn() -> i64 ! {io, panic, suspend} { worker(2) });
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

## Threads

`Thread.scope` / `Thread.spawn` / `Thread.join` have the shape of the task
API, but each child runs on its own OS thread. A thread body captures values
by move and slice views by borrow; the loans last until it is joined.

```kush eval
fn part(v: &[i64], from: i64, to: i64) -> i64 ! {panic} {
    let mut sum = 0;
    let mut i = from;
    while i < to { sum = sum + v.get(i); i = i + 1; }
    sum
}

fn main() -> Unit ! {io, alloc, panic} {
    let data: [i64; 4] = [1, 2, 3, 4];
    let v = &data[..];
    let total = Thread.scope(fn() -> i64 ! {alloc, panic} {
        let a = Thread.spawn(fn() -> i64 ! {panic} { part(v, 0, 2) });
        let b = Thread.spawn(fn() -> i64 ! {panic} { part(v, 2, 4) });
        Thread.join(a) + Thread.join(b)
    });
    print_i64(total);
}
```

```output
10
```

A thread body cannot capture arenas, allocator contexts, closures or trait
objects, and starts with an empty handler stack. Shared mutable state goes
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
fn bump(c: &[Atomic]) -> Unit ! {panic} { Atomic.fetch_add(c, 0, 1); }

fn main() -> Unit ! {io, alloc, panic} {
    let mut cells: Vec<Atomic> = Vec.with_capacity(1);
    cells = Vec.push(cells, Atomic.new(0));
    let c: &[Atomic] = &cells[..];
    Thread.scope(fn() -> Unit ! {alloc, panic} {
        Thread.spawn(fn() -> Unit ! {panic} { bump(c); });
        Thread.spawn(fn() -> Unit ! {panic} { bump(c); });
    });
    print_i64(Atomic.load(c, 0));
}
```

```output
2
```
