# Parallel threads

Status: THREAD-SCOPE and THREAD-ATOMICS implemented 2026-11-06 (design
approved by the user); channels (THREAD-CHANNELS) follow. Tests:
`crates/kush/tests/threads.rs`.

```kush
fn part(v: &[i64], from: i64, to: i64) -> i64 ! {panic} { .. }

fn sum(v: &[i64]) -> i64 ! {alloc, panic} {
    Thread.scope(fn() -> i64 ! {alloc, panic} {
        let a = Thread.spawn(fn() -> i64 ! {panic} { part(v, 0, 500) });
        let b = Thread.spawn(fn() -> i64 ! {panic} { part(v, 500, 1000) });
        Thread.join(a) + Thread.join(b)
    })
}
```

`Thread.scope`, `Thread.spawn` and `Thread.join` have the shape of the
cooperative task API ([async.md](async.md)), but every child runs on its own
OS thread, in parallel with its parent and siblings. Cooperative tasks are
unchanged.

- **Structure.** `Thread.spawn` is legal only lexically inside a
  `Thread.scope` lambda (not a `Task.scope` one, and `Task.spawn` not in a
  `Thread.scope`). It returns a `Thread<T>` handle with the rules of
  `Task<T>`: affine, never stored, captured, returned or put in a union.
  `Thread.join(h)` waits for the thread and yields its `T` (threads are not
  cancelled). The scope's epilogue joins every thread not joined yet and
  drops its result; a linear result must be joined explicitly.
- **Effects.** `Thread.scope` and `Thread.spawn` need `{alloc, panic}`. A
  thread body may only have `{io, alloc, panic}`: it cannot suspend (no
  cooperative tasks inside threads in this version) and must handle any
  declared operation inside itself, since a thread starts with an empty
  handler stack. A panic in a thread ends the process.
- **Sharing (moves and borrows).** A thread body captures values by move
  and borrowed views (`&[T]`, `&mut [T]`, `&str`) of its parent's data. The
  ownership rules of scoped tasks keep every loan until the child is joined:
  the parent cannot write what a thread reads, an exclusive view goes to one
  thread only, and disjoint halves from `Slice.split_at_mut` may go to
  different threads. Without atomics or channels there is no other shared
  mutable state, so a program's result does not depend on the schedule.
- **Not shareable.** A thread body cannot capture arenas, user allocator
  contexts and their boxes or vectors, closures or trait objects: they can
  reach allocator or environment state that is not thread-safe.

## Atomics (THREAD-ATOMICS)

```kush
fn bump(c: &[Atomic]) -> Unit ! {panic} { Atomic.fetch_add(c, 0, 1); }

let mut cells: Vec<Atomic> = Vec.with_capacity(1);
cells = Vec.push(cells, Atomic.new(0));
let c: &[Atomic] = &cells[..];
Thread.scope(fn() -> Unit ! {alloc, panic} {
    Thread.spawn(fn() -> Unit ! {panic} { bump(c); });
    Thread.spawn(fn() -> Unit ! {panic} { bump(c); });
});
Atomic.load(c, 0) // 2
```

`Atomic` is a one-word integer cell. Atomics live in arrays, vectors or
records and are shared the way threads share any data: through a borrowed
view `&[Atomic]` (a shared view is enough, since every operation is atomic).

| Operation | Result |
| --- | --- |
| `Atomic.new(v: i64)` | a new cell |
| `Atomic.value(a: Atomic)` | consumes a cell, giving its value |
| `Atomic.load(view, i)` | the element's value |
| `Atomic.store(view, i, v)` | `Unit` |
| `Atomic.fetch_add(view, i, v)` | the previous value (wrapping add) |
| `Atomic.swap(view, i, v)` | the previous value |
| `Atomic.compare_exchange(view, i, expected, new)` | `true` if the element was `expected` and is now `new` |

Every operation is sequentially consistent (Cranelift `atomic_load`,
`atomic_store`, `atomic_rmw`, `atomic_cas`) and bounds-checked like
`Slice.get` (it needs `panic`). An `Atomic` is affine and never copied:
`Slice.get`, `Vec.get`, indexing and copies are rejected, so a cell is never
read with a plain load that could race with an atomic write; it owns nothing,
so dropping one is free. The prover never treats an atomic's value as known.
With atomics, results may depend on the schedule; the reference evaluator
explores one schedule (threads run one at a time).

## Runtime

Threads run the cooperative tasks' wrapper (code, environment, result
buffer) under `pthread_create`, with a 64 MiB stack. A program that uses
threads is built with `KUSH_HAS_THREADS` and linked with `-pthread`; then the
allocation counters are atomic, and the allocator pool, the dynamic handler
stack, the current task and the abort word are per thread (generated code
reaches the abort word through `kush_abort_word_address`). Programs without
threads keep the single-threaded runtime unchanged.

The reference evaluator runs threads as cooperative tasks: one valid
schedule. Without shared mutable state both backends agree; the tests check
results, output and balanced allocations in the evaluator and natively.

Measured: four CPU-bound threads (2 x 10^8 multiply-mod steps each) take
477 ms against 1802 ms sequentially on the 6-core development laptop (3.8x).

## Limits

- No tasks (`suspend`) inside thread bodies; no thread-local declared
  handlers inherited from the parent.
- Allocator pool statistics (`KUSH_ALLOCATOR_POOL_STATS`) report the main
  thread's pool only.
- `Thread.spawn` panics after 64 nested thread scopes per OS thread.
