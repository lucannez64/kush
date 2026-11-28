# What tasks cost

The budget for moving tasks to std on fiber handlers
([docs/tasks-on-handlers.md](../../docs/tasks-on-handlers.md), decision T5):
yield and join within 10% of the C scheduler's times below, spawn and join
within 20%, the reactor echo within 5%. The C scheduler is deleted only
once they are met. The reference is the scheduler on the hand-written
switch (FIBER-RUNTIME), so std's fibers have to keep that switch's speed.

```sh
python3 benchmarks/tasks/run.py --kush /path/to/kush --cpu 5
```

## Kernels

| Kernel | Rounds | What one operation is |
| --- | ---: | --- |
| yield | 3,000,000 | one `Task.yield`; two tasks take turns, two per round |
| spawn-join | 2,500,000 | `Task.spawn` of a task that returns a number, then `Task.join` of it |
| spawn-scope | 3,000,000 | one of 64 children spawned in a `Task.scope` and joined by its end |
| echo | 25,000 | one byte to a task and back over loopback TCP (`std.net`, `TCP_NODELAY`), both ends waiting on the reactor |

Every build prints the same checksum before it is timed. Timing as in
[../languages](../languages/README.md): fresh processes pinned to one CPU,
shuffled, two warm-ups, median of 15, process startup included.

## Results

2026-11-27, tsar-bomba-2 (Ryzen 5 5500), median. With the hand-written
switch (FIBER-RUNTIME), the budget's reference:

| Kernel | Operation | LLVM ms | LLVM ns/op | Cranelift ms | Cranelift ns/op |
| --- | --- | ---: | ---: | ---: | ---: |
| yield | yield | 194 | 32 | 185 | 31 |
| spawn-join | spawn and join | 250 | 100 | 260 | 104 |
| spawn-scope | spawn, scope join | 281 | 94 | 274 | 91 |
| echo | round trip | 434 | 17348 | 433 | 17311 |

Before, at c2fdb3c, with `swapcontext` (rounds a tenth of the above for
yield and the spawns):

| Kernel | Operation | LLVM ms | LLVM ns/op | Cranelift ms | Cranelift ns/op |
| --- | --- | ---: | ---: | ---: | ---: |
| yield | yield | 553 | 921 | 558 | 931 |
| spawn-join | spawn and join | 604 | 2418 | 594 | 2374 |
| spawn-scope | spawn, scope join | 453 | 1510 | 457 | 1523 |
| echo | round trip | 480 | 19207 | 489 | 19576 |

- The backend does not matter: the runtime does the work.
- `swapcontext` saves and restores the signal mask with a system call each
  way, and `perf` put 99.9% of the old yield kernel's time in the kernel.
  The hand-written switch saves six registers and two control words: a
  yield went from 921 to 32 ns, a spawn and join from 2,418 to 100 ns.
  Control blocks also became small enough for the allocator's pool.
- The echo is dominated by the loopback round trip and `epoll`; it gained
  10%.

## std.sched (STD-SCHED-BENCH)

The yield and spawn-join kernels again, scheduled by `std.sched`, the
scheduler written in Kush on fibers (same checksums). 2026-11-28,
tsar-bomba-2, compiler at 2f4605a, same session as the first four rows:

| Kernel | Operation | LLVM ms | LLVM ns/op | Cranelift ms | Cranelift ns/op |
| --- | --- | ---: | ---: | ---: | ---: |
| yield | yield | 181 | 30 | 176 | 29 |
| spawn-join | spawn and join | 231 | 92 | 229 | 91 |
| sched-yield | yield (std.sched) | 413 | 69 | 450 | 75 |
| sched-spawn-join | spawn and join (std.sched) | 700 | 280 | 761 | 304 |

`std.sched` is 2.3 times the C scheduler for a yield and 3 times for a
spawn and join, far from the T5 budget (10% and 20%). `perf` on the LLVM
build: the switch itself is 11-14% of the time; the rest is the Kush side.

| Where | yield | spawn-join |
| --- | ---: | ---: |
| `run`'s loop (match, queue, bookkeeping) | 19% | 18% |
| `kush_vec_set` and `kush_vec_get` (out-of-line calls) | 15% | 20% |
| `kush_switch` | 14% | 11% |
| `kush_fiber_suspend`, `_resume`, the fiber handler | 24% | 12% |
| libc `memcpy` | 6% | 8% |
| `kush_fiber_new`, block claim and release | | 12% |

To get within budget: `Vec.get`/`Vec.set` compiled inline, the per-slot
vectors folded into one record per slot, the step and reply passed in
registers rather than through copied slots, and a fiber stack reused with
its slot.
