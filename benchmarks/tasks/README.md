# What tasks cost

The budget for moving tasks to std on fiber handlers
([docs/tasks-on-handlers.md](../../docs/tasks-on-handlers.md), decision T5):
yield and join within 10% of these times, spawn and join within 20%, the
reactor echo within 5%. The C scheduler is deleted only once they are met.

```sh
python3 benchmarks/tasks/run.py --kush /path/to/kush --cpu 5
```

## Kernels

| Kernel | Rounds | What one operation is |
| --- | ---: | --- |
| yield | 300,000 | one `Task.yield`; two tasks take turns, two per round |
| spawn-join | 250,000 | `Task.spawn` of a task that returns a number, then `Task.join` of it |
| spawn-scope | 300,032 | one of 64 children spawned in a `Task.scope` and joined by its end |
| echo | 25,000 | one byte to a task and back over loopback TCP (`std.net`, `TCP_NODELAY`), both ends waiting on the reactor |

Every build prints the same checksum before it is timed. Timing as in
[../languages](../languages/README.md): fresh processes pinned to one CPU,
shuffled, two warm-ups, median of 15, process startup included.

## Results

2026-11-27, Kush at c2fdb3c, tsar-bomba-2 (Ryzen 5 5500), median:

| Kernel | Operation | LLVM ms | LLVM ns/op | Cranelift ms | Cranelift ns/op |
| --- | --- | ---: | ---: | ---: | ---: |
| yield | yield | 553 | 921 | 558 | 931 |
| spawn-join | spawn and join | 604 | 2418 | 594 | 2374 |
| spawn-scope | spawn, scope join | 453 | 1510 | 457 | 1523 |
| echo | round trip | 480 | 19207 | 489 | 19576 |

- The backend does not matter: the runtime does the work.
- A yield costs about 920 ns, and `perf` puts 99.9% of the yield kernel's
  time in the kernel. That fits the runtime switching with `swapcontext`,
  which makes a signal-mask system call on every switch; the switch itself
  is a few registers. A fiber switch without it should cost tens of
  nanoseconds, so the budget for yield and spawn is easy to meet and most
  of their current cost can go.
- The echo is dominated by the loopback round trip and `epoll`, not by the
  scheduler.
