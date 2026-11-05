# Effect perform paths (EFF-CAP-PERF)

Build each program with `kush build <file>.kush -o <dir>/<name> --release`
(including `empty.kush`), then run `python3 -I measure.py <dir>`.
Every program computes the same masked sum over 10^7 performs or calls with
a pure, tail-resumptive handler (`resume(x ^ 5)`); all exit with 192.

Results, x86-64 Linux laptop, 2026-11-05, load average about 4, two runs:

| Program | ns/iteration |
| --- | --- |
| `direct-call` | 1.91, 2.19 |
| `lexical-perform` (perform in the handled body) | 3.49, 3.74 |
| `capability-perform-lexical` (`perform tick(i)` in the body) | 3.50, 3.74 |
| `capability-perform-in-callee` (`work(tick, i)`) | 4.49, 4.72 |
| `dynamic-perform-in-callee` (`perform Tick(x)` in `work`) | 6.69, 7.25 |
