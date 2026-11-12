# Build time on a larger program

The other benchmarks are a few hundred lines. This one generates a program
of a chosen size, in Kush and in Rust, and times the builds.

```
python3 benchmarks/build-scale/generate.py 36 /tmp/scale      # main.kush, main.rs
python3 benchmarks/build-scale/measure.py --kush /path/to/kush --units 12 36
```

Each unit is seven functions (a checked reduction, an element-wise kernel, a
vector fill, branchy scalar code, a recursion, a search, a driver) whose
constants differ, so nothing is shared between units. `main` runs every unit
once; both languages print the same checksum, which `measure.py` verifies.

## Limits found on the way

- An executable could hold at most 256 function instances in all, which this
  program reached at 37 units, about 2,300 lines. The cap is now per
  declaration (256 specializations of one function) plus 1024 instances of
  generic functions in all; ordinary functions are unlimited.
- A source file may hold at most 100,000 tokens, about 12,000 lines of this
  program. That limit remains.

## Results

Seconds, best of three, on a 2-core cloud
machine with LLVM 18.1.3 and rustc 1.97. "Warm" means the proof cache held
this program's proofs; the C runtime cache was warm throughout.

| Build | 12 units (775 lines) | 36 units (2,311 lines) | 100 units (6,407 lines) | 180 units (11,527 lines) |
| --- | ---: | ---: | ---: | ---: |
| Kush, Cranelift | 0.07 | 0.12 | 0.29 | 0.53 |
| Kush, Cranelift, warm proof cache | 0.07 | 0.12 | 0.26 | 0.53 |
| Kush, LLVM `--release` | 0.60 | 1.97 | 5.78 | 13.06 |
| Kush, LLVM `--release`, warm proof cache | 0.64 | 1.83 | 5.55 | 11.56 |
| `rustc` debug | 0.13 | 0.20 | 0.45 | 0.62 |
| `rustc -C opt-level=3` | 0.33 | 0.76 | 2.18 | 3.82 |

- A development build is faster than a `rustc` debug build at every size,
  by 15% to 45%.
- An LLVM release build is 1.8 to 3.4 times slower than
  `rustc -C opt-level=3`, and the gap widens with size. On the two small
  benchmark programs it was faster; that did not generalize.
- Most of the gap is LLVM vectorizing the deferred-overflow loops (two per
  unit here, every one of which pays at run time): on the 100-unit program
  LLVM takes 5.3 seconds, and 2.4 without deferral. Rust vectorizes the
  same loops, but without a certificate and with one copy of each loop
  where Kush has two.
- Since the first measurement, LLVM's time on that program went from 12.4
  to 5.3 seconds: each deferred loop was lowered up to eight times, then
  three, now twice, and a late LLVM pass rescanned the whole function once
  per loop (see `docs/deferred-overflow.md`, "What is generated").
- Before two fixes made with this benchmark, the 100-unit build took 12.4
  seconds: each deferred loop was lowered up to eight times, and a late
  LLVM pass rescanned the whole function once per loop
  (see `docs/deferred-overflow.md`, "What is generated").

Not measured: a program split over several modules, incremental rebuilds
(Kush has none), and real code, which has fewer hot loops per line than
this generator produces.
