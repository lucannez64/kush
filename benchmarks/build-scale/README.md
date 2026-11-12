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

## Two limits found on the way

- An executable may hold at most 256 function instances
  (`MAX_FUNCTIONS` in `executable.rs`), which this program reaches at 37
  units, about 2,300 lines.
- A source file may hold at most 100,000 tokens, about 12,000 lines of this
  program.

The first two columns below were measured with the compiler as it is. The
last two needed a throwaway build with `MAX_FUNCTIONS` raised; that change
is not in the repository.

## Results

Seconds, best of three (two for the larger sizes), on a 2-core cloud
machine with LLVM 18.1.3 and rustc 1.97. "Warm" means the proof cache held
this program's proofs; the C runtime cache was warm throughout.

| Build | 12 units (775 lines) | 36 units (2,311 lines) | 100 units (6,407 lines) | 180 units (11,527 lines) |
| --- | ---: | ---: | ---: | ---: |
| Kush, Cranelift | 0.08 | 0.13 | 0.27 | 0.56 |
| Kush, Cranelift, warm proof cache | 0.07 | 0.13 | 0.30 | 0.47 |
| Kush, LLVM `--release` | 0.66 | 2.08 | 6.34 | 13.86 |
| Kush, LLVM `--release`, warm proof cache | 0.75 | 2.21 | 6.84 | 14.08 |
| `rustc` debug | 0.14 | 0.22 | 0.37 | 0.72 |
| `rustc -C opt-level=3` | 0.35 | 0.84 | 1.95 | 3.93 |

- A development build is faster than a `rustc` debug build at every size,
  by 25% to 45%.
- An LLVM release build is 2 to 3.5 times slower than
  `rustc -C opt-level=3`, and the gap widens with size. On the two small
  benchmark programs it was faster; that did not generalize.
- Nearly all of it is LLVM working on deferred-overflow loops: with
  `--no-deferred-overflow` the 100-unit program built in under 3 seconds
  when this was first measured. A vectorized loop with its certificate is
  two to three times the work of the scalar checked loop in every pass.
- Before two fixes made with this benchmark, the 100-unit build took 12.4
  seconds: each deferred loop was lowered up to eight times, and a late
  LLVM pass rescanned the whole function once per loop
  (see `docs/deferred-overflow.md`, "What is generated").

Not measured: a program split over several modules, incremental rebuilds
(Kush has none), and real code, which has fewer hot loops per line than
this generator produces.
