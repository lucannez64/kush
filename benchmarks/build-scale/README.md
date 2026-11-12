# Build time on a larger program

The other benchmarks are a few hundred lines. This one generates a program
of a chosen size, in Kush, Rust and C, and times the builds.

```
python3 benchmarks/build-scale/generate.py 36 /tmp/scale      # main.kush, main.rs, main.c
python3 benchmarks/build-scale/measure.py --kush /path/to/kush --units 12 36
```

Each unit is seven functions (a checked reduction, an element-wise kernel, a
vector fill, branchy scalar code, a recursion, a search, a driver) whose
constants differ, so nothing is shared between units. `main` runs every unit
once; all three print the same checksum, which `measure.py` verifies for the
optimized builds. The C version has no overflow checks, so it shows what the
same work costs a C compiler; `cc` here is GCC 13.

`KUSH_TIME_PHASES=1` makes `kush` print where a build spends its time
(parsing, checking, lowering, `clang`, linking) to standard error.

## Limits found on the way

- An executable could hold at most 256 function instances in all, which this
  program reached at 37 units, about 2,300 lines. The cap is now per
  declaration (256 specializations of one function) plus 1024 instances of
  generic functions in all; ordinary functions are unlimited.
- A source file may hold at most 100,000 tokens, about 12,000 lines of this
  program. That limit remains.

## Results

Seconds, best of three, on a 2-core cloud machine with LLVM 18.1.3, rustc
1.97 and GCC 13. "Warm" means the proof cache held this program's proofs;
the C runtime cache was warm throughout.

| Build | 12 units (775 lines) | 40 units (2,567 lines) | 100 units (6,407 lines) | 180 units (11,527 lines) |
| --- | ---: | ---: | ---: | ---: |
| Kush, Cranelift | 0.06 | 0.13 | 0.26 | 0.51 |
| Kush, Cranelift, warm proof cache | 0.06 | 0.14 | 0.30 | 0.52 |
| Kush, LLVM `--release` | 0.63 | 0.94 | 2.54 | 4.53 |
| Kush, LLVM `--release`, warm proof cache | 0.67 | 1.06 | 2.71 | 4.60 |
| `rustc` debug | 0.14 | 0.20 | 0.41 | 0.63 |
| `rustc -C opt-level=3` | 0.31 | 0.84 | 1.94 | 4.06 |
| `cc -O0` | 0.07 | 0.18 | 0.41 | 0.62 |
| `cc -O2` | 0.14 | 0.46 | 1.32 | 2.45 |

- A development build is faster than `cc -O0` and than a `rustc` debug
  build at every size.
- An LLVM release build is 1.1 to 2 times slower than
  `rustc -C opt-level=3`; the gap is largest on the smallest program. Before
  the changes below it was 1.8 to 3.4 times, widening with size.
- Large programs are split into partitions that LLVM optimizes and compiles
  in parallel (`docs/llvm-backend.md`, "Parallel partitions"); that took the
  180-unit build from 13 to 4.5 seconds. A program under about 8,000 lines
  of LLVM IR stays whole: splitting the 12-unit one in two builds it in 0.39
  seconds instead of 0.63, but separates hot kernels from their only
  caller, and a kernel benchmark ran up to 25% slower.
- On the whole 12-unit module, `clang -O3` takes about as long as it does
  on the C version at `-O3` (0.60 against 0.61 seconds). Most of the
  remaining gap to `cc -O2` is optimization level and compiler, not the
  IR Kush emits.
- The deferred-overflow loops are still the main cost: with
  `--no-deferred-overflow` the 12-unit build takes 0.33 seconds. Deferral
  adds only 7% more IR but lets LLVM vectorize and unroll every such loop,
  which pays at run time.
- Fewer IR lines per Kush line also helped, by about 10% of LLVM's time:
  loop-invariant block parameters no longer become phis, conditions stay
  `i1` from comparison to branch, an access range is checked once per
  slice rather than once per access, and a slice of known layout loads
  without testing its byte flag (24% fewer lines on this program).
- Earlier, each deferred loop was lowered up to eight times and a late
  LLVM pass rescanned the whole function once per loop; fixing both took
  the 100-unit build from 12.4 to 5.3 seconds before partitioning (see
  `docs/deferred-overflow.md`, "What is generated").

Not measured: a program split over several modules, incremental rebuilds
(Kush has none), and real code, which has fewer hot loops per line than
this generator produces.
