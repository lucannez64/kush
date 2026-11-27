# Kush against Rust, C and Zig

The same small programs in four languages, measured on one machine: run
time, binary size and build time. The other benchmarks compare Kush with one
language each; this one puts all four side by side on the current compiler.
The results are specific to these workloads and toolchains, not a language
ranking.

```sh
python3 benchmarks/languages/run.py --kush /path/to/kush --zig /path/to/zig --cpu 5
python3 benchmarks/build-scale/measure.py --kush /path/to/kush --zig /path/to/zig --units 12 40 100 180
```

`run.py` needs `rustc`, `gcc`, `clang`, `zig`, `strip` and `taskset`.

## Workloads

| Name | Kush | Rust | C | Zig |
| --- | --- | --- | --- | --- |
| loops: sum, dot, scale then sum (4,096 elements × 200,001 rounds) | `../checked-loops/kush` | `../checked-loops/rust` | `c/loops.c` | `zig/loops.zig` |
| pipeline: fused feature-pipeline batch (2,097,152 elements × 16 batches) | `../feature-pipeline/kush` (mode 1) | `../feature-pipeline/rust` (mode 1) | `c/pipeline.c` | `zig/pipeline.zig` |
| hello world | `kush/hello.kush` | `rust/hello.rs` | `c/hello.c` | `zig/hello.zig` |
| build time: generated program, 7 functions per unit | `../build-scale` | same | same | same |

Every build of a workload must print the same number before anything is
timed.

## Checked and unchecked

Kush checks every `+`, `-` and `*` for overflow and every index against its
slice. The other languages are built both ways:

- **Rust:** `-C opt-level=3 -C panic=abort`, with and without
  `-C overflow-checks=yes`. Indexing is always checked.
- **Zig:** ReleaseSafe checks overflow and indexing, like Kush; ReleaseFast
  checks neither.
- **C:** `-O2` with gcc and clang. `-DCHECKED` checks arithmetic with
  `__builtin_*_overflow`; C has no bounds checks in either build.

All builds target baseline x86-64 (Kush's default `--target-cpu baseline`,
no `-march=native` anywhere).

## Method

- Run time: fresh process per sample, pinned to one CPU with `taskset`, all
  variants of a workload interleaved in shuffled order, two warm-up rounds,
  median of 15.
- Size: the binary as built, and after `strip`. Every build links libc
  dynamically except `gcc-static`.
- Build time in `run.py`: one build of each small program. Each Zig build
  gets an empty local cache (`--cache-dir`), so it compiles the program; its
  global cache keeps Zig's prebuilt runtime, as `cc` keeps libc.
- Build time on larger programs: `../build-scale/measure.py`, best of three.

## Results

2026-11-27, Kush at 1e47209 (release build of the compiler), on
tsar-bomba-2: AMD Ryzen 5 5500 (6 cores, 12 threads), GCC 16.2.1,
clang 23.1.5, rustc 1.101.0-nightly, Zig 0.17.1. The machine was not idle
(load 4 to 6 from other builds and a container pull); runs were pinned to
one CPU and interleaved, and every median is within about 10% of its
fastest sample.

### Run time (median ms, lower is better)

| Workload | Kush LLVM | Kush Cranelift | Rust checked | Rust | gcc checked | gcc | clang checked | clang | Zig ReleaseSafe | Zig ReleaseFast |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| sum | **133** | 671 | 233 | 61 | 457 | 244 | 229 | 116 | 230 | 201 |
| dot | 441 | 1057 | 422 | 269 | 462 | 235 | **330** | 290 | 423 | 236 |
| scale, then sum | **391** | 1844 | 629 | 335 | 848 | 548 | 561 | 369 | 647 | 457 |
| pipeline | 57 | 92 | 64 | 55 | 56 | 59 | **49** | 48 | 113 | 77 |

Bold is the fastest checked build.

- Among builds that check overflow, Kush with LLVM is fastest on sum (1.7×
  ahead of the next) and on scale then sum (1.4×), where deferred overflow
  checks let the loop vectorize. On dot it ties Rust and Zig and trails
  clang's checked build by 1.3×; on the pipeline it is between the C builds
  (1.0× gcc's checked build, 1.16× clang's) and ahead of Rust's.
- Against builds that check nothing, Kush is 2.2× behind Rust on sum, 1.6×
  to 1.9× behind on dot, and 1.0× to 1.2× on scale then sum and the pipeline.
- Zig's LLVM leaves `sum` scalar (unrolled 8×) where rustc's vectorizes, and
  its pipeline is allocator-bound: Zig's allocator returns the 16 MiB vector
  to the system after each batch and faults it back in (8,404 page faults,
  against 590 for the C build, whose `malloc` reuses it).
- Cranelift (Kush's development backend) is 1.6× to 5× slower than LLVM.

### Size (bytes)

| Program | Kush LLVM | Kush Cranelift | Rust | gcc | gcc `-static` | Zig ReleaseFast | Zig ReleaseSmall |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| hello, stripped | 84,880 | 80,744 | 334,864 | 14,496 | 825,640 | 505,720 | 148,584 |
| hello, as built | 102,232 | 99,896 | 4,565,776 | 16,040 | 906,960 | 4,049,040 | 148,584 |
| loops, stripped | 84,880 | 84,840 | 341,416 (checked) | 14,536 | | 508,088 | |

Kush, Rust and gcc link libc dynamically; Zig links nothing and carries its
own runtime. A Kush program's floor is its runtime, about 80 KB: the loops
program is the size of hello world.

### Build time (seconds)

Single builds of the small programs (`run.py`): Kush 0.07 to 0.08
(Cranelift) and 0.13 to 0.43 (LLVM), Rust 0.12 to 0.40, C 0.05 to 0.09, Zig
13 to 18 (release, empty local cache) and 4.8 (ReleaseSmall).

`../build-scale/measure.py`, best of three:

| Build | 12 units (715 lines) | 40 units (2,367 lines) | 100 units (5,907 lines) | 180 units (10,627 lines) |
| --- | ---: | ---: | ---: | ---: |
| Kush, Cranelift | 0.10 | 0.17 | 0.38 | 0.55 |
| Kush, LLVM `--release` | 0.43 | 0.53 | 1.00 | 1.34 |
| `rustc` debug | 0.09 | 0.18 | 0.41 | 0.58 |
| `rustc -C opt-level=3` | 0.24 | 0.71 | 2.05 | 3.16 |
| `cc -O0` | 0.07 | 0.18 | 0.40 | 0.61 |
| `cc -O2` | 0.20 | 0.71 | 2.00 | 3.16 |
| `zig` Debug | 0.34 | 0.39 | 0.46 | 0.43 |
| `zig` ReleaseSafe | 14.32 | 18.08 | 23.19 | 32.40 |
| `zig` ReleaseFast | 14.01 | 16.27 | 20.28 | 25.04 |

- A Kush development build keeps pace with `cc -O0` and a `rustc` debug
  build. A Zig debug build (its own x86 backend) costs about 0.35 s up front
  but grows slowest, and is the fastest at 10,600 lines.
- A Kush release build is about 2× slower than `rustc -O3` and `cc -O2` on
  the smallest program (0.43 s, mostly `clang` and linking) and the fastest
  optimizing build from about 2,000 lines: 2.4× faster than both at 10,600
  lines.
  That is wall time; large programs are optimized in parallel partitions
  (`docs/llvm-backend.md`), so it uses more than one core. `cc` uses one.
  Kush caches proofs and its C runtime between builds, not program code;
  the warm-proof-cache rows (omitted) match the cold ones within 0.03 s.
- A Zig release build recompiles the standard library with LLVM when its
  local cache is empty, about 14 s before any program code.
