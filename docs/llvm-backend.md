# LLVM release backend

Kush has two native code generators. Cranelift stays the default: it builds
fast and needs only `cc`. LLVM is opt-in for release builds: it builds slower,
needs `clang`, and produces substantially faster programs.

```sh
kush build program.kush -o program --release --backend llvm
kush run   program.kush --release --backend llvm -- argument
kush build --manifest-path path/Kush.toml --release --backend llvm
```

| Flag | Meaning |
| --- | --- |
| `--backend <cranelift\|llvm>` | Code generator. `llvm` also turns on deferred overflow checks. |
| `--release` | Speed optimization and scalar callback inlining, on either backend (`-O3` on LLVM; without it LLVM uses `-O1`). |
| `--no-deferred-overflow` / `--deferred-overflow` | Panic at the overflowing operation instead of at the loop exit, or opt in on Cranelift. See [deferred-overflow.md](deferred-overflow.md). |
| `--target-cpu <baseline\|native>` | LLVM only. `native` passes `-march=native`; the default is the portable x86-64 baseline, like Rust. |

Flags are processed in order and `--release` keeps an earlier `--backend`.
`check`, `eval` and `test` are unaffected.

Environment:

| Variable | Meaning |
| --- | --- |
| `KUSH_CLANG` | The `clang` to use (default: `clang` on `PATH`). |
| `KUSH_BACKEND=llvm\|cranelift` | Override the backend of every native build in the process. Meant for replaying a test suite on the other backend. |
| `KUSH_EMIT_LLVM=path` | Also save the program's LLVM module (before linking with the runtime and optimizing). |
| `KUSH_LLVM_NO_WHOLE_PROGRAM` | Compile the program module alone and link the ordinary runtime object. |
| `KUSH_TRACE_DEFERRED` | Print why a loop keeps immediate overflow checks. |

Requirements: Linux x86-64 and a `clang` with opaque pointers (LLVM 15 or
newer; developed and tested with LLVM 18.1). For whole-program optimization
`llvm-link` from the same LLVM must sit beside the real `clang` binary or be
reported by `clang -print-prog-name=llvm-link`; distribution packages named
`llvm` provide it. Without it the backend still works, but runtime operations
are not inlined into user code.

## Design

### One lowering, two code generators

The checked executable IR is lowered exactly once, by `Generator` in
`native.rs`, into verified Cranelift IR. The default backend passes each
function to Cranelift's code generator. The LLVM backend passes the same
verified function to `native/llvm.rs`, which prints it as textual LLVM IR.

`CodeModule` implements Cranelift's `Module` trait and makes the choice in
`define_function`; the 6,500 lines of lowering do not know which backend is
active. Evaluation order, checks, layouts, drop glue, task wrappers and the
handler protocol are therefore identical by construction, and a lowering fix
reaches both backends. The translator handles the instruction set the
generator uses (about 60 opcodes) and reports any other instruction as an
error instead of guessing.

No LLVM library is linked into `kush`, the workspace keeps
`unsafe_code = "forbid"`, and the compiler's own build time is unchanged.

Where the two IRs differ, the translator keeps Cranelift's defined behaviour:
division and remainder trap on zero and on `MIN / -1` (LLVM would have
undefined behaviour), shift amounts are reduced modulo the width, and loads and
stores carry alignment 1.

### Pointer forms

Cranelift values are untyped words, and LLVM optimizes memory poorly when
every address is an `inttoptr`. Each translated value keeps its integer form;
values with a known pointer origin (stack slots, symbols, function addresses,
pointers returned by the runtime) also keep a pointer form. At each load,
store and pointer-typed runtime argument the address is rebuilt as a
`getelementptr` on the pointer form, looking through `base + offset`
additions. Stack slots whose address does not escape are promoted to
registers, and array accesses appear to LLVM as a pointer plus an induction
variable, which is what its loop vectorizer needs.

### The runtime is optimized with the program

`clang -S -emit-llvm` compiles the C runtime to LLVM IR once (cached like the
runtime object, under a separate key). The backend reads each runtime
function's real signature from that IR and emits calls with exactly that type,
converting words to pointers where the C prototype has one; a call through a
mismatched type would never be inlined.

`llvm-link --internalize --only-needed` then pulls the runtime functions the
program reaches into the program module with internal linkage, and
`clang -O3` optimizes and compiles the single module. `Vec.get`, `Vec.set`,
byte operations, allocation fast paths and handler-depth bookkeeping inline
into user code, and their bounds checks become visible to LLVM's range
analysis. The runtime is compiled with `KUSH_WHOLE_PROGRAM`, which turns its
`main` into `kush_runtime_main(argc, argv, entry)`; the program module defines
the real `main` and passes its internal entry function, so `main` is the only
visible symbol.

Programs with extra link inputs (`Bridge.toml` adapters, foreign objects)
link the whole runtime without internalizing, because foreign code may call
runtime symbols.

### Checks

Bounds checks are ordinary compare-and-branch code in both backends. With the
runtime inlined, LLVM removes them wherever the index is bounded by the same
length, which covers `while i < Slice.len(v)` and `while i < Vec.len(&v)`
loops; `Vec.at`/`Slice.at` with a proof remain unchecked loads as before.

Overflow checks become `llvm.*.with.overflow` intrinsics, which LLVM removes
for induction variables and other provably bounded values. Checks on data
values are handled by [deferred overflow](deferred-overflow.md).

## Validation

- `KUSH_BACKEND=llvm cargo test --workspace` replays the entire suite on the
  LLVM backend: 1,691 tests pass on both backends (LLVM 18.1.3, 2026-11-11).
  Tests that replace `cc` to exercise the Cranelift pipeline pin themselves to
  it.
- `tests/llvm_backend.rs` runs 22 example programs through four LLVM
  configurations and the separate-runtime pipeline and compares output and
  exit status with Cranelift. It passes vacuously without `clang`.
- `tests/deferred_overflow.rs` compares the evaluator with up to nine native
  configurations, including panicking programs.

## Measurements

Two-core cloud VM (Xeon, 2.1 GHz nominal), LLVM 18.1.3, rustc 1.97.0. Fresh
process per sample, 15 samples after 2 warm-ups, shuffled order, medians in
milliseconds. The machine was otherwise idle but is shared hardware; treat
differences under about 5% as noise. Kush always checks overflow. "Rust
checked" is `-C overflow-checks=yes`; "Rust" is an ordinary `-C opt-level=3`
build, which does not check.

`benchmarks/feature-pipeline`, 2,097,152 elements × 16 batches, fused mode:

| Build | Time |
| --- | ---: |
| Kush, Cranelift `--release` | 141 |
| Kush, LLVM, immediate checks | 78 |
| Kush, LLVM | 69 |
| Rust checked | 63 |
| Rust | 60 |

`benchmarks/checked-loops`, 4,096 elements × 200,000 repetitions:

| Kernel | Cranelift | LLVM immediate | LLVM | Rust checked | Rust | LLVM native | Rust native |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| sum | 786 | 260 | 170 | 265 | 84 | 70 | 52 |
| dot | 1320 | 523 | 518 | 508 | 418 | 197 | 165 |
| scale, then sum | 2269 | 1105 | 554 | 784 | 458 | 267 | 258 |

Reading these:

- LLVM is 2 to 4.6 times faster than Cranelift `--release` here.
- With checks kept, Kush matches or beats Rust built with overflow checks,
  and is within 3% to 2.1× of unchecked Rust. The sum is the worst case: its
  certificate costs four SSE2 instructions per vector next to Rust's one add.
- The remaining gap in `feature-pipeline` is `Vec.push`. A Kush vector keeps
  its length and capacity in the heap block, so each push loads and stores
  them (14 instructions per element against Rust's 8, which keeps them in
  registers). The map and checksum loops match Rust's code.

Build time for the same two programs (warm runtime cache, median of five):

| Build | feature-pipeline | checked-loops |
| --- | ---: | ---: |
| Kush, Cranelift | 133 | 139 |
| Kush, Cranelift `--release` | 136 | 136 |
| Kush, LLVM `--release` | 311 | 298 |
| `rustc` debug | 139 | 118 |
| `rustc -C opt-level=3` | 249 | 199 |

For programs this small an LLVM release build of Kush is slower than `rustc`:
Kush re-optimizes the runtime and standard-library code the program uses on
every build, while Rust links a precompiled standard library, and about 85 ms
of every Kush build is its own front end. Development builds are unchanged.

## Limits

- Linux x86-64 only, as for Cranelift.
- No alias metadata yet. Ownership facts (`Box` uniqueness, `&mut`
  exclusivity) are not passed to LLVM as `noalias`, and vector header fields
  are not distinguished from element storage. Type-based tags for those were
  left out deliberately: with the pool allocator inlined into the same module,
  a freed element block can be reused as a header within one function, which
  type-based alias rules would let LLVM reorder incorrectly.
- Function parameters and loaded words are still integers; only values with a
  local pointer origin get pointer forms.
- `--target-cpu native` code runs only on machines with the build machine's
  features.
- Debug information is not emitted.
