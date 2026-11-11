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
| `KUSH_LLVM_NO_WHOLE_PROGRAM` | Do not use `llvm-link`: runtime operations stay calls into the runtime object. |
| `KUSH_TRACE_DEFERRED` | Print why a loop keeps immediate overflow checks. |

Requirements: Linux x86-64 and a `clang` with opaque pointers (LLVM 15 or
newer; developed and tested with LLVM 18.1). To inline runtime operations into
user code, `llvm-link` from the same LLVM must sit beside the real `clang`
binary or be reported by `clang -print-prog-name=llvm-link`; distribution
packages named `llvm` provide it. Without it the backend still works, but
runtime operations stay calls.

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

### A precompiled runtime with inlinable bodies

The C runtime is compiled by `clang` once per compiler, flags and system
headers, and cached. From that single LLVM module the backend derives three
artifacts (`split_runtime` in `native/llvm.rs`):

- **the runtime object**, linked into every program. It is the module
  unchanged, except that internal functions and variables are *hidden*
  instead, so the program object can refer to them;
- **inlinable bodies**: the same module as bitcode with every definition
  marked `available_externally`. LLVM may inline such a body and then discards
  it; it is never compiled again. Variables are `available_externally` too, so
  there is exactly one copy of the allocator pools, counters and task state:
  the runtime object's;
- **the interface**: each runtime function's real signature. Calls are
  emitted with exactly that type, converting words to pointers where the C
  prototype has one, because a call through a mismatched type is never
  inlined.

Each build then runs `llvm-link --only-needed` to pull the bodies the program
reaches into the program module, and `clang -O3` on the result. Only program
code is optimized and compiled per build, as with a Rust program and its
precompiled standard library.

Only plain accessors may actually be inlined (`INLINABLE`: vector, byte and
string reads, in-place element writes, float conversions, handler depth).
Everything else carries `noinline`. The allocator in particular must stay an
opaque call, for the reason given under ownership facts.

### Ownership facts

Kush knows more about aliasing than LLVM can discover, and tells it in two
ways.

**Exclusive parameters.** A parameter that is an owning handle (`Box<T>`,
`Vec<T>`, `Bytes`, `String`) or an exclusive borrow (`&mut T`, the data
pointer of `&mut [T]` and `&mut str`) becomes a `ptr noalias` parameter. The
translator derives every address computed from it by `getelementptr`, so the
accesses stay based on that parameter. When such a function is inlined, LLVM
keeps the fact as scoped alias metadata. A function with pointer parameters
whose address is taken (function values, closures, task entries) gets a
`.words` thunk with the plain word signature, and that thunk is what function
pointers refer to, so an indirect call always has the type of its callee.

**Memory classes.** The generator marks the loads and stores of its inline
vector and byte-buffer paths as *buffer header* (length, capacity) or *buffer
elements*. A header word is never an element of any buffer, so the two get
distinct type-based alias tags under a root of their own; they say nothing
about untagged accesses or about the C runtime's accesses. The class travels
as the Cranelift instruction's source location, which Cranelift's code
generator ignores. (Cranelift's own alias regions were not used: it treats
untagged memory as disjoint from every region, which would be wrong here.)

Both kinds of fact are statements about objects. Kush's allocator recycles
blocks, so the same address can be a freed vector's elements and later a new
vector's header. That is sound for the same reason it is in C and Rust: the
recycling happens behind `kush_alloc`/`kush_free` calls LLVM cannot see
through. This is why allocator functions are never inlined into program code.

Not stated yet: shared borrows are not marked `readonly`, allocation results
are not marked as fresh, and exclusive values held in locals or fields (as
opposed to parameters) carry no fact.

### Checks

Bounds checks are ordinary compare-and-branch code in both backends. With the
accessors inlined, LLVM removes them wherever the index is bounded by the same
length, which covers `while i < Slice.len(v)` and `while i < Vec.len(&v)`
loops; `Vec.at`/`Slice.at` with a proof remain unchecked loads as before.

Overflow checks become `llvm.*.with.overflow` intrinsics, which LLVM removes
for induction variables and other provably bounded values. Checks on data
values are handled by [deferred overflow](deferred-overflow.md).

## Validation

- `KUSH_BACKEND=llvm cargo test --workspace` replays the entire suite on the
  LLVM backend: 1,694 tests pass on both backends (LLVM 18.1.3, 2026-11-11).
  Tests that replace `cc` to exercise the Cranelift pipeline pin themselves to
  it.
- `tests/llvm_backend.rs` runs 22 example programs through four LLVM
  configurations and the no-`llvm-link` pipeline, compares output and exit
  status with Cranelift, and checks that ownership facts appear in the module.
  It passes vacuously without `clang`.
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
| Kush, Cranelift `--release` | 146 |
| Kush, LLVM, immediate checks | 63 |
| Kush, LLVM | 61 |
| Rust checked | 62 |
| Rust | 59 |

`benchmarks/checked-loops`, 4,096 elements × 200,000 repetitions:

| Kernel | Cranelift | LLVM immediate | LLVM | Rust checked | Rust | LLVM native | Rust native |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| sum | 803 | 267 | 177 | 265 | 84 | 72 | 53 |
| dot | 1324 | 530 | 519 | 528 | 425 | 196 | 162 |
| scale, then sum | 2336 | 1128 | 565 | 818 | 468 | 269 | 254 |

Reading these:

- LLVM is 2.4 to 4.5 times faster than Cranelift `--release` here.
- With checks kept, Kush matches or beats Rust built with overflow checks,
  and is within 3% to 2.1× of unchecked Rust. The sum is the worst case: its
  certificate costs four SSE2 instructions per vector next to Rust's one add.
- `feature-pipeline` is within 3% of Rust. Stating ownership facts took it
  from 69 ms to 61 ms. What remains is `Vec.push`: a Kush vector keeps its
  length and encoded capacity in the heap block, so each push loads both and
  decodes the capacity (14 instructions per element against Rust's 8).

Build time for the same two programs, median of five in milliseconds:

| Build | feature-pipeline | checked-loops |
| --- | ---: | ---: |
| Kush, Cranelift | 74 | 78 |
| Kush, LLVM `--release` | 156 | 159 |
| `rustc` debug | 133 | 114 |
| `rustc -C opt-level=3` | 250 | 210 |
| Kush, Cranelift, no proof cache | 142 | 128 |
| Kush, LLVM `--release`, no proof cache | 207 | 221 |

With warm caches an LLVM release build takes about two thirds of `rustc`'s
time and a development build a little over half. Two things make that
possible. The runtime is precompiled, so only program code goes through LLVM.
And the [proof cache](proof-cache.md) removes most of the front end's work:
without it (the last two rows, which is also what the very first build of a
project costs) Kush and `rustc` are about level. These are small programs;
nothing here measures a large code base, where Kush still checks and compiles
the whole program on every build.

## Limits

- Linux x86-64 only, as for Cranelift.
- Apart from exclusive parameters, function parameters and loaded words are
  still integers; only values with a local pointer origin get pointer forms.
- `--target-cpu native` code runs only on machines with the build machine's
  features.
- Debug information is not emitted.
