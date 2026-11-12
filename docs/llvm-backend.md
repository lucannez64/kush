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
| `KUSH_BACKEND=llvm\|llvm-release\|cranelift` | Override the backend of every native build in the process. Meant for replaying a test suite on the other backend; `llvm-release` also forces release settings, so the suite exercises `-O3` and deferred loops as users get them. |
| `KUSH_EMIT_LLVM=path` | Also save the program's LLVM module (before linking with the runtime and optimizing). |
| `KUSH_LLVM_NO_WHOLE_PROGRAM` | Do not use `llvm-link`: runtime operations stay calls into the runtime object. |
| `KUSH_TRACE_DEFERRED` | Print why a loop keeps immediate overflow checks. |

Requirements: Linux x86-64 and a `clang` with opaque pointers (LLVM 15 or
newer; developed and tested with LLVM 18.1). To inline runtime operations into
user code, `llvm-link` from the same LLVM must sit beside the real `clang`
binary or be reported by `clang -print-prog-name=llvm-link`; distribution
packages named `llvm` provide it. A compiler wrapper such as ccache is looked
through only by asking it (`-print-prog-name`), never by taking whatever sits
beside the wrapper. Without `llvm-link`, or if it cannot read this clang's
bitcode, the backend still works, but runtime operations stay calls.

`--deferred-overflow` and `--no-deferred-overflow` mean the same wherever
they stand relative to `--backend`.

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
translator derives addresses of the usual `base + offset` shapes from it by
`getelementptr`; any other address arithmetic goes through the integer form
and `inttoptr`, which LLVM treats as based on every pointer that contributed
to the integer, so the fact stays true but is less useful there. When such a function is inlined, LLVM
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
through. This is why allocator functions are never inlined into program code, and
why the inlinable set holds only functions that neither allocate nor free
(checked by hand when the list changes; the list is part of the runtime cache
key).

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

### Differences from Cranelift

Running out of stack is a panic (`panic: stack exhausted`, then abort) on
both backends, on the process stack and on each task stack. Every stack ends
in an unmapped guard, generated code probes each page of a frame larger than
a page so that it cannot step over the guard, and the runtime handles the
fault on a separate signal stack. It reports a fault as exhaustion only when
the address lies in the frame being set up (from 64 KiB below the
interrupted stack pointer to two pages above it) and below the frame the
process started in. Every other fault, and any SIGSEGV or SIGBUS sent by
another process, gets its default action.

Limits: the handler exists on Linux x86-64 and AArch64, which is also where
the native backends run. Only generated code is probed. The C runtime's own
frames are about 1 KiB at most, but a libc built without stack-clash
protection could, in principle, enter a frame larger than a page at the very
end of a task stack and step over its single guard page. With an unlimited
stack (`ulimit -s unlimited`) a runaway recursion ends when memory does.

A recursion stays a recursion on both backends. LLVM functions carry
`"disable-tail-calls"="true"`, which stops it from running a tail call, or a
recursion with an accumulator, as a loop; so a runaway recursion panics on
both instead of panicking on one and spinning on the other. The depth a
program can reach still differs with frame size, which is not promised. The
price is that tail-recursive code does not become a loop in release builds;
write the loop.

## Validation

- `KUSH_BACKEND=llvm cargo test --workspace` replays the entire suite on the
  LLVM backend: 1,708 tests pass on both backends and with `KUSH_BACKEND=llvm-release` (LLVM 18.1.3, 2026-11-11).
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
| Kush, Cranelift `--release` | 117 |
| Kush, LLVM, immediate checks | 59 |
| Kush, LLVM | 58 |
| Rust checked | 58 |
| Rust | 54 |

`benchmarks/checked-loops`, 4,096 elements × 200,000 repetitions:

| Kernel | Cranelift | LLVM immediate | LLVM | Rust checked | Rust | LLVM native | Rust native |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| sum | 668 | 230 | 147 | 223 | 72 | 57 | 44 |
| dot | 1113 | 447 | 476 | 441 | 357 | 193 | 149 |
| scale, then sum | 1768 | 659 | 475 | 661 | 398 | 229 | 229 |

Reading these:

- LLVM is 2 to 4.5 times faster than Cranelift `--release` here.
- With checks kept, Kush beats Rust built with overflow checks on the sum
  and the scale, and equals it on the dot product: that loop keeps immediate
  checks on this target, and its ten instructions are the same, one for
  one, in both LLVM columns and in checked Rust. The spread between those
  three dot numbers is this machine's run-to-run spread (pinned runs of one
  binary vary by as much). Sticky flags and a magnitude certificate were
  both measured for this loop and are slower than branches without a
  64-bit vector multiply. Against unchecked Rust it is between 7% and
  2× slower. The sum is the worst case: its certificate costs four SSE2
  instructions per vector next to Rust's one add.
- These numbers are with loops checked in chunks of 65,536 iterations (see
  [deferred-overflow.md](deferred-overflow.md)); chunking itself costs
  nothing measurable here.
- `feature-pipeline` is within 7% of Rust. Stating ownership facts took it
  from 69 ms to 61 ms on the earlier measurement run. What remains is `Vec.push`: a Kush vector keeps its
  length and encoded capacity in the heap block, so each push loads both and
  decodes the capacity (14 instructions per element against Rust's 8).

Build time for the same two programs, median of seven in milliseconds:

| Build | feature-pipeline | checked-loops |
| --- | ---: | ---: |
| Kush, Cranelift | 55 | 55 |
| Kush, LLVM `--release` | 141 | 155 |
| `rustc` debug | 137 | 108 |
| `rustc -C opt-level=3` | 241 | 186 |
| Kush, Cranelift, no proof cache | 63 | 66 |
| Kush, LLVM `--release`, no proof cache | 135 | 164 |

A development build takes about half of a `rustc` debug build's time. An
LLVM release build takes 60% to 85% of `rustc -C opt-level=3`, and is not
faster than a `rustc` debug build. Three things make that possible. The runtime is
precompiled, so only program code goes through LLVM. Only functions the
program can reach are lowered and compiled. And the proof search, which used
to be nearly all of the front end, is both faster and
[remembered between builds](proof-cache.md); the last two rows show a build
that remembers nothing. These are small programs; nothing here measures a
large code base, where Kush still checks and compiles the whole program on
every build.

## Limits

- Linux x86-64 only, as for Cranelift.
- Apart from exclusive parameters, function parameters and loaded words are
  still integers; only values with a local pointer origin get pointer forms.
- `--target-cpu native` code runs only on machines with the build machine's
  features.
- Debug information is not emitted.
