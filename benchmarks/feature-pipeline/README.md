# Feature pipeline: Kush versus Rust with Cranelift

A small, runnable scalar batch-processing project. It combines five Kush
features in one real computation, implements the same computation in safe
Rust, and measures the actual binaries. No foreign library performs the Kush
workload. The results are specific to this workload and toolchain, not a
language ranking or a formal safety audit.

## Run

Requirements: current Kush, Python 3, GNU `/usr/bin/time`, `cc`, and a Rust
nightly with `rustc-codegen-cranelift-preview` installed. `objcopy` enables the
native-code erasure comparison. The harness fails if Cranelift is unavailable;
it never falls back to LLVM.

```sh
python3 benchmarks/feature-pipeline/run.py --kush /path/to/kush
```

Outputs: `results/latest/results.json` (every sample, diagnostics and build
command), `report.md`, and an interactive `report.html`. Generated variants and
binaries live under ignored `build/`. Override `--sizes 262144:8,2097152:4`,
`--repetitions 7`, `--warmups 2`, `--cpu N`, or `--output PATH` as needed.
Sizes are bounded to 1..8,000,000 elements and 1..32 batches. A zero-batch run is
reserved for allocation-baseline measurement. The benchmark is single-threaded;
performance measurements run on this laptop, not across different Boat hardware.

The checked-in [laptop snapshot](sample-results/laptop-2026-11-03/report.md)
contains the first full run, with [raw JSON](sample-results/laptop-2026-11-03/results.json)
and an [interactive chart](sample-results/laptop-2026-11-03/report.html).

Run the ordinary Kush project independently:

```sh
kush check --manifest-path benchmarks/feature-pipeline/kush/Kush.toml
kush test --manifest-path benchmarks/feature-pipeline/kush/Kush.toml
kush run --manifest-path benchmarks/feature-pipeline/kush/Kush.toml -- 2097152 4 1
# Arguments: elements, batches, mode (0 staged / 1 fused).
```

The Rust project can also use Cargo. Its nightly-only manifest explicitly
selects Cranelift in both profiles, with overflow checks enabled:

```sh
cargo +nightly run --release --manifest-path benchmarks/feature-pipeline/rust/Cargo.toml -- 2097152 4 1
# Modes: 0 staged / 1 manual fusion / 2 iterator chain.
```

The measurement harness invokes rustc directly with
`-Zcodegen-backend=cranelift -Copt-level=3 -Coverflow-checks=yes -Cpanic=abort`
and also builds an O0 control. It uses no Cargo dependency cache for these
standalone binaries. Cargo builds should use a separate target from any mbx
build; repository work uses mbx when building through Cargo.

## What the computation does

For every batch:

1. Issue a completion ticket containing an authorized calibration key.
2. Allocate one `Vec<i64>` at its final capacity and initialize element `i`
   with `i & 65535`.
3. Transform each element with `(x & 65535) ^ (x & 255)`, then `x ^ 23130`.
4. Borrow the vector as a slice and sum its elements with checked arithmetic.
5. Consume the ticket and add its key to the checksum.

A Python oracle computes the expected checksum independently, using the
65,536-element periodicity. Native results are checked for every measured
sample. Small cases also agree with Kush's reference evaluator.

The configured bounds ensure valid runs do not overflow signed 64-bit sums.
That is a harness/input constraint, **not a theorem proved by the erased
witness**. Both implementations retain runtime overflow and bounds checking.

## Kush-specific contracts

| Feature | Actual use | What it does not establish |
| --- | --- | --- |
| Usage grade `@[2]` | `scrub` must use its parameter exactly twice | Algorithmic correctness or two machine loads |
| Zero grade `@[0]` | `issue` receives erased audit metadata with no ABI payload | Ignoring effects in an initializer |
| Linear owning result/parameter `@[1]` | Issued `Box<i64>` ticket must be consumed by `finish` | Recovery/finalization after an abort |
| Kernel-checked erased proof | `AuthorizedKey<key>` has a constructor only for key 23130 | Bounds-check removal, arithmetic theorems, or general runtime authentication |
| Borrowing | `checksum` reads a slice while the vector remains owned by its caller | A formal proof of the whole compiler |
| Effects | `#[noalloc]`/`#[nosuspend]` on transforms/checksum | No allocations in the entire batch; initialization allocates |
| Automatic fusion | Nested `Vec.map_in_place` calls with pure callbacks | General effectful/recursive fusion |

The zero-graded parameter is erased at the `issue` boundary. Its wrapper's
argument is an ordinary scalar; this benchmark does not claim unrestricted
forwarding/inference of zero grades.

## Comparisons and controls

- **Kush fused:** all contracts and automatic nested-map fusion.
- **Kush plain:** same valid computation with use grades, effect contracts and
  erased binders removed. The script mechanically generates the source and
  asserts those contracts were removed. It compares native `.text` hashes.
- **Kush staged:** nested maps are replaced by separate statements everywhere.
  The stats build must report zero static fusion sites, versus one for fused.
- **Rust manual O3:** a single in-place loop, giving Rust an explicitly fused
  implementation instead of relying on optimizer inference.
- **Rust iterators O3:** `into_iter().map(scrub).map(tag).collect()`. Iterator
  composition is already one traversal; it is not a naive two-allocation straw
  man. Allocation instrumentation confirms buffer reuse on this toolchain.
- **Rust staged O3:** two separate in-place loops.
- **Rust manual O0:** same loop, lower-optimization control.

All variants preallocate exactly one vector per batch. The algorithm, element
width, input, arithmetic checks, checksum and one ticket allocation are matched.

Rust's whitelist is a private-field `AuthorizedKey` with a safe `standard()`
constructor. It enforces this **particular** policy without dependent types.
`Audit` is a zero-sized type. Rust's affine `Ticket` is `#[must_use]` and has a
runtime Drop guard requiring `finish`; valid benchmark runs always finish it.
The guard costs a flag/check per batch, not per element, and is included in
Rust timings. A scoped Rust API could instead own finalization internally; this
is not a claim that Rust cannot implement safe resource protocols.

## Measurement method and fairness limits

- Two workload sizes; two warmups and seven measured repetitions by default.
  Implementation order is shuffled in each block with a recorded fixed seed.
- A fresh child process for each sample, pinned to one allowed logical CPU.
  Other laptop activity, thermal state and CPU frequency are not controlled.
  Every raw observation is retained; min/max are reported, not a claim of
  statistical significance from seven runs.
- Wall time uses Python's high-resolution clock around GNU time and process
  creation. It **includes startup, argument handling, initialization, transforms,
  checksum, allocation/free, printing and teardown**. It is not a map-kernel or
  cycles-per-instruction measurement. GNU time's user/system seconds are also
  recorded but have coarser precision.
- Peak RSS comes from GNU time in KiB. It includes runtime, code pages and
  allocator retention; it is not live heap bytes. Small RSS differences should
  not be advertised as a language memory advantage.
- Allocation diagnostics use separate binaries, excluded from timing. Kush's
  whole-process **logical object** counters are recorded with a zero-batch
  baseline; only allocation/deallocation counts are baseline-subtracted. Peak
  values are never subtracted. Its fusion count is static sites, not elements
  or batches executed. Rust's counting System allocator observes **requested
  blocks/bytes** only inside the batch window. Those are different definitions;
  do not compare total Kush logical allocations directly to Rust system calls.
  Both show the same two-allocation-per-batch shape and balanced cleanup.
- The counting allocator's unsafe forwarding code is isolated in
  `rust/allocation.rs`; the production Rust workload uses only safe Rust.
- Both program crates use Cranelift, but not an identical compilation pipeline.
  Kush uses its current default Cranelift settings and a cc-built C runtime;
  Rust uses recorded O3/O0 flags, MIR transformations, and installed prebuilt
  standard libraries (potentially LLVM-built). Backend versions can differ.
  Toolchain versions, backend library hash, binary hashes and build commands are
  recorded. **These results do not predict ordinary LLVM Rust release builds.**
- Build times are single warm standalone invocations, including linking and
  Kush's C runtime compilation. They are not statistically sampled clean
  bootstrap/dependency-build comparisons.

## Safety checks, not a score

The harness compiles deliberately invalid fixtures and checks the intended
error, not merely a nonzero exit. This is a small regression matrix, not
fuzzing, sanitizers, a soundness proof or an overall security ranking.

| Misuse | Kush | Equivalent Rust surface |
| --- | --- | --- |
| Use after move | Compile error | Compile error |
| Invalidate a live borrowed slice | Compile error | Compile error |
| Overlap exclusive borrows | Compile error | Compile error |
| Forge unauthorized key | Kernel/type error | Private constructor error |
| Observe erased audit payload | Grade error | ZST cannot be returned as an integer |
| Violate exact use count | Grade error | No built-in use-count contract; accepted |
| Discard unfinished ticket explicitly | Linear error | Accepted, then runtime guard aborts |
| Allocate inside declared noalloc function | Effect error | No corresponding built-in effect restriction; accepted |

An extra Rust fixture confirms `mem::forget(ticket)` compiles and bypasses the
runtime guard. This is a safe-Rust resource leak/protocol bypass, not undefined
behavior. Kush has no corresponding safe forget operation in this API.
The ZST/private-newtype cases use Rust API design to implement the concrete
property; they do not pretend Rust has Kush's general graded/dependent syntax.

## Code quality observations

Both implementations have the same named steps: `issue`, `scrub`, `tag`,
`checksum`, `finish`, `batch`.

- Kush puts exact usage, finalization, proof and effect obligations directly in
  signatures, and its nested maps get checked automatic fusion. Refactoring
  that violates those declared contracts is rejected. It also needs explicit
  effect rows and more manual CLI/error plumbing in this small standard library.
- Rust's standard iterators and sealed newtypes are concise and idiomatic, and
  its borrow/move diagnostics cover the shared memory-safety cases. Exact-use
  and noalloc restrictions are not part of these built-in signatures; the
  explicit completion protocol needs the additional runtime guard.
- Source line counts are reported for transparency only, with file lists and
  instrumentation excluded. Formatting density, library support and the chosen
  guard design affect them. **Fewer lines are not a code-quality score.**
- No automatic "quality" or "safety" winner is derived from these metrics.

## Observed laptop results (2026-11-03)

AMD Ryzen 5 PRO 5675U, pinned logical CPU 11. Main case: 2,097,152 elements,
four batches, seven measured repetitions:

| Implementation | Median wall ms | Median peak RSS MiB |
| --- | ---: | ---: |
| Kush automatic fusion | 161.132 | 18.086 |
| Kush without contracts | 160.972 | 18.117 |
| Kush two passes | 171.103 | 18.191 |
| Rust Cranelift O3 manual fusion | 60.918 | 18.355 |
| Rust Cranelift O3 iterators | 192.795 | 18.359 |
| Rust Cranelift O3 two passes | 73.317 | 18.375 |
| Rust Cranelift O0 manual fusion | 214.514 | 18.344 |

On this run Rust's best loop is about **2.65× faster than Kush**, while Kush
is about **16% lower in wall time than this Rust iterator implementation**.
Kush fusion lowers wall time about **5.8%** versus its own two-pass control.
The two Kush fused binaries have **identical `.text` bytes** with/without the
contracts; their timing difference is not evidence of contract overhead.
Memory footprint is comparable. These conclusions are intentionally limited
to this scalar pipeline and these exact builds; no causal profiling or broad
performance superiority claim is made.

Sources for backend selection:
[Rust codegen-backend flag](https://doc.rust-lang.org/beta/unstable-book/compiler-flags/codegen-backend.html),
[rustc_codegen_cranelift](https://github.com/rust-lang/rustc_codegen_cranelift).


## Release optimization study

The original snapshot above uses Kush's unchanged default build mode. The new
native release mode can be measured independently:

```sh
python3 benchmarks/feature-pipeline/optimize.py --kush /path/to/new/kush
```

This builds default, speed-only, inline-only and release Kush binaries, plus
Rust's manual/iterator Cranelift controls. Separate clock-probe binaries measure
initialization, transformation and checksum. They are excluded from headline
end-to-end samples. See [native optimizations](../../docs/native-optimizations.md)
for exact eligibility, API/CLI controls, validation and remaining limitations.
