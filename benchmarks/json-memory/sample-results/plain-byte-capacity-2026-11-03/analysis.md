# Plain byte capacity: keeping the header savings off the hot path

Compiler source checkpoint: `0d77048`.

This follow-up retains small-buffer header elision and the same source language
contracts. It changes native byte-buffer representation and release codegen;
application sources and Rust controls are unchanged.

## Mechanism and evidence

A short `gprof` sampling run (16,384 documents, 63 edits) put about 74% of
samples in the content-generation function and about 4.5% in the capacity
helper. This is coarse sampling, not a precise per-instruction attribution.
Hardware performance counters were unavailable on this laptop. Disassembly
confirmed the content-generation append loop decoded capacity with a move,
mask, sign test and conditional move before its capacity comparison.

Bytes and String now retain a plain logical-capacity word. Unlike vectors,
they never change element width or shrink capacity. Their physical class can
therefore be recovered exactly as `round_up(16 + capacity, 16)` at the cold
growth/release boundary. The hot append loop loses its tag decode. Vectors
retain their class metadata to support narrowing maps and later growth.
Release-mode length, capacity, checked byte reads and clear operations are
also lowered directly into Cranelift; String byte length/read share that path.
Bounds checks, byte-value checks, ownership and allocation-failure semantics
remain in force. Scalar UTF-8 operations retain their runtime implementation.

`encoded-capacity.asm` and `plain-capacity.asm` preserve the relevant function
disassemblies. `sampled-profile.txt` preserves the sampling result. The
intermediate access-inlining-only candidate is retained in the raw timings;
it is not presented as an independently established optimization.

## Measurement scope

All controls use the existing inline-metadata JSON editor with deliberate
reuse, 16,384 documents and 31 edits. Both language backends use Cranelift;
Rust's prebuilt standard library may contain LLVM code. Binaries are hash
verified and every measured checksum is checked against the Python oracle.
No compilation runs during a timing cohort. CPU and RSS are per-child wait4
measurements. RSS is resident memory, distinct from requested heap.

## Boat: matched confirmation

The resumed VM ran on a **Ryzen 7 9700X**, not the Ryzen 9 9950X of the earlier
report. Absolute times from those two hosts must not be compared. All five
controls below ran on the same new host, pinned to CPU 0, shuffled each round,
with nine measured samples after one warmup. Compilation/checks finished before
timing began. Load average decayed from 3.01 to 2.50 after the gate; it was not
an all-zero-load host. Raw samples vary and their ranges overlap, so these are
median workload results, not a universal ranking or a confidence interval.

| Control | Median wall ms | Median CPU ms | Median peak RSS KiB |
|---|---:|---:|---:|
| Original Kush (headers) | 317.191 | 316.482 | 16,128 |
| Previous headerless Kush | 343.794 | 343.092 | 15,616 |
| Rust CLIF | 387.777 | 387.301 | 16,000 |
| Intermediate: inline access only | 294.287 | 293.755 | 15,616 |
| New: plain capacity + inline access | 261.768 | 261.292 | 15,616 |

Relative to previous headerless Kush, the new version takes **23.9% less wall
time and 23.8% less CPU time**, with unchanged peak RSS. Against original
header-bearing Kush it takes **17.5% less wall time / 17.4% less CPU time**,
with **3.2% less peak RSS**. Against Rust CLIF it takes **32.5% less wall/CPU
time**, with **2.4% less peak RSS**, on this inline JSON workload.

The new version is faster than original Kush in eight of nine corresponding
shuffled rounds, and faster than Rust in all nine. The first measured new-Kush
sample is slow; it remains in the data and summary. No samples were removed.
The intermediate access-only candidate also improves in this Boat cohort;
plain capacity removes additional hot-loop work. This is a combined measured
change, not proof that either optimization benefits every program.

[Raw Boat samples and binary identities](boat.json).

## Laptop: noisy supporting control

Five samples after one warmup on CPU 7 of Ryzen 5 PRO 5675U. Background proof
jobs stayed active; load was approximately 7.8 at both ends. The new version's
median CPU is **757.2 ms**, versus original Kush **853.8 ms**, previous
headerless Kush **736.5 ms**, and Rust **1,102.6 ms**. Thus it beats original
Kush here but remains **2.8% slower than previous headerless Kush** in this busy
cohort. This does not establish an improvement on every processor. Its peak RSS
is 16,104 KiB, versus previous headerless 16,052, original 16,576 and Rust
16,272 KiB. Small RSS differences include code pages/allocator residency.

The intermediate access-only version is slower locally even though faster on
Boat. Both exploratory cohorts are kept, with all samples; no laptop result is
used to overwrite or explain away the Boat findings.

[Raw laptop cohort](laptop.json) · [Earlier access-only experiment](inline-access-only-laptop.json).

## Allocation invariants

The separate allocator trace is byte-for-byte equivalent on its reported
allocation fields to the previous headerless implementation: peak requested
heap **13,638,416 bytes**, **81,935 allocator requests**, cumulative requested
bytes **38,536,096**, and zero live allocations/bytes after exit. Logical
allocation stats remain balanced. The original header-bearing implementation
peaked at 14,164,688 requested bytes, so the 526,272-byte saving remains.
Rust's prior matched trace is 13,633,480 bytes: Kush remains 4,936 bytes (0.036%)
higher, essentially tied rather than a strict requested-heap win. Allocation
tracing is separate from plain timing and does not claim to measure all OS
allocations. The boxed layout was not rebenchmarked in this follow-up.

## Validation

- Full Boat gate: **1,170 tests passed**, zero failed; formatting and strict
  workspace/all-target Clippy passed.
- Local focused tests: allocator containers 34, allocator pool 10, FFI 15,
  headerless buffers 5, host APIs 10; all passed.
- Direct runtime test covers every initial capacity 0 through 1100, content,
  alignment, small/large transition, full-width positive capacities, retained
  vector capacity, fallible refusal, successful growth, drain and double release.
- Current runtime probe passed AddressSanitizer/UndefinedBehaviorSanitizer with
  leak detection and strict C syntax checks with stats/tasks enabled.
- Eight canonical JSON/oracle cases (both rebuild/reuse) passed. Accepted byte
  paths compare default and release native output/stats with the evaluator;
  negative/upper-bound indices, capacity 65,537, clear and reserve behavior are
  covered.

The validated compiler was installed atomically; its SHA-256 is
`bcb2bd5dbfb5290ef067de0bbe86cc8aad4d5f6b355c5b9fafbff1991165ae5e`.
The installed niche example prints `42`, `42`, `65`. Boat was stopped after
the gate and measurement run.

## Laptop slowdown follow-up: code layout, not extra work

On the laptop (Ryzen 5 PRO 5675U), this build ran about 4% slower than the
previous headerless build, while Boat showed a large gain. Disassembly showed
the hottest loop has **identical instructions** in both builds; inlining
elsewhere only moves it to a different address. That points to instruction
fetch/layout sensitivity on the older core, not to more work per iteration.

Two candidate fixes were measured with hash-verified binaries:

| Candidate | Laptop median wall ms (CPU 7, 9 reps) | Boat median CPU ms (9700X, CPU 0, 9 reps) |
|---|---:|---:|
| Previous headerless Kush | 504 | 340 |
| This build (broad inlining) | 522 | **272** |
| Capacity-only inlining | **503** | 285 |
| Broad inlining + 32-byte function alignment | 526 | not run |

Forcing 32-byte function alignment did not help, so this is not a simple
function-alignment effect (Cranelift has no loop-header alignment option).
Capacity-only inlining removes the laptop regression but gives back about 5%
of the Boat gain; neither variant wins on both hosts. The broad inlining is
kept: its gain on the newer core is larger than its loss on the older one, and
the loss comes from placement rather than added instructions. Boat wall times
in this cohort were noisy right after VM resume (load 1.4 → 5.5), so CPU time
is the comparison column. Raw data: `selective-inlining-boat.json`,
`selective-inlining-laptop.json`.

## Resolution: inline everything except checked indexed reads

Splitting the inlining by operation isolated the cause. Every build that inlines
the checked byte read (`Bytes.get`/`String.byte_at`) is slow on the laptop, and
every build without it is fast:

| Inlined byte ops | Laptop median CPU ms | Boat median CPU ms |
|---|---:|---:|
| none (previous headerless) | 509 | 311 |
| capacity only | 507 | 252 |
| capacity + length + clear (**adopted**) | **499** | 246 |
| capacity + length + read + clear (previous) | 531 | **243** |
| capacity + length + read | 531 | not run |
| capacity + read + clear | 539 | not run |

The adopted set keeps checked reads as a runtime call. It is the fastest
laptop build and stays within about 1% of the best Boat build, so it removes
the laptop regression while keeping essentially all of the Boat gain. The Boat
cohort ran under high host load (1-minute load ≈16 → 14) but all builds were
shuffled within the same rounds. Raw data: `inline-subsets-laptop.json`,
`inline-subsets-boat.json`.
