# Owned JSON document editor: allocation and memory comparison

A schema-specific JSON editor, implemented in Kush and Rust. Rust data editing
uses safe APIs; the shared probe hooks have explicit unsafe C-ABI calls. It parses the same tiny seed, builds a corpus of independently owned
objects, alternates large/small edits, serializes each object, drops the large
corpus, builds a 16-document corpus, then releases all workload owners.

The schema is `{id, revision, text, children}`. An object owns a boxed metadata
node, text bytes, and a child-number vector. It is a shallow owned tree, not a
JSON DOM with arbitrary recursive node shapes. The seed is fixed to
`seed.json`; generated text is ASCII A–Z, so serialization needs no escape
handling. This is not a general-purpose JSON serializer or editor UI. Undo
history and arbitrary nested edits are not implemented.

## Four controls

- **Kush rebuild:** allocate new text, children and metadata before dropping the
  old fields. Edit traversal keeps the outer document vector.
- **Kush reuse:** `Box.reuse` for metadata, `Bytes.clear`/capacity checks for text,
  `Vec.clear`/`Vec.reserve` for children. Retain capacity through small edits.
- **Rust rebuild:** construct replacements before dropping the old fields, with
  the same initial capacities and push-based growth as Kush rebuild.
- **Rust deliberate reuse:** overwrite boxed metadata, clear buffers, and reserve
  the target size before filling. Retain capacity through small edits.

Reuse controls reserve the known target size; neither relies on repeated small
reallocations to reach it. Kush has no `Bytes.reserve`, so its first text growth
replaces the empty buffer; Rust uses `Vec::reserve` and can grow in place.
These are idiomatic safe operations, not forced identical allocator algorithms.

Every edited object increments its revision. Odd revisions use 512 text bytes
and 32 children; even revisions use 16 bytes and four children. The default
31 edits end with large objects. The final serialization order and checksum
must agree with an independent Python JSON oracle for every run. Small cases
also compare full JSON bytes and decoded values, and run through Kush's
reference evaluator with only the foreign no-op probes removed.

## Run

Linux/glibc, Python 3, GNU `/usr/bin/time`, `cc`, `mbx`, and a Rust nightly with
`rustc_codegen_cranelift` are required. The Rust `serde_json` dependency must be
available for Cargo's offline build. There is no silent LLVM fallback.

```sh
python3 benchmarks/json-memory/run.py --kush /path/to/kush
# Quick validation, including allocator-probe self-test:
python3 benchmarks/json-memory/run.py --kush /path/to/kush --validate-only
# Smaller experiment:
python3 benchmarks/json-memory/run.py --sizes 256 4096 --rounds 15 --repetitions 7
```

Defaults: 256 / 4,096 / 16,384 documents, 31 edit batches, seven samples after
two warmups, shuffled variant order, one pinned CPU. Rust builds use mbx,
two jobs, a dedicated target under `~/.cache/kush-json-memory-rust`, Cranelift,
opt-level 3, overflow checks, panic abort, and x86-64 baseline. Kush uses
`--release`. Builds finish before the measurement loop starts.

Binaries are also small NDJSON-producing programs:

```sh
benchmarks/json-memory/build/kush-plain 3 2 1 1
benchmarks/json-memory/build/rust-plain 3 2 1 1
# Arguments: document count, edit batches, mode (0=rebuild, 1=reuse), emit JSON.
# The last stdout line is a checksum, following the document lines when emit=1.
# After the harness builds the probe, the Kush project also runs directly:
kush run --manifest-path benchmarks/json-memory/Kush.toml --release -- 3 2 1 1
```

## What the measurements mean

Three separate binaries per language keep instrumentation out of headline
measurements:

1. **Plain:** no-op phase markers; wall time and GNU time peak RSS. Parsing,
   initial construction, all edits, serialization, shrinking and destruction
   are included. Execution is a fresh process for every sample.
2. **Allocation trace:** GNU linker `--wrap` hooks for malloc/calloc/realloc,
   aligned_alloc/posix_memalign/free, sharing exactly the same C recorder across
   languages. Records client-visible successful libc allocator requests,
   requested bytes, usable bytes (`malloc_usable_size`), and live/peak totals.
   Reallocations distinguish in-place and moved results. This is **not** a count
   of OS mmap/brk calls, fresh physical blocks, or glibc's internal allocations.
   A realloc's hidden transient peak is not observable from these hooks.
3. **Phase RSS:** no allocation recorder; snapshots of `/proc/self/status`
   VmRSS/VmHWM. These include all process residency, including libc-retained
   pages. Phase values are medians of three independent diagnostic runs (raw frames
   retained); headline peak RSS is a median across the plain timing runs.

The allocation recorder uses a fixed BSS table and performs no bookkeeping
allocations. Its own table inflates trace-process RSS, so that RSS is never
used. `probe_self_test.c` checks known malloc/calloc/realloc sizes, refusal,
peak and final-live accounting before any experiment. Hooks see static-object
and executable relocations, not hidden calls inside shared libc. Before-workload
allocation baseline is recorded. Allocations after `memory_end` are ignored,
but releases of tracked pointers remain observed. An atexit report sees Kush's
normal-exit pool drain; Rust startup allocations are reported separately from new workload requests.
Every allocation born inside the workload must be released by the final report,
and the harness asserts zero live workload bytes/blocks. This also checks that
Kush's retained blocks are released during its normal-exit pool drain.

Stages: 0=before parse; 1=seed parsed/corpus loaded; 2=edits done;
3=large corpus serialized/dropped, seed still live; 4=small corpus loaded;
5=all workload owners dropped, before Kush's normal-exit pool drain;
6=allocation trace at exit, after that drain. Plain binaries make the same
marker calls but perform no tracing or snapshots.

Kush's stable logical `allocation-stats` and physical `allocator-pool` reports
are retained separately in the raw data. A logical box reuse, a pool hit, a libc
allocation request, and an OS page allocation are different events.

## Fairness and interpretation

- Both languages use Cranelift, but have different frontends, optimization
  pipelines, layouts and standard libraries. This says nothing about Rust LLVM
  release performance. Rust's prebuilt standard library may use LLVM.
- Kush `std.json` and Rust `serde_json` parse the same small seed. Their parser
  allocations differ and are included, so this is not a parser comparison or
  a perfectly identical representation experiment.
- Kush has thin heap handles, word-granular record tags, runtime buffer headers,
  16-byte allocation headers, padding and a bounded 1 MiB pool. Rust has inline
  Vec descriptors and normal Box allocations. Physical metrics include these
  differences rather than pretending payload sizes are the same.
- Kush can reuse the document vector when consuming it into scalar hashes.
  Rust consumes the vector directly while accumulating the checksum; neither
  allocates another output vector. Actual compiler decisions are part of the
  experiment, not assumed from source spelling.
- Less allocation churn can coexist with **more live or retained memory**.
  Rust reuse is the important control; outperforming rebuild-only Rust does
  not establish an advantage over deliberate Rust memory management.
- RSS after dropping a document may remain high in either language. No forced
  malloc_trim, alternate allocator, cache flush or memory-release claim is used.
- Timing includes serialization and short-process startup. It is secondary to
  this memory experiment. Thermal state and background load still matter.

Raw samples, phase frames, allocator reports, commands, compiler versions and
binary/source hashes are written to `results/latest/`, with a standalone
interactive `report.html` and `report.md`. Generated build/results directories
are ignored; selected measured snapshots can be committed under sample-results.

## Measured laptop checkpoint

The [2026-11-03 analysis](sample-results/laptop-2026-11-03/analysis.md) records
the full three-size experiment. Reuse reaches essentially the same allocator
request count in both languages. On the largest case, Kush reuse uses more
peak requested heap and RSS than Rust reuse, while finishing sooner. The
analysis reconciles the requested-heap gap with document layouts and pool
retention; it does not infer OS allocation counts from libc requests.

The content-hashed probe object filenames force Cargo to relink if the C probe
changes. `--skip-build` checks source/compiler/binary hashes before accepting
existing binaries. Raw data records both the measurement script hash and, when
regenerated later, the report-generator hash.

The current pool also limits each size class to 64 retained blocks. The original
laptop snapshot predates this change and used 32-byte allocation headers; its
layout accounting is historical. A preserved-binary comparison can be run with
`--previous /path/to/baseline`, holding the original `kush-plain`, `kush-trace`,
`kush-rss`, and their `manifest.json`. The harness verifies the hashes and
workload sources, reruns those binaries in the same cohort, and records the
previous compiler identity separately.

For runtime revisions, `--previous-compiler /path/to/old/kush` rebuilds the
unchanged workload with the old compiler and the same current probe objects as
the new controls. This avoids comparing different instrumentation revisions.
The tracer reuses a hash-table tombstone immediately for a fresh allocation
address; allocator uniqueness guarantees that no live key is duplicated. This
keeps heavy reallocation tracing from scanning a long history of freed slots.
Tracer time is excluded from application timing and RSS measurements.
