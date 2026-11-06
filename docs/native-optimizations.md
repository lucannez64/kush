# Native release optimization

Kush's native backend has an explicit release mode. Default builds retain the
existing Cranelift `none` setting and ordinary callback calls. Source checking,
proof checking, grades, ownership and borrowing run in either mode.

```sh
kush build program.kush -o program --release
kush run program.kush --release -- argument
kush build --manifest-path path/Kush.toml --release
kush run --manifest-path path/Kush.toml --release -- argument
```

These flags apply to native build/run, not check/eval/test. Flags after `--`
belong to the program. Source-file builds retain their existing
`FILE -o OUTPUT [options]` argument order.

## Independent controls

| Flags | Cranelift optimization | Scalar map callback inlining |
| --- | --- | --- |
| none | `none` | off |
| `--opt-level speed` | `speed` | off |
| `--inline-scalars` | `none` | on |
| `--release` | `speed` | on |
| `--release --no-inline-scalars` | `speed` | off |

`--release` also inlines small direct calls (below); `--inline-calls` and
`--no-inline-calls` set that independently.

`--opt-level none` explicitly selects the unoptimized backend. Controls are
processed in argument order; later flags override earlier choices. Invalid or
missing option values fail before building. The C runtime still uses `cc -O2`
in every mode; release changes the Cranelift-generated user code.

## Restricted callback inlining

The checked `VecMap` lowering recognizes a deliberately bounded subset:

- a directly known `FnValue`, without captures, once/linear calling mode, or
  effects in its callable signature;
- one ordinary physical `i64` parameter and an `i64` result (nonzero usage
  grades such as `@[2]` remain allowed);
- one immutable, unpinned parameter local, no additional locals, statements,
  resources, or erased result;
- a tail expression containing only the parameter, `i64` constants, and `&`,
  `|`, `^`, bounded to 32 expression nodes.

A validated expression plan substitutes the loop's current scalar value for
that parameter. It does not lower a callee body using caller-local indices.
The original vector and callback expressions are still evaluated once in the
same order. Unsupported callbacks retain the existing ABI/call/drop path.
There is no partial inlining after a failed eligibility check.

This applies to a single map, automatically fused maps, and explicit map
chains. It does not create additional fusion sites or change allocation-stats
format/counters. The source checker already enforces the callback's grade and
effect contracts before this code generation step.

For the feature-pipeline benchmark, the resulting loop performs a masked load,
XOR and store directly. The inlined expressions cannot install handlers, so
there are no callback handler-depth/restore calls in the loop. This is not a
general pass removing handler frames from arbitrary functions; normal function
frames and dynamic handlers retain their previous behavior.

Owning or borrowed payloads, aggregate values, narrower integers, floats,
booleans, calls, branches, local bindings, arithmetic/shift checks and larger
expressions all use the fallback in this initial implementation. General
inlining and unchecked bounds-check elimination are not implemented.

## Library API

`native::CodegenOptions::release()` selects both controls. Set
`optimization: native::Optimization::{None, Speed}` and
`inline_scalar_callbacks` independently for ablations.

```rust
native::build_with_codegen(
    &program, &output, stats, &links, native::CodegenOptions::release(),
)?;
```

Existing `native::build`, `build_with_stats`, and `build_with_options` keep their
old defaults. Project `BuildOptions` and `RunOptions` now carry a `codegen`
field; struct-literal callers should supply it or use `..Default::default()`.
Native output replacement and link-input validation remain unchanged.

## Validation and measurements

`tests/native_release.rs` compares reference output and allocation diagnostics
against all four combinations of backend optimization/inlining. It covers
negative integers, grades, erased proofs, linear resources, borrowed data,
callback expression effects, owning cleanup, aggregate intermediate ABIs,
booleans, indirect/delegating bodies, dynamic handlers, checked failures, CLI
flag parsing and argument forwarding. A machine-code test confirms that
inlining removes callback call instructions with backend optimization disabled.

The reproducible ablation/phase probe is:

```sh
python3 benchmarks/feature-pipeline/optimize.py --kush /path/to/new/kush
```

Its end-to-end measurements use fresh, CPU-pinned processes and shuffled
implementation order. Clock probes are built separately and never used for
headline timings. They distinguish vector initialization, transformation, and
borrowed checksum; they do not time initialization/output as part of the map.
Keep comparisons within one cohort: laptop frequency/temperature/background
load can shift absolute numbers between runs. See the generated JSON for every
sample and the benchmark README for other fairness limits.

### Laptop checkpoint (2026-11-03)

At compiler checkpoint `a4060de`, 2,097,152 elements × four batches, seven
shuffled samples after two warmups: default Kush 161.274 ms, speed-only
157.479 ms, inline-only 77.645 ms, release 74.736 ms, Rust Cranelift O3 manual
fusion 61.495 ms. Release reduces whole-process time by 53.7% versus default;
it remains 21.5% slower than the manual Rust control. Median RSS stays near
18 MiB for every implementation.

Separate instrumented probes measure the transform at 7.801 ms for Kush
release versus 16.781 ms for Rust manual fusion. Initialization (49.171 versus
29.618 ms) and checksum (15.944 versus 9.563 ms) remain the next targets.
This is one workload, not a general performance ranking. Raw samples, commands,
source hashes, and phase data are in
`benchmarks/feature-pipeline/sample-results/release-2026-11-03/`.

Full integration validation of compiler checkpoint `a4060de`: Boat passed
all 1,141 workspace tests and strict workspace/all-target Clippy; formatting
also passed. The first test attempt stopped on a missing cached dependency
build artifact; the retry completed successfully and the sandbox stopped with
its snapshot preserved. Logs: `/tmp/kush-boat-native-release-full.log` and
`/tmp/kush-boat-native-release-retry.log`. Local release regression and
machine-code tests also passed using mbx with two jobs.

## Vector access (2026-11-06)

With speed optimization, `Vec.len` is an inline load of the vector header.
Checked `Vec.get` and `Vec.set` stay runtime calls: inlining them (a bounds
check plus a load or store) made the kush-kv store 17-20% faster but the
JSON benchmark (`benchmarks/json-memory`, 4096 × 15, 11 repetitions, against
the previous compiler in the same run) 5-6% slower, as for `Bytes.get`
earlier. `Vec.len` alone measured neutral (80.6 vs 80.8 ms). Hot loops get
the same speed from proofs instead: `Vec.at` and `Bytes.at` with a proved
index are plain loads, and `std.crc32` and `std.bytemap` are written that way
(see [std-storage.md](std-storage.md)).

## Runtime object cache and collection fast paths

Native builds cache the compiled C runtime under
`$XDG_CACHE_HOME/kush/native-runtime-v1` (default
`~/.cache/kush/native-runtime-v1`). `KUSH_RUNTIME_CACHE=/path/to/private/cache`
selects another directory; setting `KUSH_NO_RUNTIME_CACHE` disables it.
The cache is shared across source programs and optimization modes.

A key includes runtime contents, C flags, task/statistics defines and fusion
count, resolved compiler identity/version/target, working directory, a hash of
the environment, and dependency-header paths/sizes/modification times. Every
lookup preprocesses the runtime's include graph, but skips C object compilation
on a hit. Header checks use normal file metadata, not a content-addressed
snapshot. Environment changes can cause conservative misses; environment values
are not stored in plaintext. Cache filenames use a noncryptographic hash;
entries also verify the complete key and an object checksum. This is a private
same-user build cache, not an interface for untrusted object files.

Publication is atomic, parallel cold builds may compile independently, and each
link uses its own scratch-local object copy. Symlinked/unusable caches and
malformed entries fall back to compilation. On Unix the cache leaf must be
owned by the compiling user and private (mode 0700). An optional cache failure
does not prevent a build. To clear it, remove only the selected runtime cache
directory. Other build caches are independent.

`--opt-level speed` (including `--release`) now also:

- Inlines the capacity-available path of owned and borrowed `Vec.push`, including
  aggregate/owning elements. Full vectors retain the original C growth helper
  and overflow/capacity checks; allocation/growth/drop counters are unchanged.
- Versions small `while i < Slice.len(view)` loops over immutable, unpinned
  descriptors. One runtime check selects a fixed word-stride path; other
  descriptors, including byte-backed views, retain generic lowering. Nested
  loops/large bodies are not duplicated. Descriptor assignment/address-taking
  prevents this specialization; element mutation is still supported.
- Reuses a dominating signed upper-bound comparison only for the exact SSA
  index/length pair. Negative indices remain checked at the original access
  site. Changed indices require their own full check. Other slice accesses use
  one unsigned comparison to reject both negative and too-large indices.

This is bounded code generation, not general range analysis or general
inlining. Overflow checks, negative-index failures, byte-write validation,
ownership cleanup, effect order, and the generic ABI remain enforced.

Reproduce build-time measurements with:

```sh
python3 benchmarks/feature-pipeline/build_time.py --kush /path/to/kush
```

The optimization benchmark optionally accepts `--previous /path/to/binaries`
containing a previous `kush-release` and `phases-kush-release`; hashes are
recorded and those controls run in the same shuffled cohort as the new builds.

### Collection/cache checkpoint (2026-11-03)

At compiler `524c39b`, a matched seven-sample cohort measures release at
38.340 ms versus the previous release binary at 74.841 ms and Rust Cranelift
manual fusion at 60.913 ms. Peak RSS stays near 18 MiB. Separate phase probes
measure initialization at 18.576 ms (previous 49.476), transform at 8.298 ms
(previous 7.955), and checksum at 7.188 ms (previous 15.898). The transform
change is small; the targeted gains are initialization and checksum.

Warm C-runtime caching reduces total native build median from 1040.929 ms
(cache disabled) to 236.747 ms using the same compiler, source, release flags
and CPU. A single initial cold-cache build takes 1088.139 ms. The workload
source and previous binary hashes match the prior archived cohort. Raw data
and caveats: `benchmarks/feature-pipeline/sample-results/fastpaths-2026-11-03/`.
These measurements cover this scalar workload only.

Validation at `94cbe30`: Boat passed all **1,147 workspace tests**, formatting,
and strict workspace/all-target Clippy, then stopped with its snapshot preserved.
The first gate identified an obsolete link-failure mock and an older-Clippy
style warning; both were corrected and the full gate rerun. Logs are
`/tmp/kush-boat-cache-fastpaths-full.log` and
`/tmp/kush-boat-cache-fastpaths-retry.log`. Local mbx checks used two jobs:
60 focused tests, strict Clippy, plus the corrected failure-preservation test.
The local installed `~/.local/bin/kush` was updated after validation.
The measured `524c39b` and validated `94cbe30` have identical collection codegen;
the latter only adjusts lazy cache lookup style and failure-test coverage.

### Allocation metadata and retention (2026-11-03)

Compiler `528a804` uses 16-byte allocation headers and retains at most 64 free
blocks per size class under the existing global budget. These changes apply to
all native build modes. Runtime-object caching invalidates automatically because
the embedded C source changed. Full Boat validation passes 1,149 tests,
formatting and strict Clippy. The installed local `kush` has been updated and
its JSON-project checksum smoke check passes.

The [matched memory comparison](../benchmarks/json-memory/sample-results/compact-pool-2026-11-03/analysis.md)
records lower peak requested heap and post-release RSS, plus increased
rebuild-only allocation traffic. Rust deliberate reuse remains leaner on the
measured large corpus.

## Direct call inlining (NATIVE-INLINE)

With `--release` (or `--inline-calls`), every Kush function body is built
first, then each caller absorbs its small direct callees through Cranelift's
library inliner (`Context::inline`): a callee of at most 96 CLIF instructions
that does not call itself directly and has no exception-table calls. Inlined
bodies are visited again, so chains of small predicates flatten; one caller
absorbs at most 64 calls, which bounds mutual recursion. The callee stays an
ordinary out-of-line function for other callers.

Cranelift 0.135's inliner remaps call targets into the caller's name table
but copies data symbols (such as the abort word) verbatim, so each callee copy
has its symbols re-declared in the caller first (`inline_bodies_for` in
`native.rs`); without that, abortive effects read an unrelated symbol.

Correctness: `native_release.rs` runs every program in five modes including
inlining with and without backend optimization; the whole test suite also
passed with inlining forced on in every native build (2026-11-06).

Measurements, AMD Ryzen 5 PRO 5675U, load average about 2, release builds,
`benchmarks/inline` and the existing benchmarks (inlining off vs on, best of
5 or median of 9 runs):

| Benchmark | off | on (limit 96) |
| --- | --- | --- |
| VELA-style policy with predicate calls (`policy-predicates`), ns/decision | 20.5 | 14.2 |
| same policy, conditions written out (`policy-written-out`), ns/decision | 9.6 | 9.0 |
| `effects/direct-call`, ms | 19.9 | 7.6 |
| `effects/checked-call`, ms | 19.9 | 12.5 |
| `effects/capability-perform-in-callee`, ms | 43.5 | 33.2 |
| `effects/dynamic-perform-in-callee`, ms | 63.8 | 53.9 |
| JSON memory, 16384 documents, rebuild / reuse, ms | 571 / 392 | 568 / 396 |
| `unboxing/tag-niche-three-words`, median ms | 398 | 392 |
| `unboxing/multi-niche-tagged`, median ms | 390 | 405 |

The JSON rows are within run-to-run noise. In `multi-niche-tagged` only the
cold construction loop changes; the hot loop's machine code is identical and
moved by 4 bytes, so its difference is code alignment, not the inlined call.
A limit of 48 instructions gave 18.5 ns on the policy (callers such as `plan`
were then too large to absorb). 
## Records in registers (INLINE-RECORD-PARAMS)

Record locals used to be pinned to a stack slot for the whole function so a
`&Record`/`&mut Record` could point at them; every by-value record parameter
was stored there and every field read was a load, and Cranelift removes
neither. Now a record whose fields are scalars (or such records) stays in
SSA variables unless the function takes its address (`&local`, a borrowed
temporary owner, or the root of a field or element place;
`addressed_slots`). Records with arrays, owned or borrowed fields keep the
old rule.

Same machine and method, release builds with inlining:

| Benchmark | pinned | in registers |
| --- | --- | --- |
| `policy-predicates`, ns/decision | 14.2 | 5.9 |
| `policy-written-out`, ns/decision | 9.0 | 5.7 |
| effects, unboxing, JSON (rebuild / reuse) | | within noise (JSON 572 / 399 vs 567 / 398 ms) |

The Rust crate measured 3.3 ns/decision for the same policy. The whole test
suite passed with this change (107 test binaries).
