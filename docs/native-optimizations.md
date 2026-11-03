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
