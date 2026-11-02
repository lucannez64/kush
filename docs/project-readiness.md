# Project readiness work

The advanced-language completion backlog is on hold at the user's request.
Active work targets useful applications and reusing existing Rust/C libraries:

1. Correct known reference safety defects, retain adversarial regressions, and
   validate the integrated compiler before declaring it ready.
2. Checked host APIs: filesystem, arguments/environment, clocks, processes,
   networking and timeouts, with explicit effects and deterministic cleanup.
3. Project manifests, reproducible local dependencies, project build/run/test,
   formatting and basic editor integration.
4. Rust-first native-library integration, generated checked adapters and C ABI
   support, with ownership, errors, panic boundaries, and executable examples.
5. Everyday library helpers and a persistent multi-file CLI application that
   demonstrates the project workflow end to end.

New capabilities require positive application tests, hostile input/cleanup
coverage where relevant, native/reference agreement where supported, exact
unsupported-boundary diagnostics, and full integrated Boat checks. This file
tracks work in progress, not a claim that these APIs exist already.

Initial safety correction: indexed-place base/index evaluation order now
matches checking; InitOwner place reads retain one owner; hidden declarations
use their real source span for lexical escape detection. Focused local checks:
38 borrowing-reference tests and 8 borrowing-safety tests pass with mbx, two
jobs. Broader compiler validation and independent review remain required.

## Project workflow milestone

The practical project layer is implemented in `kush::project` and documented in
[projects.md](projects.md): strict `Kush.toml` parsing, local path dependency
resolution with deterministic ordering and cycle/missing/name-collision
diagnostics, a generated `Kush.lock`, `kush new`, project
check/build/run/test, `#[test]` discovery with per-test processes and filtering,
a comment/string-preserving whitespace formatter with `--check`, process-argument
forwarding after `--`, and validated `[native]` manifest extension points.

This is not full editor or package tooling: there is no LSP, live diagnostics,
go-to-definition, registry, workspace, or incremental build, and `[native]`
entries intentionally fail project build/run/test until the Rust/C bridge lands.
Test functions return `Unit` and use the `std.test` assertion helpers; runtime
failures are reported by test name with captured output, while compile errors
retain normal source diagnostics. See [projects.md](projects.md) for exact
limits and integration points.
