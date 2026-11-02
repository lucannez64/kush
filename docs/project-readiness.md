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
   Implemented in this branch for Linux x86-64: `foreign "symbol" fn ...;`
   declarations, checked `io`/signature/resource rules, `Result<T, i64>` status
   lowering, exactly-once `#[foreign("release")]` resources, `LinkSpec` and
   `build_with_options`, generated Rust adapter shims with panic containment,
   the `[native]` manifest mapping, and `examples/rust-adapter/` reusing `sha2`.
   See [native interop](native-interop.md). Project-manifest wiring and the
   integrated Boat gate are parent-owned.
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
