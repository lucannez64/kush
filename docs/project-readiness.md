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

## Checked host surface (implementation pass)

The first practical host surface is implemented in both the native runtime and
the reference evaluator: bounded filesystem read/write/append/remove/rename/
mkdir/list/metadata, process arguments and environment, wall/monotonic clocks
and sleeping, a bounded non-shell subprocess runner with explicit timeout, and
one-shot plain TCP exchange. Blocking semantics, errno values, ownership, and
explicit timeouts are documented in [host-api.md](host-api.md). Reference
evaluation accepts deterministic `Host` arguments/environment; native output
reads the real process argv, so the project `ProgramInvocation` forwarding
requires no source rewriting.

Everyday helpers live in `std.text`, `std.path`, `std.sort`, and
`std.collections`. `examples/todo-cli` is a project-shaped multi-file CLI with
atomic file replacement, `--file`, `KUSH_TODO_FILE`, invalid-file rejection, and
reload tests. It can move under the project manifest workflow without source
changes.

Still missing and not claimed: recursive directory operations, file handles and
seek, stderr capture, environment mutation, persistent sockets/nonblocking or
TLS HTTP, DNS timeouts, and resource-handle types. The cooperative scheduler is
not used to pretend blocking host calls are cancellable. A frontend limitation
prevents `return i64` inside `while`; the helpers use found flags instead. Full
integrated/Boat validation remains parent-owned.

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

## Project workflow integration

Merged `6180569` as `bcc0aa5`: strict Kush.toml manifests, deterministic local
path dependency resolution and Kush.lock verification, project build/run/check,
per-process #[test] execution, argument forwarding, conservative whitespace
formatting, and VS Code syntax highlighting. LSP diagnostics/go-to-definition
are not implemented. Native manifest entries remain explicit build errors until
the Rust/C bridge is integrated.

Boat validation: 28 focused project/library/CLI tests pass. The full workspace
run passed formatting, Clippy, and every target except one stale diagnostic
substring assertion (1059 passing tests, 1 failing assertion). Commit `f969a0d`
updates that assertion; its entire 9-test executable suite passes on Boat.
Thus all 1060 tests passed across the full run and affected-target rerun, not
in one uninterrupted clean run. Sandbox confirmed stopped. Logs are local:
`/tmp/kush-boat-project-full.log`, `/tmp/kush-boat-project-executable-rerun.log`.
Independent project workflow review remains pending; host APIs and Rust/C
integration continue in separate worktrees.

## Rust/C bridge integration

Compiler checkpoint `2f318ae` adds checked foreign declarations, opaque owned
foreign resources, generated Rust adapters, and project-manifest native linking
for both build/run and tests. Explicit C libraries and Cargo staticlib adapters
are collected from the root and local dependencies. Adapter Cargo builds use
separate target directories to avoid the mbx compiler cache.

Full Boat validation passes **1071 tests**, formatting, and Clippy with warnings
denied. The same command then runs `examples/rust-adapter/Kush.toml`: SHA-256 of
`abc` is correct twice, the live Hasher count is zero, and fallible error/panic
statuses are 1/2. The expected Rust panic-hook message is printed on stderr;
unwinding is contained and the example exits successfully. Sandbox confirmed
stopped. Log: `/tmp/kush-boat-rust-full-example.log` (machine-local).

This provides a native-only trusted C ABI bridge, not arbitrary Rust ABI/type
compatibility. Interpreter foreign calls are rejected explicitly. Independent
interop review remains pending; host APIs and fuller editor/library support
remain in progress.

## Host integration and reviewed project fixes

Host API checkpoint `d6ba475` merges filesystem, argv/environment, clocks,
bounded subprocess/TCP operations, std.text/path/sort/collections/http, and the
persistent todo CLI. Project commands check the app and run its four tests;
CLI eval/native argument and environment behavior agree in regression tests.

Project review follow-ups (`34ed66e`, `77eb93a`, `bda56ac`) separate test
artifacts from package executable names, check normal test targets even with an
empty filter, validate entry headers and lexical identifiers, report actual
lock read errors, retain dash-prefixed single-file commands, and align source
symlink/custom test-path behavior. All 15 project tests pass.

Full Boat gate at compiler checkpoint `bda56ac`: **1088 tests**, formatting,
and all-targets Clippy with warnings denied pass; sandbox confirmed stopped.
Log: `/tmp/kush-boat-project-host-reviewed-full.log` (machine-local). Independent
host and interop review remain required; this is not a claim of complete LSP,
full formatting, TLS, asynchronous I/O, or arbitrary library ABI compatibility.
