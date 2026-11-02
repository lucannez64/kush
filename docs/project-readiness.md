# Project readiness work

The advanced-language completion backlog is on hold at the user's request.
Active work targets useful applications and reusing existing Rust/C libraries:

1. Correct known reference safety defects, retain adversarial regressions, and
   validate the integrated compiler before declaring it ready.
2. Checked host APIs: filesystem, arguments/environment, clocks, processes,
   networking and timeouts, with explicit effects and deterministic cleanup.
3. Project manifests, reproducible local dependencies, project build/run/test,
   formatting and editor integration (`kush lsp`, diagnostics,
   go-to-definition, VS Code client).
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
not used to pretend blocking host calls are cancellable. The helpers use explicit found flags for searches; simple `i64` returns from
`while` are supported. Full
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

This is not full editor or package tooling: the LSP now supplies live
diagnostics and lexical go-to-definition, but not completion, hover, rename,
references, semantic tokens, or incremental sync; there is no package registry,
workspace, or incremental build. See [language-server.md](language-server.md).
Test functions return `Unit` and use the `std.test` assertion helpers; runtime
failures are reported by test name with captured output, while compile errors
retain normal source diagnostics. See [projects.md](projects.md) for exact
limits and integration points.

## Project workflow integration

Merged `6180569` as `bcc0aa5`: strict Kush.toml manifests, deterministic local
path dependency resolution and Kush.lock verification, project build/run/check,
per-process #[test] execution, argument forwarding, conservative whitespace
formatting, and VS Code syntax highlighting. Editor tooling was later extended
with `kush lsp`; see the language-server section below.

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

### Declarative adapter generation

`kush bindgen <Bridge.toml> [--check]` turns a strict declarative adapter
configuration into both generated sides: Rust `extern "C"` shims through
`AdapterSpec` and a matching public Kush module with resource releases and a
callable owned-`Bytes` error accessor. It supports borrowed text/bytes, fixed
scalars, `Bool`, borrowed resources, owned bytes/resource results, `Unit`, and
`Result<T, i64>` fallibility. Paths are configuration-relative and may contain
spaces; unknown keys, Rust keywords, reserved/generated symbol collisions,
duplicate resources, `kush_out`, and `<name>_data`/`<name>_len` collisions are
rejected. Generated files are deterministic and marker-protected; `--check`
reports drift without writing, and output symlinks are refused. Generated Rust
requires `panic = "unwind"` and works through `include!`; each adapter derives
distinct error-helper symbols so two adapters can link together. The
`examples/rust-adapter` project reuses `sha2` and now demonstrates
`bindgen -> kush run -> kush test`. See [native interop](native-interop.md).
Callbacks, arbitrary Rust ABI, borrowed results, structs/variadics, and
resource ownership transfer into foreign code remain outside the boundary.

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

## Bridge core and shared helper review corrections

The interop review found two high-severity checked-side defects: foreign handle
layouts were recomputed as two words despite the one-word C ABI, and borrowed
foreign results were accepted without a supported return ABI. `f36aaf5` fixes
these, same-width u64 lowering, owned Bytes/Unit parameter rejection, requested
Cargo artifact selection, response-file argument rejection, package library
path confinement, and versioned shared-library paths. Tests cover handles in
records/tuples/arrays/vectors/boxes/calls/Result slots, following arguments,
release counts, rejected borrowed results, u64, and dependency staticlibs.

Full Boat command at `3e74911` passes **1092 workspace tests**, formatting,
Clippy, the Rust SHA-256 project, and the todo project's four tests. The
combined log counter includes those four app tests separately (1096 total);
they are not additional workspace tests.
Log: `/tmp/kush-boat-ffi-core-reviewed-full.log` (machine-local).

The host review found incorrect HTTP header termination. `b54696d` scans for
the complete CRLF-CRLF terminator, preserving zero/one/multiple headers and
empty bodies. It also fixes lone-CR trimming, root basenames, and dotfile
extensions. Eleven focused host/helper tests and all-targets Clippy pass on
Boat. Log: `/tmp/kush-boat-http-helper-review-fixes.log`. Sandbox stopped.

## Editor language server

`kush lsp` implements bounded stdio JSON-RPC framing, initialize/shutdown/exit,
full-sync `didOpen`/`didChange`/`didClose`, versioned diagnostics from unsaved
overlays, lexical go-to-definition for local bindings, declarations, imported
items, and `use` module paths, and formatting through the existing
whitespace-only formatter. It reuses `program::load`,
`resolve::resolve_program`, and `executable::check_program`; diagnostics do not
write `Kush.lock` or run Cargo/native code. The VS Code extension uses
`vscode-languageclient` and a configurable `kush.server.path` while preserving
the TextMate grammar.

Not implemented and not claimed: completion, hover, rename, references,
semantic tokens, incremental sync, type-directed method dispatch in
go-to-definition, or a real pretty-printer. Builtins and virtual standard
modules return no definition instead of a bogus file path. See
[language-server.md](language-server.md) for protocol details, UTF-16 handling,
and the exact limits. Integrated Boat validation at compiler checkpoint
`772b1f6` passes **56 focused tests** (library, language server, project, CLI,
and bindgen), formatting, and workspace/all-targets Clippy with warnings denied.
Log: `/tmp/kush-boat-lsp-integration.log` (machine-local). The VS Code client's
server-disable fix at `18577f7` also passes `node --check`; editor UI behavior
has not been exercised inside VS Code.

The subsequent full Boat gate at `414f170` passes **1116 workspace tests**,
formatting, and Clippy. The sandbox stopped with its snapshot preserved.
Log: `/tmp/kush-boat-lsp-full.log` (machine-local). Independent language-server
review remains pending; the gate does not replace that review.

Still unresolved: evaluator-wide TCP/process deadline behavior, secure todo
file replacement and permissions, fuller editor features, and the other documented
readiness limits. These passing tests do not erase outstanding review findings.

## Declarative Rust adapter integration

Compiler checkpoint `21c566d` integrates `kush bindgen Bridge.toml [--check]`:
a strict config generates Rust C-ABI shims and matching Kush declarations.
Module-derived helper namespaces allow multiple generated adapters to link;
generated Rust works through `include!` and rejects panic-abort builds. Output
writes use exclusive temporary creation, preserve existing permissions, and
refuse unmarked files and symlink output paths. The legacy library generator's
default helper prefix remains appropriate for one adapter; multiple adapters
must use distinct configured prefixes.

Boat focused validation passes **47 workspace tests** (bindgen 8, CLI 9,
FFI 15, project 15), formatting, and workspace/all-targets Clippy with warnings
denied. Generated example files pass drift checking. The Rust SHA-256 project
runs correctly and its **two app tests** pass, including exactly-once resource
release and error text. Log: `/tmp/kush-boat-bindgen-integration.log`
(machine-local).

Full Boat gate after integration: **1102 workspace tests**, formatting, and
Clippy pass. The sandbox was stopped with its snapshot preserved. Compiler
source matches `21c566d`; later commits only document output protection and
validation. Log: `/tmp/kush-boat-bindgen-full.log` (machine-local).
Independent bindgen review found five low-severity validation/code-generation
issues, corrected at `0b48a14`: helper shadowing, Kush builtin/resource/function
name collisions, ambiguous flattened helper namespaces, output-directory prefix
conflicts, and an unused fallible-Unit binding. Module-derived helpers now use
length-prefixed components, so `a.b` and `a_b` remain distinct. The generated
example files were updated together.

Boat correction validation passes **35 focused workspace tests** (bindgen 11,
FFI 15, resolver 9), formatting, and workspace/all-targets Clippy. Generated-file
drift checks and the Rust adapter project's **two app tests** pass. New tests
reject invalid configs before any output writes and compile colliding-path
namespaces and fallible Unit shims with warnings denied.
Log: `/tmp/kush-boat-bindgen-review-fixes.log` (machine-local). Full workspace
validation after these corrections is pending. Host deadlines/persistence and
independent LSP review remain outstanding.
