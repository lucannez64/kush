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
