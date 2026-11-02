# Remote checks with Boat

The local machine can remain the source workspace while a Boat sandbox performs
Rust compilation, native compiler tests, formatting, and Clippy. The remote
checks script does not run Cargo locally or copy target artifacts to this machine.

Authenticate the Boat CLI through `boat login` or private API-key input. Never put
an API key in this repository. Before creating/resuming a sandbox, check the
account's actual allowance with `boat limits --all`. Use one trial-supported
sandbox with automatic stop enabled; this workflow does not change billing plans
or add funds.

Prepare its Rust toolchain and C compiler remotely, then run:

```sh
scripts/boat-check.sh
```

With no argument the script uses `$KUSH_BOAT_SANDBOX` or the `sandbox_id` in
`~/.config/kush/boat.json`. A stopped sandbox is resumed automatically with a
1-hour TTL and `--no-env` (no account secrets); the script stops it again when the
checks finish. Set `KUSH_KEEP_RUNNING=1` to leave it running, or pass an explicit
sandbox id as the first argument to override the configured one. Set
`KUSH_SYNC_ONLY=1` to sync and verify the source without running Cargo, which is
useful after documentation-only edits.

`BOAT_CLI` can select the CLI path; otherwise the script uses `boat` from PATH or
`~/.ascii/bin/boat`.

Each run uploads current tracked and nonignored source files using `boat push`
to a fresh staging directory. Before any check runs, a SHA-256 manifest of the
uploaded files is compared with the local checkout; a mismatch aborts the run
without touching the stable tree. The verified tree is then swapped into
`/home/user/kush`, so the sandbox holds the same source as the local workspace
between runs. `target/` and `.git/` are not part of that sync. Local source
remains authoritative; local edits are uploaded on the next run.

The existing target directory is ignored. A fresh staging directory prevents
stale deleted source files from influencing results. Build artifacts stay in
`/home/user/kush-build-cache`; staging is removed with Python
`shutil.rmtree` when the command ends. The script uses one build job and disables
debug symbols and incremental storage to fit a small sandbox. These settings
concern building the Rust compiler, not the language's checked arithmetic or
ownership guarantees.

The cache records the workspace path it was built under. If that path changes,
the script clears the target cache once before compiling, because Cargo test
binaries embed absolute workspace paths and can otherwise read files from an old
source directory.

First-time dependency downloads require network access; `--locked` keeps the
repository's dependency lockfile authoritative. The sandbox needs Rust 1.95+
(or the project's current minimum), rustfmt, Clippy, and `cc`. Keep these tools
and Cargo's download/build caches on the sandbox for subsequent runs.

Formatting, tests, and Clippy run as separate checks so one failure does not hide
the others. The script exits nonzero if any check fails and prints a
`PASS`/`FAIL (<exit code>)` line for each.

## Current sandbox

| Item | Value |
| --- | --- |
| Sandbox | `bx_3m6vs6ah` (`kush-build`) |
| Machine | small, 2 vCPU / 4 GB, Ubuntu 24.04 x86-64 |
| Lifetime | TTL 3600 s, automatic stop enabled |
| State | stopped after final validation with a completed verified snapshot; the script resumes it automatically |
| Environment | `base`, created with `--no-env` (no account secrets) |
| Build cache | `/home/user/kush-build-cache` |
| Remote source | `/home/user/kush` (verified mirror; fresh `/home/user/kush-sync-*` staging removed after each run) |

The base image already provides the required toolchain:

```text
rustc 1.97.1 (2026-07-14), cargo 1.97.1
rustfmt 1.9.0-stable, clippy 0.1.97
gcc/cc 13.3.0, python3, git, curl
```

Linux x86-64 is the target architecture; remote checks do not validate other
host platforms.

## Validation record (2026-10-31)

The setup was exercised end to end on this sandbox. The initial run passed
383 tests and formatting, but reported one `needless_range_loop` Clippy lint in
`ownership.rs`. After fixing that lint and adding a task-result coercion fix and
regression, the final remote run passed:

```text
cargo fmt --all -- --check                                      PASS
cargo test --workspace --locked --no-fail-fast                   PASS
    384 passed, 0 failed (including 17 async tests)
cargo clippy --workspace --all-targets --locked -- -D warnings    PASS
RESULT: all remote checks passed (exit 0)
```

The async regression checks expected and explicit task-result union widening,
including cancellation cleanup of an owning union, in both native and reference
execution. All Cargo checks ran on Boat; no local compilation was used.

The final run used the no-argument automatic path: it resumed the stopped
sandbox, uploaded 115 files to a fresh staging directory, verified the SHA-256
manifest matched this checkout, swapped the tree into `/home/user/kush`, and
stopped the sandbox again with a snapshot (exit 0). Staging is removed after each
run; the stable remote tree and the build cache are preserved for resume.

The sandbox is stopped after validation to conserve trial compute.

The mutable-return and retained-reborrow milestone subsequently passed **404
tests**, formatting, and Clippy on Boat. Regression coverage includes freezing
mutable slice parameters while shared children remain live, and restoring those
parameters after the children's last use. Existing temporary-argument loan and
pinned-array regressions remain active.

## Latest borrowing validation (2026-10-31)

The final borrowing source passed **431 tests**, formatting, and Clippy with
`-D warnings` on Boat. This includes the checked split, scoped borrowed closure,
lifetime elision, pending-linear cleanup, pipeline and fallible slice-access
regressions. The explicit `Option<i64 | Bool>` test covers reversed option tags,
union payload layout, negative/out-of-bounds results and zero program allocation.
A multi-module regression also checks that fallible slice access uses the
caller-visible `Option`, never an unrelated private declaration.

Independent probe reviews found and drove fixes for temporary argument loans and
local borrowed-callee capture retention. Subsequent elision and pending-linear
reviews found no additional confirmed defect in their samples. See the
[borrowing audit record](borrowing-audit.md) for coverage and limits. This is not
a formal soundness proof.

Final checks used the same no-argument script and remote build cache. Source is
kept authoritative locally and synchronized by a hash-verified upload. No local
Cargo compilation or native stress workloads were run.

## Borrowed-record validation (2026-10-31)

The earlier lifetime-parameterized shared-slice record milestone and its review
fixes passed **449 tests**, `cargo fmt --all -- --check`, and Clippy with
`-D warnings` on Boat. The
regression file `crates/kush/tests/borrowed_records.rs` adds 16 tests covering
construction, field access, destructuring, copies, multiple field lifetimes,
nested/generic/alias records, helper returns, split siblings, loops/branches,
early `?`, same-task suspension, Vec/Bytes/array owners, allocation balance, and
native/reference agreement. At that shared-only milestone negative tests also
rejected local-owner escapes, wrong or swapped fields, owner replacement/drop in
later arguments/fields, mutable or owning mixed fields,
container/union/generic/callable/task escapes, and mutable upgrades of shared
fields. The example `examples/borrowed-records.kush` prints
`10`, `20`, `5` on both backends.

The later mutable-field and mixed-owning milestone passes **466 tests**, the same
formatting and Clippy checks. Its regression file adds mutable construction,
helper returns, transitive move-only affinity, field reborrows, split siblings in
one record, mixed `Box`/`Bytes`/`Vec` cleanup, reordered/partial constructors,
same-task suspension and `noalloc` payload helpers on both backends. Its examples
are `examples/mutable-borrowed-records.kush` and
`examples/mixed-borrowed-records.kush`.

The final no-argument run uploaded 128 files, matched the local SHA-256 manifest,
and stopped sandbox `bx_3m6vs6ah` with a completed, verified snapshot. See the [borrowing audit record](borrowing-audit.md) and
[borrowed-record contract](borrowed-records.md). This is not a formal soundness
proof.

## Stopping and resuming

The borrowing/lifetimes milestone and its review fixes were subsequently checked
with the same automatic workflow: **396 tests passed**, formatting passed, and
Clippy passed with `-D warnings`. This includes 12 lifetime tests with generated
negative cases and native/reference mutation and cleanup checks. The script
stopped the sandbox after validation. No local compilation was used.

The basic-values milestone (fixed-width integers and explicit conversions,
`Char`, 2–16 element tuples, validated UTF-8 `String`, and builtin method
syntax) passes **529 tests**, `cargo fmt --all -- --check`, and Clippy with
`-D warnings` on Boat. The reference evaluator and native backend agree on the
executable basic-value cases. Floating-point values remain unimplemented; see
[basic-values.md](basic-values.md) for the exact remaining scope.

`scripts/boat-check.sh` stops the sandbox automatically when checks finish, so
normal use needs no manual lifecycle commands. Use `KUSH_KEEP_RUNNING=1` when you
need to run several commands without a resume between them.

To stop compute manually (for example after `KUSH_KEEP_RUNNING=1`):

```sh
boat stop bx_3m6vs6ah
```

The stop snapshots the filesystem, including the Rust toolchain,
`/home/user/kush`, and `/home/user/kush-build-cache`. Resume manually with the
same 1-hour TTL and without account environment secrets:

```sh
boat resume bx_3m6vs6ah --ttl 3600 --no-env
```

The check script performs the same resume itself when it finds the sandbox
stopped.

`boat resume` waits for readiness by default. If the sandbox has been stopped
long enough for its snapshot to expire, create a fresh small sandbox with
`boat new --personal --no-env --type small --ttl 3600 --name kush-build` and rerun
the checks; dependency and build caches on the old sandbox are not reused then.

When finished, use `boat stop <sandbox-id>` to stop compute. Boat's current disk
retention rules apply to stopped sandboxes; check the service documentation before
relying on them as a backup. Keep local source as the authoritative copy unless
a separate remote-editing workflow is explicitly set up.

An authenticated sandbox and a completed remote check are required before claiming
this setup works. Merely installing the CLI or creating this script is not that
verification.

## Integrated milestone validation (2026-11-02)

Boat is now authenticated and usable directly from the current development PC.
The corrected full gate hash-verified 173 source files, passed formatting,
**681 tests**, and Clippy with warnings denied, then stopped the existing
sandbox. The earlier gate passed tests/Clippy but failed two formatting checks;
those were corrected before the successful full rerun. See the
[milestone review](milestone-review.md) for the implementation and independent
review record.

## Snapshot cache location correction

Snapshot-tree inspection after the vector/trait gate showed that Boat excludes
`/home/user/.cache` entirely. The old `.cache/kush-target` path therefore lost
its workspace marker and artifacts on every resume, despite the earlier cache
preservation statements in this document. The script now stores Cargo outputs
in `/home/user/kush-build-cache`, outside the snapshot-excluded directory.
The path remains outside the replaced source tree and is never uploaded from
the local target directory. A stop/resume cache-persistence check is pending.
