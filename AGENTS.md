# Kush workspace instructions

Builds and tests run on this computer; there is no remote build machine (Boat
is no longer available, so do not use `scripts/boat-check.sh`). Keep the
computer responsive: check available RAM, CPU load and free disk space first,
and use conservative build concurrency (start with two jobs).

- Prefer `mbx build` / `mbx test` / `mbx clippy` (Mr. Boxington, installed in
  `~/.cargo/bin`) over plain `cargo`, so worktrees share compiled dependencies
  through `~/.cache/mbx`. Keep a target directory on one tool: mbx hard-links
  read-only cached outputs, which plain `cargo` cannot overwrite. The Cargo shim
  is intentionally not on `PATH`.
- Disk space is the tightest resource. A debug `mbx test -p kush` build takes
  about 24 GB with debug info; set `CARGO_PROFILE_DEV_DEBUG=0
  CARGO_PROFILE_TEST_DEBUG=0` unless you need a debugger, and check `df -h /`
  before building. mbx storage is capped at 20 GiB (`gc.max_total_size`);
  `mbx gc` is the safe cleanup, but run it only when no build is in progress.
- Use `--no-fail-fast` for full test runs so one failing test file does not hide
  the rest. `scripts/test-all.sh` runs the whole suite with cargo-nextest,
  sized to the machine's free memory and cores (about 3.5 minutes instead of
  about 40 with `mbx test -j 2`); targeted runs can stay on `mbx test`.
- Preserve all existing uncommitted work. The initial cooperative task system is implemented; see `docs/async.md` for its limits.
- Work plan: `plan/plan.json` is the dependency graph of remaining work. View it
  with `scripts/plan-server.py` (http://127.0.0.1:4318/). Update it with
  `scripts/plan.py start|done|log|add ID ...` when starting, finishing (with
  `--commit`), or noting progress on a node, and add nodes for new work.
