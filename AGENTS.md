# Kush workspace instructions

Keep this computer responsive and prefer Boat for heavy compilation and testing.
The user explicitly allows local builds and tests when this PC has spare capacity,
including while Boat access is being migrated. Check available RAM and CPU load
first, use conservative build concurrency (start with two jobs), and move heavier
workloads to Boat when local capacity is constrained.

- For local builds, prefer `mbx build` / `mbx test` / `mbx clippy` (Mr.
  Boxington, installed in `~/.cargo/bin`) over plain `cargo`, so worktrees share
  compiled dependencies through `~/.cache/mbx`. Keep a target directory on one
  tool: mbx hard-links read-only cached outputs, which plain `cargo` cannot
  overwrite. The Cargo shim is intentionally not on `PATH`.
- Use `scripts/boat-check.sh` for source upload and remote checks. With no
  argument it takes the sandbox from `~/.config/kush/boat.json`, resumes it when
  stopped, verifies the uploaded tree matches this checkout, runs the checks, and
  stops the sandbox afterwards. Set `KUSH_KEEP_RUNNING=1` only when you need the
  VM to stay up between commands.
- Machine-local sandbox details are in `~/.config/kush/boat.json`; no API key is
  stored in this repository. Use the authenticated Boat CLI. Never print tokens
  or copy host credentials to a sandbox.
- Verify actual trial allowance using `boat limits --all` before provisioning.
  Use one trial-supported sandbox with automatic stop enabled. No plan upgrades,
  wallet funding, or paid-overage changes without explicit user authorization.
- Preserve build caches remotely; do not upload the local target directory.
- If Boat is unavailable, report the blocker. Local checks are authorized when
  there is spare capacity; keep resource use conservative and report where checks ran.
- Preserve all existing uncommitted work. The initial cooperative task system is implemented; see `docs/async.md` for its limits.
