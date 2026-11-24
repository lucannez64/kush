# Working gates

Before changing a plan node, mark it started and record its scope with
`scripts/plan.py`. Preserve unrelated edits and do not build into another
worktree's target directory.

For each coherent implementation step:

1. Check available RAM and CPU load. Prefer `mbx` locally with two jobs and a
   dedicated mbx-only target; use Boat for heavy checks when this PC is busy.
2. Run formatting, strict Clippy and focused tests that exercise the changed
   contracts. For compiler semantics include positive and hostile cases;
   accepted executable programs need reference/native parity and cleanup checks
   where relevant. Fix failures before integrating another step.
3. Run `BOAT_NO_UPDATE=1 scripts/boat-check.sh` for the integrated fmt/test/Clippy
   gate. Preserve remote caches and let the script stop the existing sandbox.
   Do not provision, upgrade or change billing without authorization.
4. Review soundness-sensitive changes before closing their feature: provenance,
   aliasing, escape, ownership transfer, cancellation and early-exit cleanup.
   A green suite is evidence, not a soundness proof. Record the source pin,
   tested scope and remaining boundaries; resolve blocking findings.
5. Commit the coherent change, then mark the node done with `--commit SHA` and
   record local/remote results. Do not mark a whole area complete because one
   sub-step passed. A documentation-only change needs relevant script/link checks,
   not another compiler build.

## Safe cleanup

A worktree is removable only after checking its status (including untracked
files), branch history, and whether any process/task still uses it. Never force
remove or delete a branch to make an audit pass. A clean checkout with a merged
ancestor tip is a candidate, not automatic permission to disrupt an active task.
Cherry-picking means an unmerged tip is not by itself proof of unique work;
patch comparison and final-state review are required before removing such a
checkout. Keep it if equivalence or inactivity is uncertain.

The audit inspected 41 delegate worktrees. An ancestry-only check found no
merged-tip candidates, so patch equivalence was checked as well. Thirty-three
inactive checkouts had every unique commit patch-equivalent to main. Their
only untracked file was an empty marker; one also held a target symlink.
These were archived under `~/.cache/kush-worktree-cleanup-20261103`, then those
33 checkouts were removed without force. All branch references and the real
build caches remain. Eight checkouts with unique patches were preserved.
The machine-readable evidence is in `plan/worktree-audit.json`. Branch deletion
is deliberately excluded from this cleanup so every historical tip is recoverable.
