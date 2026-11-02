#!/usr/bin/env bash
# Sync this checkout to Boat and run checks remotely; never invokes Cargo here.
#
# Usage:
#   scripts/boat-check.sh [sandbox-id]
#
# With no argument, uses $KUSH_BOAT_SANDBOX or the sandbox_id in
# ~/.config/kush/boat.json. A stopped sandbox is resumed with a 1-hour TTL and
# no account environment secrets. The source is uploaded to a fresh staging
# directory, verified file-by-file against the local checkout, then swapped into
# the stable remote path /home/user/kush before checks run. The sandbox is
# stopped again on exit unless KUSH_KEEP_RUNNING=1. KUSH_COMMAND='cargo check'
# runs one command after syncing instead of the full fmt/test/clippy suite.
set -euo pipefail

root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
sandbox=${1:-${KUSH_BOAT_SANDBOX:-}}
if [[ -z $sandbox ]]; then
    sandbox=$(python3 - <<'PY'
import json, pathlib
try:
    config = json.loads((pathlib.Path.home() / ".config/kush/boat.json").read_text())
    print(config.get("sandbox_id", ""))
except Exception:
    print("")
PY
)
fi
if [[ -z $sandbox ]]; then
    echo 'Usage: scripts/boat-check.sh <boat-sandbox-id>' >&2
    echo 'No sandbox id given and no sandbox_id in ~/.config/kush/boat.json.' >&2
    exit 2
fi

if [[ -n ${BOAT_CLI:-} ]]; then
    boat_cli=$BOAT_CLI
elif command -v boat >/dev/null 2>&1; then
    boat_cli=boat
else
    boat_cli=$HOME/.ascii/bin/boat
fi

ttl=${KUSH_BOAT_TTL:-3600}
keep_running=${KUSH_KEEP_RUNNING:-0}
stop_on_exit=0

sandbox_state() {
    "$boat_cli" info --json "$sandbox" | python3 -c \
        'import json,sys; print(json.load(sys.stdin)["sandbox"]["state"])'
}

stop_sandbox() {
    if [[ $keep_running == 1 ]]; then
        echo "Keeping sandbox $sandbox running (KUSH_KEEP_RUNNING=1)." >&2
        return
    fi
    echo "Stopping sandbox $sandbox (snapshot preserved)..." >&2
    "$boat_cli" stop "$sandbox" --json >/dev/null || echo "warning: could not stop $sandbox" >&2
}

on_exit() {
    status=$?
    trap - EXIT
    if [[ $stop_on_exit == 1 ]]; then
        stop_sandbox
    fi
    exit "$status"
}
trap on_exit EXIT

# Resume a stopped snapshot so a subagent can invoke this script unconditionally.
state=$(sandbox_state)
if [[ $state == stopping ]]; then
    for _ in $(seq 1 24); do
        sleep 5
        state=$(sandbox_state)
        [[ $state == stopped ]] && break
    done
fi
case $state in
    stopped)
        echo "Resuming $sandbox (ttl=${ttl}s, no-env)..." >&2
        "$boat_cli" resume "$sandbox" --ttl "$ttl" --no-env --json >/dev/null
        stop_on_exit=1
        ;;
    idle|running|ready|provisioned|cloning|starting)
        stop_on_exit=1
        ;;
    *)
        echo "sandbox $sandbox is in state '$state'; refusing to run checks" >&2
        exit 1
        ;;
esac

# Hash exactly the files boat push will send: tracked plus nonignored files.
local_manifest=$(python3 - "$root" <<'PY'
import hashlib, os, subprocess, sys
root = sys.argv[1]
out = subprocess.run(
    ["git", "-C", root, "ls-files", "-z", "-co", "--exclude-standard"],
    check=True, capture_output=True,
).stdout
paths = sorted({p.decode() for p in out.split(b"\0") if p})
h = hashlib.sha256()
count = 0
for rel in paths:
    path = os.path.join(root, rel)
    if not os.path.isfile(path):
        continue
    with open(path, "rb") as file:
        digest = hashlib.sha256(file.read()).digest()
    h.update(rel.encode() + b"\0" + digest)
    count += 1
print(f"{count} {h.hexdigest()}")
PY
)

remote_staging="/home/user/kush-sync-$(date -u +%Y%m%dT%H%M%S)-$$"
# A fresh staging directory prevents deleted local files surviving remote checks.
# target/ is ignored. A stable /home/user/kush tree is swapped in only after the
# uploaded content matches the local checkout's manifest.
"$boat_cli" push "$sandbox" "$root" --to "$remote_staging"

remote_command="export KUSH_STAGING='$remote_staging'"$'\n'"export KUSH_STABLE='/home/user/kush'"$'\n'"export KUSH_EXPECTED_MANIFEST='$local_manifest'"$'\n'"export KUSH_SYNC_ONLY='${KUSH_SYNC_ONLY:-0}'"$'\n'"export KUSH_COMMAND=$(printf '%q' "${KUSH_COMMAND:-}")"$'\n'"$(cat <<'REMOTE'
set -u
export PATH="$HOME/.cargo/bin:/usr/local/cargo/bin:$PATH"
# Boat excludes .cache from filesystem snapshots. Keep Cargo artifacts in a
# normal home directory so automatic stop/resume preserves the build cache.
export CARGO_TARGET_DIR=/home/user/kush-build-cache
export CARGO_BUILD_JOBS=1
export CARGO_INCREMENTAL=0
export CARGO_PROFILE_DEV_DEBUG=0
export CARGO_PROFILE_TEST_DEBUG=0
export CARGO_NET_RETRY=5
mkdir -p "$CARGO_TARGET_DIR"
cleanup() {
    python3 - "$KUSH_STAGING" <<'PY'
import shutil, sys
shutil.rmtree(sys.argv[1], ignore_errors=True)
PY
}
trap cleanup EXIT

actual_manifest=$(python3 - "$KUSH_STAGING" <<'PY'
import hashlib, os, sys
root = sys.argv[1]
entries = []
for dirpath, dirnames, filenames in os.walk(root):
    dirnames.sort()
    for name in sorted(filenames):
        path = os.path.join(dirpath, name)
        if not os.path.isfile(path):
            continue
        rel = os.path.relpath(path, root)
        with open(path, "rb") as file:
            entries.append((rel, hashlib.sha256(file.read()).digest()))
entries.sort()
h = hashlib.sha256()
for rel, digest in entries:
    h.update(rel.encode() + b"\0" + digest)
print(f"{len(entries)} {h.hexdigest()}")
PY
)
if [ "$actual_manifest" != "$KUSH_EXPECTED_MANIFEST" ]; then
    echo "SYNC MISMATCH: local=$KUSH_EXPECTED_MANIFEST remote=$actual_manifest" >&2
    exit 3
fi
echo "SYNC: $actual_manifest (local and remote files match)"

# Swap the verified upload into the stable path so both machines expose the
# same source tree between runs.
python3 - "$KUSH_STAGING" "$KUSH_STABLE" <<'PY'
import os, shutil, sys
src, dst = sys.argv[1], sys.argv[2]
if os.path.lexists(dst):
    if os.path.isdir(dst) and not os.path.islink(dst):
        shutil.rmtree(dst)
    else:
        os.remove(dst)
os.replace(src, dst)
PY
export KUSH_SOURCE="$KUSH_STABLE"
cd "$KUSH_SOURCE" || exit 1

# Cargo test binaries embed the absolute workspace path. If the cache was built
# under a different path, its test binaries can point at a directory that no
# longer exists, so clear the cache once when the workspace path changes.
workspace_marker="$CARGO_TARGET_DIR/.kush-workspace"
if [ ! -f "$workspace_marker" ] || [ "$(cat "$workspace_marker")" != "$KUSH_SOURCE" ]; then
    echo "workspace path changed; clearing stale build cache"
    python3 - "$CARGO_TARGET_DIR" <<'PY'
import shutil, sys
shutil.rmtree(sys.argv[1], ignore_errors=True)
PY
    mkdir -p "$CARGO_TARGET_DIR"
fi
printf '%s\n' "$KUSH_SOURCE" > "$workspace_marker"

echo "== remote =="
uname -srm
rustc --version
cargo --version
cargo fmt --version
cargo clippy --version
cc --version | head -n 1
echo "workspace=$KUSH_SOURCE"
echo "target=$CARGO_TARGET_DIR"
echo "jobs=$CARGO_BUILD_JOBS"

if [ "$KUSH_SYNC_ONLY" = 1 ]; then
    echo "RESULT: sync only (checks skipped)"
    exit 0
fi

if [ -n "$KUSH_COMMAND" ]; then
    echo "== custom: $KUSH_COMMAND =="
    bash -c "$KUSH_COMMAND"
    exit $?
fi

status=0
# Keep every result: a formatting failure must not hide compile or test results.
run_check() {
    label=$1
    shift
    echo
    echo "== $label =="
    if "$@"; then
        echo "PASS: $label"
    else
        code=$?
        echo "FAIL ($code): $label"
        status=1
    fi
}
run_check 'cargo fmt --check' cargo fmt --all -- --check
run_check 'cargo test' cargo test --workspace --locked --no-fail-fast
run_check 'cargo clippy' cargo clippy --workspace --all-targets --locked -- -D warnings

echo
if [ "$status" -eq 0 ]; then
    echo "RESULT: all remote checks passed"
else
    echo "RESULT: one or more remote checks failed"
fi
exit "$status"
REMOTE
)"
"$boat_cli" exec --timeout 0 --stream "$sandbox" -- "$remote_command"
