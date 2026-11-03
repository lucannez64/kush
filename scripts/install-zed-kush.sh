#!/usr/bin/env bash
# Install Kush editor support for Zed, locally or on another machine over SSH.
#
#   scripts/install-zed-kush.sh [user@host] [path/to/kush-binary]
#
# Installs:
#   ~/.local/bin/kush                                  (language server: `kush lsp`)
#   ~/.local/share/kush-zed/tree-sitter-kush           (grammar, as a local git repo)
#   ~/.local/share/kush-zed/zed-kush                   (Zed extension, grammar pinned)
#
# Then, in Zed: command palette -> "zed: install dev extension" ->
# choose ~/.local/share/kush-zed/zed-kush. Re-run this script after grammar or
# compiler changes, then "zed: rebuild dev extension" (or reinstall it).
set -euo pipefail

root=$(cd "$(dirname "$0")/.." && pwd)
host=${1:-}
binary=${2:-$HOME/.cache/kush-mbx-release/release/kush}
[ -x "$binary" ] || { echo "kush binary not found at $binary (build with: mbx build --release -p kush --bin kush)" >&2; exit 1; }

stage=$(mktemp -d)
trap 'rm -rf "$stage"' EXIT
mkdir -p "$stage/tree-sitter-kush" "$stage/zed-kush"
cp -r "$root/editors/tree-sitter-kush/"{grammar.js,tree-sitter.json,src,queries} "$stage/tree-sitter-kush/"
cp -r "$root/editors/zed-kush/"{extension.toml,Cargo.toml,src,languages,.cargo} "$stage/zed-kush/"
cp "$binary" "$stage/kush"

remote_script='
set -euo pipefail
base="$HOME/.local/share/kush-zed"
stage="$1"
mkdir -p "$HOME/.local/bin" "$base"
install -m 755 "$stage/kush" "$HOME/.local/bin/kush"
grammar="$base/tree-sitter-kush"
mkdir -p "$grammar"
rsync -a --delete --exclude .git "$stage/tree-sitter-kush/" "$grammar/"
cd "$grammar"
[ -d .git ] || git init -q -b main
git add -A
git -c user.name=kush -c user.email=kush@localhost commit -q -m "Kush grammar" >/dev/null 2>&1 || true
rev=$(git rev-parse HEAD)
ext="$base/zed-kush"
mkdir -p "$ext"
rsync -a --delete --exclude target --exclude grammars --exclude extension.wasm "$stage/zed-kush/" "$ext/"
python3 - "$ext/extension.toml" "$grammar" "$rev" <<PY
import re, sys
path, grammar, rev = sys.argv[1:]
text = open(path).read()
block = f"[grammars.kush]\nrepository = \"file://{grammar}\"\nrev = \"{rev}\"\n"
text = re.sub(r"\[grammars\.kush\]\n(?:[a-z]+ = .*\n)+", block, text)
open(path, "w").write(text)
PY
echo "kush:      $HOME/.local/bin/kush ($("$HOME/.local/bin/kush" --help | head -1))"
echo "grammar:   $grammar @ ${rev:0:12}"
echo "extension: $ext"
case ":$PATH:" in *":$HOME/.local/bin:"*) ;; *) echo "note: add ~/.local/bin to PATH so Zed finds kush";; esac
'

if [ -z "$host" ]; then
    bash -c "$remote_script" _ "$stage"
else
    remote_stage=$(ssh "$host" mktemp -d)
    rsync -a "$stage/" "$host:$remote_stage/"
    # Feed the script on stdin so the remote login shell (bash, fish, ...)
    # never has to parse it.
    printf '%s' "$remote_script" | ssh "$host" bash -s -- "$remote_stage"
    ssh "$host" rm -rf "$remote_stage"
fi
echo "Next: in Zed run 'zed: install dev extension' and pick ~/.local/share/kush-zed/zed-kush"
