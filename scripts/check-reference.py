#!/usr/bin/env python3
"""Check every Kush example in the language reference against the compiler.

  scripts/check-reference.py [--kush PATH] [--native] [FILE.md ...]

Fenced blocks whose info string starts with `kush` are programs:

  ```kush            must pass `kush check`
  ```kush eval       must run with `kush eval`; its stdout must equal the
                     next ```output block, if there is one. `exit=N` in the
                     info string sets the expected exit status (default 0).
  ```kush reject     `kush check` must fail; every `// error: TEXT` line in
                     the block must appear in the diagnostic.
  ```kush fragment   not checked (syntax excerpts only; use sparingly).

`--native` also builds and runs each `eval` block natively and compares.
Defaults: docs/reference/*.md and target/release/kush.
"""
import argparse
import concurrent.futures
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
FENCE = re.compile(r"^```(\S*)(.*)$")


def blocks(path):
    """Yield (line, kind, options, source, expected_output) for each program."""
    lines = path.read_text().splitlines()
    found, i = [], 0
    while i < len(lines):
        m = FENCE.match(lines[i])
        if not m or not m.group(1):
            i += 1
            continue
        lang, rest, start = m.group(1), m.group(2).split(), i + 1
        j = start
        while j < len(lines) and lines[j].strip() != "```":
            j += 1
        body = "\n".join(lines[start:j]) + "\n"
        found.append((start, lang, rest, body))
        i = j + 1
    for index, (line, lang, rest, body) in enumerate(found):
        if lang != "kush":
            continue
        kind = rest[0] if rest and "=" not in rest[0] else "check"
        options = dict(r.split("=", 1) for r in rest if "=" in r)
        expected = None
        if kind == "eval" and index + 1 < len(found) and found[index + 1][1] == "output":
            expected = found[index + 1][3]
        yield line, kind, options, body, expected


def run(kush, args, cwd):
    return subprocess.run([kush, *args], cwd=cwd, capture_output=True, text=True, timeout=300)


def check(kush, native, item):
    path, line, kind, options, body, expected = item
    where = f"{path.relative_to(ROOT)}:{line}"
    if kind == "fragment":
        return None
    with tempfile.TemporaryDirectory(prefix="kush-ref-") as tmp:
        source = Path(tmp) / "example.kush"
        source.write_text(body)
        if kind == "check":
            r = run(kush, ["check", str(source)], tmp)
            if r.returncode != 0:
                return f"{where}: expected to check, got:\n{r.stderr.strip()}"
        elif kind == "reject":
            r = run(kush, ["check", str(source)], tmp)
            if r.returncode == 0:
                return f"{where}: expected a diagnostic, but the program checks"
            wanted = re.findall(r"//\s*error:\s*(.+)", body)
            if not wanted:
                return f"{where}: a reject block needs at least one '// error: TEXT' line"
            for text in wanted:
                if text.strip() not in r.stderr:
                    return f"{where}: diagnostic does not contain {text.strip()!r}:\n{r.stderr.strip()}"
        elif kind == "eval":
            status = int(options.get("exit", "0"))
            modes = [["eval", str(source)]] + ([["run", str(source)]] if native else [])
            for mode in modes:
                r = run(kush, mode, tmp)
                if r.returncode != status:
                    return f"{where}: {mode[0]} exited {r.returncode}, expected {status}:\n{r.stderr.strip()}"
                if expected is not None and r.stdout != expected:
                    return f"{where}: {mode[0]} printed {r.stdout!r}, expected {expected!r}"
        else:
            return f"{where}: unknown block kind {kind!r}"
    return None


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("files", nargs="*")
    parser.add_argument("--kush", default=os.environ.get("KUSH", str(ROOT / "target/release/kush")))
    parser.add_argument("--native", action="store_true")
    parser.add_argument("--jobs", type=int, default=max(1, (os.cpu_count() or 2) // 2))
    args = parser.parse_args()
    files = [Path(f).resolve() for f in args.files] or sorted((ROOT / "docs/reference").glob("*.md"))
    items = [(f, *b) for f in files for b in blocks(f)]
    with concurrent.futures.ThreadPoolExecutor(args.jobs) as pool:
        failures = [r for r in pool.map(lambda it: check(args.kush, args.native, it), items) if r]
    for failure in failures:
        print(failure, end="\n\n")
    checked = sum(1 for it in items if it[2] != "fragment")
    print(f"check-reference: {checked - len(failures)}/{checked} examples pass "
          f"({len(items) - checked} fragments not checked)")
    sys.exit(1 if failures else 0)


if __name__ == "__main__":
    main()
