#!/usr/bin/env python3
"""Time builds of the generated program at several sizes.

    python3 measure.py --kush /path/to/kush [--units 100 500 2000]

Prints a Markdown table of wall-clock seconds (best of `--repetitions`).
Kush rows are measured with the proof cache disabled, then once more with
it warm; the C runtime cache is warm throughout.
"""
import argparse
import os
import subprocess
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def best(command, repetitions, environment):
    times = []
    for _ in range(repetitions):
        started = time.perf_counter()
        done = subprocess.run(command, capture_output=True, env=environment)
        elapsed = time.perf_counter() - started
        if done.returncode != 0:
            raise SystemExit(f"{command}: {done.stderr.decode()[:2000]}")
        times.append(elapsed)
    return min(times)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--kush", required=True, type=Path)
    parser.add_argument("--units", type=int, nargs="+", default=[100, 500, 2000])
    parser.add_argument("--repetitions", type=int, default=3)
    args = parser.parse_args()
    kush = str(args.kush.resolve())
    rows = {}
    with tempfile.TemporaryDirectory(prefix="kush-build-scale-") as directory:
        for units in args.units:
            root = Path(directory) / str(units)
            subprocess.run(
                ["python3", str(ROOT / "generate.py"), str(units), str(root)], check=True
            )
            lines = len((root / "main.kush").read_text().splitlines())
            source, binary = str(root / "main.kush"), str(root / "program")
            cold = dict(os.environ, KUSH_NO_PROOF_CACHE="1")
            warm = dict(os.environ, KUSH_PROOF_CACHE=str(root / "proofs"))
            warm.pop("KUSH_NO_PROOF_CACHE", None)
            builds = {
                "Kush, Cranelift": [kush, "build", source, "-o", binary],
                "Kush, LLVM `--release`": [
                    kush, "build", source, "-o", binary, "--release", "--backend", "llvm",
                ],
            }
            results = {}
            for name, command in builds.items():
                results[name] = best(command, args.repetitions, cold)
                best(command, 1, warm)
                results[name + ", warm proof cache"] = best(command, args.repetitions, warm)
            rust = str(root / "main.rs")
            results["`rustc` debug"] = best(
                ["rustc", rust, "-o", binary], args.repetitions, dict(os.environ)
            )
            results["`rustc -C opt-level=3`"] = best(
                ["rustc", "-C", "opt-level=3", rust, "-o", binary],
                args.repetitions,
                dict(os.environ),
            )
            outputs = set()
            for command in (builds["Kush, LLVM `--release`"], ["rustc", "-O", rust, "-o", binary]):
                subprocess.run(command, check=True, capture_output=True, env=warm)
                outputs.add(subprocess.run([binary], capture_output=True).stdout)
            if len(outputs) != 1:
                raise SystemExit(f"{units} units: the two programs print different results")
            rows[(units, lines)] = results
    header = " | ".join(f"{units} units ({lines:,} lines)" for units, lines in rows)
    print(f"| Build | {header} |")
    print("| --- |" + " ---: |" * len(rows))
    for name in next(iter(rows.values())):
        cells = " | ".join(f"{results[name]:.2f}" for results in rows.values())
        print(f"| {name} | {cells} |")


if __name__ == "__main__":
    main()
