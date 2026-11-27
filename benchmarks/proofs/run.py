#!/usr/bin/env python3
"""What Kush's proofs buy, against the same code in Rust, C and Zig.

    python3 benchmarks/proofs/run.py --kush /path/to/kush --zig /path/to/zig \
        [--repetitions 15] [--cpu 5] [--json results.json]

Kush is built twice from the same source: as written, and with
`KUSH_KEEP_PROVED_CHECKS=1`, which keeps every runtime check the proofs
would remove. Rust and Zig run each kernel in a checked form (safe Rust,
Zig ReleaseSafe) and in a trusted form that skips exactly what Kush proves
(`unsafe` unchecked reads, Zig many-pointer reads and wrapping arithmetic).
C is unchecked by nature. Overflow of the accumulators is checked
everywhere. Every variant must print the same number before anything is
timed. Prints Markdown.
"""
import argparse
import json
import os
import random
import statistics
import subprocess
import tempfile
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent

KERNELS = {
    "sum": ["4096", "200001", "0"],
    "stencil": ["65536", "20001", "1"],
    "crc32": ["65536", "4001", "2"],
}

# name -> (binary, mode argument)
VARIANTS = {
    "Kush, proofs": ("kush-proofs", "0"),
    "Kush, checks kept": ("kush-checks", "0"),
    "Rust, safe": ("rust", "0"),
    "Rust, unsafe": ("rust", "1"),
    "C": ("c", "0"),
    "Zig, safe": ("zig", "0"),
    "Zig, unchecked": ("zig", "1"),
}


def build(directory, kush, zig):
    source = str(HERE / "kush/main.kush")
    llvm = ["--release", "--backend", "llvm"]
    commands = {
        "kush-proofs": ([kush, "build", source, "-o", str(directory / "kush-proofs"), *llvm], {}),
        "kush-checks": (
            [kush, "build", source, "-o", str(directory / "kush-checks"), *llvm],
            {"KUSH_KEEP_PROVED_CHECKS": "1"},
        ),
        "rust": ([
            "rustc", "--edition", "2024", "-C", "opt-level=3", "-C", "panic=abort",
            "-C", "overflow-checks=yes", str(HERE / "rust/main.rs"), "-o", str(directory / "rust"),
        ], {}),
        "c": (["clang", "-O2", str(HERE / "c/main.c"), "-o", str(directory / "c")], {}),
        "zig": ([
            zig, "build-exe", "-O", "ReleaseSafe", "-mcpu", "baseline", str(HERE / "zig/main.zig"),
            f"-femit-bin={directory / 'zig'}", "--cache-dir", str(directory / "zig-cache"),
        ], {}),
    }
    for name, (command, extra) in commands.items():
        done = subprocess.run(command, capture_output=True, env=dict(os.environ, **extra))
        if done.returncode != 0:
            raise SystemExit(f"{name}: {done.stderr.decode()[-3000:]}")
        print(f"built {name}", flush=True)


def run(binary, args, cpu):
    command = [str(binary), *args]
    if cpu is not None:
        command = ["taskset", "-c", str(cpu), *command]
    started = time.perf_counter()
    done = subprocess.run(command, capture_output=True)
    elapsed = time.perf_counter() - started
    if done.returncode != 0:
        raise SystemExit(f"{command}: exit {done.returncode}\n{done.stderr.decode()[-2000:]}")
    return elapsed, done.stdout


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--kush", required=True, type=Path)
    parser.add_argument("--zig", required=True)
    parser.add_argument("--repetitions", type=int, default=15)
    parser.add_argument("--warmups", type=int, default=2)
    parser.add_argument("--cpu", type=int)
    parser.add_argument("--json", type=Path)
    parser.add_argument("--seed", type=int, default=20261127)
    args = parser.parse_args()
    random.seed(args.seed)
    times = {}
    with tempfile.TemporaryDirectory(prefix="kush-proofs-") as directory:
        directory = Path(directory)
        build(directory, str(args.kush.resolve()), args.zig)
        for kernel, kernel_args in KERNELS.items():
            outputs = {
                name: run(directory / binary, [*kernel_args, mode], args.cpu)[1]
                for name, (binary, mode) in VARIANTS.items()
            }
            if len(set(outputs.values())) != 1:
                raise SystemExit(f"{kernel}: different results {outputs}")
            samples = {name: [] for name in VARIANTS}
            for block in range(args.warmups + args.repetitions):
                order = list(VARIANTS)
                random.shuffle(order)
                for name in order:
                    binary, mode = VARIANTS[name]
                    elapsed, _ = run(directory / binary, [*kernel_args, mode], args.cpu)
                    if block >= args.warmups:
                        samples[name].append(elapsed * 1000)
            times[kernel] = samples
            print(f"timed {kernel}", flush=True)
    if args.json:
        args.json.write_text(json.dumps({"times": times}, indent=1))
    print("\n| Kernel | " + " | ".join(VARIANTS) + " |")
    print("| --- |" + " ---: |" * len(VARIANTS))
    for kernel, samples in times.items():
        cells = [f"{statistics.median(samples[name]):.0f}" for name in VARIANTS]
        print(f"| {kernel} | " + " | ".join(cells) + " |")
    print("\nMedian ms, lower is better. Spread (fastest / median / slowest):\n")
    for kernel, samples in times.items():
        print(f"- {kernel}: " + "; ".join(
            f"{name} {min(x):.0f}/{statistics.median(x):.0f}/{max(x):.0f}"
            for name, x in samples.items()
        ))


if __name__ == "__main__":
    main()
