#!/usr/bin/env python3
"""What Kush's task runtime costs (TASKS-BENCH, docs/tasks-on-handlers.md).

    python3 benchmarks/tasks/run.py --kush /path/to/kush \
        [--repetitions 15] [--cpu 5] [--json results.json]

Builds the program with the LLVM and the Cranelift backend and times each
kernel: two tasks yielding in turn, a spawn joined at once, batches of 64
spawned children joined by their scope, and a one-byte echo over a loopback
TCP connection between two tasks on the reactor. Every build must print the
same number before anything is timed. Prints Markdown, with the time per
operation, which is the budget (decision T5) the move of tasks to std on
fiber handlers is held to.
"""
import argparse
import json
import random
import statistics
import subprocess
import tempfile
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent

# name -> (rounds, kernel argument, operations per round, operation)
KERNELS = {
    "yield": (300000, "0", 2, "yield"),
    "spawn-join": (250000, "1", 1, "spawn and join"),
    "spawn-scope": (300032, "2", 1, "spawn, scope join"),
    "echo": (25000, "3", 1, "round trip"),
}

VARIANTS = {
    "LLVM": ["--release", "--backend", "llvm"],
    "Cranelift": ["--release"],
}


def build(directory, kush):
    source = str(HERE / "kush/main.kush")
    for name, flags in VARIANTS.items():
        command = [kush, "build", source, "-o", str(directory / name), *flags]
        done = subprocess.run(command, capture_output=True)
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
    parser.add_argument("--repetitions", type=int, default=15)
    parser.add_argument("--warmups", type=int, default=2)
    parser.add_argument("--cpu", type=int)
    parser.add_argument("--json", type=Path)
    parser.add_argument("--seed", type=int, default=20261127)
    args = parser.parse_args()
    random.seed(args.seed)
    times = {}
    with tempfile.TemporaryDirectory(prefix="kush-tasks-") as directory:
        directory = Path(directory)
        build(directory, str(args.kush.resolve()))
        for kernel, (rounds, argument, _, _) in KERNELS.items():
            kernel_args = [str(rounds), argument]
            outputs = {name: run(directory / name, kernel_args, args.cpu)[1] for name in VARIANTS}
            if len(set(outputs.values())) != 1:
                raise SystemExit(f"{kernel}: different results {outputs}")
            samples = {name: [] for name in VARIANTS}
            for block in range(args.warmups + args.repetitions):
                order = list(VARIANTS)
                random.shuffle(order)
                for name in order:
                    elapsed, _ = run(directory / name, kernel_args, args.cpu)
                    if block >= args.warmups:
                        samples[name].append(elapsed * 1000)
            times[kernel] = samples
            print(f"timed {kernel}", flush=True)
    if args.json:
        args.json.write_text(json.dumps({"times": times}, indent=1))
    print("\n| Kernel | Operation | " + " | ".join(f"{name} ms | {name} ns/op" for name in VARIANTS) + " |")
    print("| --- | --- |" + " ---: | ---: |" * len(VARIANTS))
    for kernel, samples in times.items():
        rounds, _, per_round, operation = KERNELS[kernel]
        cells = []
        for name in VARIANTS:
            median = statistics.median(samples[name])
            cells.append(f"{median:.0f} | {median * 1e6 / (rounds * per_round):.0f}")
        print(f"| {kernel} | {operation} | " + " | ".join(cells) + " |")
    print("\nMedian of the whole process, startup included. Spread (fastest / median / slowest):\n")
    for kernel, samples in times.items():
        print(f"- {kernel}: " + "; ".join(
            f"{name} {min(x):.0f}/{statistics.median(x):.0f}/{max(x):.0f}"
            for name, x in samples.items()
        ))


if __name__ == "__main__":
    main()
