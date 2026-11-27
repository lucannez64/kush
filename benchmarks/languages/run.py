#!/usr/bin/env python3
"""Kush against Rust, C and Zig: run time, binary size and build time.

    python3 benchmarks/languages/run.py --kush /path/to/kush --zig /path/to/zig \
        [--repetitions 15] [--cpu 3] [--json results.json]

Workloads (each language's code does the same work and prints the same
number, which is checked before anything is timed):

- `loops`: the three kernels of ../checked-loops (sum, dot, scale then sum).
- `pipeline`: the fused batch of ../feature-pipeline (Rust mode 1).
- `hello`: hello world, for the size of the smallest program.

Every language is built for the same baseline x86-64 CPU. "Checked" builds
check integer overflow as Kush always does: Rust with `-C overflow-checks=yes`,
Zig ReleaseSafe (which also checks indexing, like Kush and Rust), C with
`__builtin_*_overflow` (no bounds checks). Run times are medians of fresh
processes pinned to one CPU, in shuffled order, after two warm-ups. Build
times here are single builds of these small programs; build-scale/measure.py
times larger generated programs. Prints Markdown.
"""
import argparse
import json
import random
import shutil
import statistics
import subprocess
import tempfile
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
BENCHMARKS = HERE.parent

WORKLOADS = {
    "loops": {
        "sum": ["4096", "200001", "0"],
        "dot": ["4096", "200001", "1"],
        "scale, then sum": ["4096", "200001", "2"],
    },
    "pipeline": {"pipeline": ["2097152", "16", "1"]},
    "hello": {},
}


def builds(kush, zig):
    """name -> (workload, language, checked, command producing `{out}`)."""
    loops_kush = ["build", "--manifest-path", str(BENCHMARKS / "checked-loops/kush/Kush.toml")]
    pipe_kush = ["build", "--manifest-path", str(BENCHMARKS / "feature-pipeline/kush/Kush.toml")]
    hello_kush = ["build", str(HERE / "kush/hello.kush")]
    llvm = ["--release", "--backend", "llvm"]
    rust = ["rustc", "--edition", "2024", "-C", "opt-level=3", "-C", "panic=abort"]
    checks = ["-C", "overflow-checks=yes"]
    loops_rs = str(BENCHMARKS / "checked-loops/rust/main.rs")
    pipe_rs = str(BENCHMARKS / "feature-pipeline/rust/main.rs")
    c = lambda compiler, source, *flags: [compiler, "-O2", *flags, str(HERE / "c" / source), "-o"]
    # Zig builds for the host CPU unless told otherwise.
    z = lambda mode, source: [zig, "build-exe", "-O", mode, "-mcpu", "baseline",
                              str(HERE / "zig" / source)]
    table = {}
    for workload, kush_args, rs, c_src, z_src in [
        ("loops", loops_kush, loops_rs, "loops.c", "loops.zig"),
        ("pipeline", pipe_kush, pipe_rs, "pipeline.c", "pipeline.zig"),
    ]:
        table.update({
            f"{workload}/kush-llvm": ("Kush", True, [kush, *kush_args, *llvm, "-o"]),
            f"{workload}/kush-cranelift": ("Kush", True, [kush, *kush_args, "--release", "-o"]),
            f"{workload}/rust-checked": ("Rust", True, [*rust, *checks, rs, "-o"]),
            f"{workload}/rust": ("Rust", False, [*rust, rs, "-o"]),
            f"{workload}/gcc-checked": ("C", True, c("gcc", c_src, "-DCHECKED")),
            f"{workload}/gcc": ("C", False, c("gcc", c_src)),
            f"{workload}/clang-checked": ("C", True, c("clang", c_src, "-DCHECKED")),
            f"{workload}/clang": ("C", False, c("clang", c_src)),
            f"{workload}/zig-safe": ("Zig", True, [*z("ReleaseSafe", z_src), "-femit-bin={out}"]),
            f"{workload}/zig-fast": ("Zig", False, [*z("ReleaseFast", z_src), "-femit-bin={out}"]),
        })
    table.update({
        # A single-file build takes `-o` right after the file.
        "hello/kush-llvm": ("Kush", True, [kush, *hello_kush, "-o", "{out}", *llvm]),
        "hello/kush-cranelift": ("Kush", True, [kush, *hello_kush, "-o", "{out}", "--release"]),
        "hello/rust": ("Rust", False, [*rust, str(HERE / "rust/hello.rs"), "-o"]),
        "hello/gcc": ("C", False, c("gcc", "hello.c")),
        "hello/gcc-static": ("C", False, c("gcc", "hello.c", "-static")),
        "hello/zig-fast": ("Zig", False, [*z("ReleaseFast", "hello.zig"), "-femit-bin={out}"]),
        "hello/zig-small": ("Zig", False, [*z("ReleaseSmall", "hello.zig"), "-femit-bin={out}"]),
    })
    return table


def build(name, command, out, cache):
    if "-femit-bin={out}" in command:
        # A fresh local cache per build, so Zig compiles the program (its
        # global cache keeps the prebuilt runtime, as cc keeps libc).
        command = [part.replace("{out}", str(out)) for part in command]
        command += ["--cache-dir", str(cache / name.replace("/", "-"))]
    elif "{out}" in command:
        command = [part.replace("{out}", str(out)) for part in command]
    else:
        command = [*command, str(out)]
    started = time.perf_counter()
    done = subprocess.run(command, capture_output=True, cwd=out.parent)
    elapsed = time.perf_counter() - started
    if done.returncode != 0:
        raise SystemExit(f"{name}: {' '.join(command)}\n{done.stderr.decode()[-3000:]}")
    stripped = out.with_suffix(".stripped")
    shutil.copy(out, stripped)
    subprocess.run(["strip", str(stripped)], check=True)
    return {"build_s": elapsed, "size": out.stat().st_size, "stripped": stripped.stat().st_size}


def run(binary, args, cpu):
    command = ["taskset", "-c", str(cpu), str(binary), *args] if cpu is not None else [str(binary), *args]
    started = time.perf_counter()
    done = subprocess.run(command, capture_output=True)
    elapsed = time.perf_counter() - started
    if done.returncode != 0:
        raise SystemExit(f"{binary} {args}: exit {done.returncode}\n{done.stderr.decode()[-2000:]}")
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
    table = builds(str(args.kush.resolve()), args.zig)
    random.seed(args.seed)
    data = {"builds": {}, "times": {}}
    with tempfile.TemporaryDirectory(prefix="kush-languages-") as directory:
        directory = Path(directory)
        cache = directory / "zig-cache"
        for name, (_, _, command) in table.items():
            out = directory / name.replace("/", "-")
            data["builds"][name] = build(name, command, out, cache)
            print(f"built {name}", flush=True)
        for workload, cases in WORKLOADS.items():
            names = [name for name in table if name.startswith(workload + "/")]
            for case, case_args in cases.items():
                outputs = {
                    name: run(directory / name.replace("/", "-"), case_args, args.cpu)[1]
                    for name in names
                }
                if len(set(outputs.values())) != 1:
                    raise SystemExit(f"{case}: different results {outputs}")
                samples = {name: [] for name in names}
                for block in range(args.warmups + args.repetitions):
                    order = names[:]
                    random.shuffle(order)
                    for name in order:
                        elapsed, _ = run(directory / name.replace("/", "-"), case_args, args.cpu)
                        if block >= args.warmups:
                            samples[name].append(elapsed * 1000)
                data["times"][case] = samples
                print(f"timed {case}", flush=True)
    if args.json:
        args.json.write_text(json.dumps(data, indent=1))
    report(table, data)


def report(table, data):
    variants = ["kush-llvm", "kush-cranelift", "rust-checked", "rust", "gcc-checked", "gcc",
                "clang-checked", "clang", "zig-safe", "zig-fast"]
    print("\n## Run time (median ms)\n")
    print("| Workload | " + " | ".join(variants) + " |")
    print("| --- |" + " ---: |" * len(variants))
    for case, samples in data["times"].items():
        workload = "pipeline" if case == "pipeline" else "loops"
        cells = [f"{statistics.median(samples[f'{workload}/{v}']):.0f}" for v in variants]
        print(f"| {case} | " + " | ".join(cells) + " |")
    print("\n## Size (bytes, as built / stripped) and build time (s)\n")
    print("| Build | Language | Checked | As built | Stripped | Build s |")
    print("| --- | --- | --- | ---: | ---: | ---: |")
    for name, (language, checked, _) in table.items():
        b = data["builds"][name]
        print(f"| {name} | {language} | {'yes' if checked else 'no'} | {b['size']:,} | "
              f"{b['stripped']:,} | {b['build_s']:.2f} |")


if __name__ == "__main__":
    main()
