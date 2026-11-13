#!/usr/bin/env python3
"""EFF-CAP-PERF: time the effect perform paths (E-PERF method).

Usage: measure.py <directory with release binaries built from *.kush here>

Each program runs 10^7 iterations of a masked running sum. Runs are
interleaved; the best of RUNS wall times minus the best start-up time of
the empty program is divided by the iteration count.
"""
import subprocess, sys, time, pathlib

RUNS = 7
ITERATIONS = 10_000_000
PROGRAMS = [
    "direct-call",
    "lexical-perform",
    "capability-perform-lexical",
    "capability-perform-in-callee",
    "dynamic-perform-in-callee",
    "checked-call",
    "may-abort-call",
    "multishot-perform-in-callee",
    "oneshot-resume-in-callee",
    "multishot-resume-in-callee",
]

def main():
    binaries = pathlib.Path(sys.argv[1])
    best = {name: float("inf") for name in PROGRAMS + ["empty"]}
    for _ in range(RUNS):
        for name in ["empty"] + PROGRAMS:
            start = time.perf_counter()
            subprocess.run([binaries / name], check=False)
            best[name] = min(best[name], time.perf_counter() - start)
    for name in PROGRAMS:
        per = (best[name] - best["empty"]) / ITERATIONS * 1e9
        print(f"{name:32} {per:6.2f} ns/iteration")

if __name__ == "__main__":
    main()
