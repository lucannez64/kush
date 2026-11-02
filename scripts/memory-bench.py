#!/usr/bin/env python3
"""Reproducible memory/performance observations for the checked memory subset.

The harness builds one native binary per workload, measures it several times,
and reports:

* the stable `allocation-stats:` counters from both the reference evaluator and
  the native binary at a small parity size;
* native wall time and maximum resident set size (RSS) from `/usr/bin/time`;
* the opt-in native `allocator-pool:` retention line.

It deliberately does not claim that one spelling is faster. Results are
medians of repeated runs on the machine that invoked the harness. Use the same
binary, iteration count, and machine to compare two revisions.

Usage:
    python3 scripts/memory-bench.py [--kush target/release/kush] [--repeats 7]

Build the binary first, for example:

    cargo build --release -p kush
"""
from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import statistics
import subprocess
import sys
import tempfile
import time
from dataclasses import dataclass, field
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
STATS = re.compile(
    r"allocation-stats: allocations=(\d+) deallocations=(\d+) peak-live=(\d+) "
    r"buffer-growths=(\d+) reuses=(\d+) fusions=(\d+)"
)
POOL = re.compile(
    r"allocator-pool: hits=(\d+) misses=(\d+) retains=(\d+) releases=(\d+) "
    r"drained=(\d+) retained-bytes=(\d+) peak-retained-bytes=(\d+)"
)
TIME = re.compile(r"__bench__ wall=([0-9.]+) rss_kib=(\d+)")


@dataclass
class Stats:
    allocations: int
    deallocations: int
    peak_live: int
    buffer_growths: int
    reuses: int
    fusions: int

    def balanced(self) -> bool:
        return self.allocations == self.deallocations


@dataclass
class Observation:
    workload: str
    iterations: int
    stats: Stats
    wall: float | None = None
    rss_kib: int | None = None
    pool_peak_retained: int | None = None
    parity: bool | None = None


@dataclass
class Workload:
    name: str
    description: str
    source: str
    native_iterations: int
    parity_iterations: int


def workload_source(name: str, n: int) -> str:
    if name == "box-reuse":
        return f"""fn main() -> i64 ! {{alloc, panic}} {{
    let mut owner = Box.new(0);
    let mut i = 0;
    while i < {n} {{
        let current = Box.read(&owner);
        owner = Box.reuse(owner, current + 1);
        i = i + 1;
    }}
    drop(Box.take(owner));
    0
}}"""
    if name == "box-new":
        return f"""fn main() -> i64 ! {{alloc, panic}} {{
    let mut owner = Box.new(0);
    let mut i = 0;
    while i < {n} {{
        let current = Box.read(&owner);
        owner = Box.new(current + 1);
        i = i + 1;
    }}
    drop(Box.take(owner));
    0
}}"""
    if name == "vec-map-in-place":
        return f"""fn inc(x: i64) -> i64 ! {{panic}} {{ x + 1 }}
fn main() -> i64 ! {{alloc, panic}} {{
    let mut values: Vec<i64> = Vec.new();
    let mut i = 0;
    while i < {n} {{
        values = Vec.push(values, i);
        i = i + 1;
    }}
    let values = Vec.map_in_place(values, inc);
    drop(Vec.get(&values, {n - 1}));
    0
}}"""
    if name == "bytes-push":
        return f"""fn main() -> i64 ! {{alloc, panic}} {{
    let mut buffer = Bytes.with_capacity({n});
    let mut i = 0;
    while i < {n} {{
        buffer = Bytes.push_reserved(buffer, i % 256);
        i = i + 1;
    }}
    drop(Bytes.len(&buffer));
    0
}}"""
    if name == "arena-alloc":
        return f"""fn main() -> i64 ! {{alloc, panic}} {{
    let arena = Arena.new();
    let mut i = 0;
    while i < {n} {{
        let boxed = Arena.alloc(&arena, i);
        drop(ArenaBox.take(boxed));
        i = i + 1;
    }}
    drop(arena);
    0
}}"""
    raise KeyError(name)


WORKLOADS = [
    Workload(
        "box-reuse",
        "one allocation, repeated Box.reuse",
        "",
        1_000_000,
        500,
    ),
    Workload(
        "box-new",
        "one allocation per update with Box.new",
        "",
        1_000_000,
        500,
    ),
    Workload(
        "vec-map-in-place",
        "push then one allocation-preserving Vec.map_in_place",
        "",
        262_144,
        500,
    ),
    Workload(
        "bytes-push",
        "reserved byte-buffer pushes",
        "",
        1_048_576,
        500,
    ),
    Workload(
        "arena-alloc",
        "region allocation and take for each value",
        "",
        1_000_000,
        500,
    ),
]


def parse_stats(stderr: str) -> Stats:
    match = STATS.search(stderr)
    if not match:
        raise RuntimeError(f"missing allocation-stats line:\n{stderr}")
    return Stats(*(int(value) for value in match.groups()))


def parse_pool(stderr: str) -> int | None:
    match = POOL.search(stderr)
    return int(match.group(7)) if match else None


def run(command: list[str], env: dict[str, str] | None = None) -> subprocess.CompletedProcess:
    return subprocess.run(
        command,
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        env=env,
    )


def build(kush: Path, source: Path, binary: Path) -> None:
    run([str(kush), "build", str(source), "-o", str(binary), "--stats"])


def reference_stats(kush: Path, source: Path) -> Stats:
    result = run([str(kush), "eval", str(source), "--stats"])
    return parse_stats(result.stderr.decode())


def measure(binary: Path, repeats: int, pool_stats: bool) -> tuple[Stats, float | None, int | None, int | None]:
    time_command = shutil.which("time")
    env = os.environ.copy()
    if pool_stats:
        env["KUSH_ALLOCATOR_POOL_STATS"] = "1"
    walls: list[float] = []
    rss: list[int] = []
    stats: Stats | None = None
    pool_peak: int | None = None
    for attempt in range(repeats + 1):
        command = [str(binary)]
        if time_command:
            command = [
                time_command,
                "-f",
                "__bench__ wall=%e rss_kib=%M",
                str(binary),
            ]
        started = time.perf_counter()
        result = run(command, env=env)
        elapsed = time.perf_counter() - started
        parsed = parse_stats(result.stderr.decode())
        if stats is None:
            stats = parsed
        elif parsed != stats:
            raise RuntimeError("allocation counters changed between identical runs")
        pool = parse_pool(result.stderr.decode())
        if pool is not None:
            pool_peak = pool
        if time_command:
            match = TIME.search(result.stderr.decode())
            if match and attempt > 0:
                rss.append(int(match.group(2)))
        # The first run is warm-up for timing only.
        if attempt > 0:
            walls.append(elapsed)
    if stats is None:
        raise RuntimeError("no run completed")
    return (
        stats,
        statistics.median(walls) if walls else None,
        int(statistics.median(rss)) if rss else None,
        pool_peak,
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--kush",
        default=str(REPO / "target" / "release" / "kush"),
        help="path to the kush CLI binary (default: target/release/kush)",
    )
    parser.add_argument("--repeats", type=int, default=7, help="timed runs after warm-up")
    parser.add_argument("--json", type=Path, help="write the observations as JSON")
    parser.add_argument(
        "--native-scale",
        type=float,
        default=1.0,
        help="scale native iteration counts (for quick smoke runs)",
    )
    args = parser.parse_args()
    kush = Path(args.kush).resolve()
    if not kush.is_file():
        print(f"missing kush binary: {kush}\nbuild it with: cargo build --release -p kush", file=sys.stderr)
        return 2
    observations: list[Observation] = []
    with tempfile.TemporaryDirectory(prefix="kush-memory-bench-") as temporary:
        root = Path(temporary)
        for workload in WORKLOADS:
            native_iterations = max(1, int(workload.native_iterations * args.native_scale))
            native_source = root / f"{workload.name}-native.kush"
            native_source.write_text(workload_source(workload.name, native_iterations))
            binary = root / f"{workload.name}-native"
            build(kush, native_source, binary)
            stats, wall, rss, pool_peak = measure(binary, args.repeats, True)
            if not stats.balanced():
                raise RuntimeError(f"{workload.name}: unbalanced native cleanup {stats}")
            parity_source = root / f"{workload.name}-parity.kush"
            parity_source.write_text(workload_source(workload.name, workload.parity_iterations))
            parity_binary = root / f"{workload.name}-parity"
            build(kush, parity_source, parity_binary)
            native_parity, _, _, _ = measure(parity_binary, 1, False)
            reference_parity = reference_stats(kush, parity_source)
            parity = native_parity == reference_parity
            observations.append(
                Observation(
                    workload=workload.name,
                    iterations=native_iterations,
                    stats=stats,
                    wall=wall,
                    rss_kib=rss,
                    pool_peak_retained=pool_peak,
                    parity=parity,
                )
            )
            if not parity:
                print(
                    f"{workload.name}: reference/native parity mismatch\n"
                    f"  reference: {reference_parity}\n  native:    {native_parity}",
                    file=sys.stderr,
                )
    print(f"{'workload':<20} {'iters':>10} {'allocs':>10} {'reuses':>10} {'wall_s':>10} {'rss_kib':>10} {'pool_peak':>10} parity")
    for observation in observations:
        wall = f"{observation.wall:.4f}" if observation.wall is not None else "-"
        rss = str(observation.rss_kib) if observation.rss_kib is not None else "-"
        pool = (
            str(observation.pool_peak_retained)
            if observation.pool_peak_retained is not None
            else "-"
        )
        print(
            f"{observation.workload:<20} {observation.iterations:>10} "
            f"{observation.stats.allocations:>10} {observation.stats.reuses:>10} "
            f"{wall:>10} {rss:>10} {pool:>10} "
            f"{'ok' if observation.parity else 'MISMATCH'}"
        )
    if args.json:
        args.json.write_text(
            json.dumps(
                [
                    {
                        "workload": observation.workload,
                        "iterations": observation.iterations,
                        "allocations": observation.stats.allocations,
                        "deallocations": observation.stats.deallocations,
                        "peak_live": observation.stats.peak_live,
                        "buffer_growths": observation.stats.buffer_growths,
                        "reuses": observation.stats.reuses,
                        "fusions": observation.stats.fusions,
                        "wall_seconds": observation.wall,
                        "max_rss_kib": observation.rss_kib,
                        "pool_peak_retained_bytes": observation.pool_peak_retained,
                        "reference_native_parity": observation.parity,
                    }
                    for observation in observations
                ],
                indent=2,
            )
            + "\n"
        )
    if not all(observation.parity for observation in observations):
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
