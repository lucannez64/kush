#!/usr/bin/env python3
"""Measure prebuilt, hash-verified JSON benchmark controls on another Linux host.

This performs no compilation. Programs must print only their checksum (emit=0).
wait4 measures each child directly, without a timing wrapper or cumulative RSS.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import random
import resource
import statistics
import subprocess
import time

from run import expected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binaries", type=Path, required=True)
    parser.add_argument("--count", type=int, default=16384)
    parser.add_argument("--rounds", type=int, default=31)
    parser.add_argument("--repetitions", type=int, default=5)
    parser.add_argument("--cpu", type=int, default=min(os.sched_getaffinity(0)))
    args = parser.parse_args()
    if not 1 <= args.count <= 32768 or not 0 <= args.rounds <= 63 or args.repetitions < 3 or args.cpu not in os.sched_getaffinity(0):
        parser.error("invalid count, rounds, repetitions or CPU")
    manifest = json.loads((args.binaries / "manifest.json").read_text())
    for entry in manifest["binaries"]:
        path = args.binaries / entry["name"]
        if path.name != entry["name"] or hashlib.sha256(path.read_bytes()).hexdigest() != entry["sha256"]:
            raise RuntimeError("binary identity mismatch: " + str(path))
    answer = expected(args.count, args.rounds)
    observations = {entry["name"]: [] for entry in manifest["binaries"]}
    start_load = os.getloadavg()
    rng = random.Random(20261103)
    for iteration in range(args.repetitions + 1):
        order = list(manifest["binaries"])
        rng.shuffle(order)
        for entry in order:
            def prepare():
                resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
                os.sched_setaffinity(0, {args.cpu})
            start = time.perf_counter()
            with subprocess.Popen([str(args.binaries / entry["name"]), str(args.count), str(args.rounds), "1", "0"], stdout=subprocess.PIPE, stderr=subprocess.PIPE, preexec_fn=prepare) as process:
                _, status, usage = os.wait4(process.pid, 0)
                process.returncode = os.waitstatus_to_exitcode(status)
                elapsed_ms = (time.perf_counter() - start) * 1000
                stdout, stderr = process.communicate()
                if process.returncode != 0 or int(stdout) != answer:
                    raise RuntimeError(f"{entry['name']}: exit={process.returncode}, stdout={stdout!r}, stderr={stderr!r}")
            if iteration:
                observations[entry["name"]].append({"wall_ms": elapsed_ms, "cpu_ms": (usage.ru_utime + usage.ru_stime) * 1000, "peak_rss_kib": usage.ru_maxrss})
    results = {
        "metadata": {"host": platform.uname()._asdict(), "libc": platform.libc_ver(), "cpu": args.cpu, "cpu_model": next(line.split(":", 1)[1].strip() for line in Path('/proc/cpuinfo').read_text().splitlines() if line.startswith('model name')), "cpu_max": Path('/sys/fs/cgroup/cpu.max').read_text().strip() if Path('/sys/fs/cgroup/cpu.max').exists() else None, "count": args.count, "rounds": args.rounds, "repetitions": args.repetitions, "warmups": 1, "load_average_start": start_load, "load_average_end": os.getloadavg(), "scope": "prebuilt hash-verified binaries; wait4 per child, no compilation", "manifest": manifest},
        "observations": observations,
        "summary": [{"name": name, "wall_ms": statistics.median(x["wall_ms"] for x in samples), "cpu_ms": statistics.median(x["cpu_ms"] for x in samples), "peak_rss_kib": statistics.median(x["peak_rss_kib"] for x in samples)} for name, samples in observations.items()],
    }
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
