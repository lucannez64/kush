#!/usr/bin/env python3
"""Measure native builds with/without a warm C runtime cache, same compiler."""
import argparse
import datetime
import importlib.util
import json
import os
from pathlib import Path
import random
import statistics
import tempfile
import time

ROOT = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("pipeline_bench", ROOT / "run.py")
base = importlib.util.module_from_spec(spec)
spec.loader.exec_module(base)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--kush", required=True, type=Path)
    parser.add_argument("--repetitions", type=int, default=7)
    parser.add_argument("--cpu", type=int, default=max(os.sched_getaffinity(0)))
    parser.add_argument("--output", type=Path, default=ROOT / "results/build-time.json")
    args = parser.parse_args()
    if args.repetitions < 3 or args.cpu not in os.sched_getaffinity(0):
        parser.error("invalid repetitions or CPU")
    compiler = args.kush.resolve()
    with tempfile.TemporaryDirectory(prefix="kush-build-bench-") as directory:
        root = Path(directory)
        source = root / "pipeline.kush"
        source.write_text(base.kush_source("kush-fused"))
        command = [compiler, "build", source, "-o", root / "program", "--release"]
        environment = dict(os.environ, KUSH_RUNTIME_CACHE=str(root / "runtime-cache"))
        environment.pop("KUSH_NO_RUNTIME_CACHE", None)
        samples = {"warm-cache": [], "cache-disabled": []}

        def measure(disabled):
            child_environment = dict(environment)
            if disabled:
                child_environment["KUSH_NO_RUNTIME_CACHE"] = "1"
            started = time.perf_counter()
            base.run(command, env=child_environment, preexec_fn=lambda: base.child_limits(args.cpu))
            elapsed = (time.perf_counter() - started) * 1000
            result = base.run([root / "program", 128, 1, 1])
            assert result.stdout.strip() == str(base.expected(128, 1)), result
            return elapsed

        cold = measure(False)
        rng = random.Random(20261103)
        for at in range(args.repetitions + 1):
            order = list(samples)
            rng.shuffle(order)
            for name in order:
                elapsed = measure(name == "cache-disabled")
                if at:
                    samples[name].append(elapsed)
        data = {
            "utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
            "git_head": base.run(["git", "rev-parse", "HEAD"], cwd=base.REPO).stdout.strip(),
            "compiler_sha256": base.sha(compiler),
            "source_sha256": base.sha(source),
            "command": [str(item) for item in command],
            "pinned_cpu": args.cpu,
            "repetitions": args.repetitions,
            "shuffle_seed": 20261103,
            "initial_cold_cache_ms": cold,
            "samples_ms": samples,
            "median_ms": {name: statistics.median(values) for name, values in samples.items()},
            "note": "Total native CLI build time, including checking/codegen/dependency scan/link; execution correctness probe excluded. Cache-disabled skips lookup and recompiles C. Initial cold sample is descriptive, not a median.",
        }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(data, indent=2) + "\n")
    print(json.dumps(data["median_ms"], indent=2))


if __name__ == "__main__":
    main()
