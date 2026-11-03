#!/usr/bin/env python3
"""Compare native optimization controls and separately probe pipeline phases."""
import argparse
import datetime
import importlib.util
import json
import os
from pathlib import Path
import random
import re
import statistics
import time

ROOT = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("pipeline_bench", ROOT / "run.py")
base = importlib.util.module_from_spec(spec)
spec.loader.exec_module(base)
BUILD = base.BUILD / "optimizations"


def phases(kush, toolchain, n, rounds, repetitions, cpu):
    source = base.kush_source("kush-fused")
    source = source.replace("pub fn batch(n: i64, fused_mode: Bool) -> i64 ! {alloc, panic}", "pub fn batch(n: i64, fused_mode: Bool) -> i64 ! {io, alloc, panic}")
    source = source.replace("    let ticket = standard_ticket(n);", "    let start = clock();\n    let ticket = standard_ticket(n);")
    source = source.replace("    let transformed = if fused_mode", "    let initialized = clock();\n    let transformed = if fused_mode")
    source = source.replace("    let view = &transformed[..];", "    let mapped = clock();\n    let view = &transformed[..];")
    source = source.replace("    finish(ticket, sum)\n}", "    let reduced = clock();\n    let result = finish(ticket, sum);\n    print_i64(initialized-start); print_i64(mapped-initialized); print_i64(reduced-mapped);\n    result\n}")
    source += "\nfn clock()->i64 ! {io,panic} {match TIME.monotonic_ns(){Result.Ok(n)=>n,Result.Err(_)=>panic()}}\n"
    kush_path = BUILD / "phases.kush"
    kush_path.write_text(source)
    for name, flags in [("kush-default", []), ("kush-release", ["--release"])]:
        base.run([kush, "build", kush_path, "-o", BUILD / ("phases-" + name), *flags])
    rust_dir = BUILD / "phase-rust"
    rust_dir.mkdir(exist_ok=True)
    rust_source = (ROOT / "rust/pipeline.rs").read_text()
    rust_source = rust_source.replace("    let ticket = issue(", "    let start = std::time::Instant::now();\n    let ticket = issue(")
    rust_source = rust_source.replace("    let transformed = match mode", "    let initialized = start.elapsed().as_nanos();\n    let transformed = match mode")
    rust_source = rust_source.replace("    let view = &transformed[..];", "    let mapped = start.elapsed().as_nanos();\n    let view = &transformed[..];")
    rust_source = rust_source.replace("    finish(ticket, sum)\n}", '    let reduced = start.elapsed().as_nanos();\n    let result=finish(ticket,sum);\n    println!("{}\\n{}\\n{}",initialized,mapped-initialized,reduced-mapped);\n    result\n}')
    (rust_dir / "pipeline.rs").write_text(rust_source)
    (rust_dir / "main.rs").write_text((ROOT / "rust/main.rs").read_text())
    base.run(base.rust_flags(toolchain) + [rust_dir / "main.rs", "-o", BUILD / "phases-rust-manual"])
    names = ["kush-default", "kush-release", "rust-manual"]
    samples = {name: [] for name in names}
    rng = random.Random(20261103)
    for at in range(repetitions + 1):
        order = list(names)
        rng.shuffle(order)
        for name in order:
            result = base.run([BUILD / ("phases-" + name), n, rounds, 1], preexec_fn=lambda: base.child_limits(cpu))
            lines = [int(line) for line in result.stdout.splitlines()]
            assert len(lines) == rounds * 3 + 1 and lines[-1] == base.expected(n, rounds), result
            if at:
                samples[name].append({phase: sum(lines[offset:-1:3]) / 1e6 for offset, phase in enumerate(["initialize_ms", "map_ms", "checksum_ms"])})
    observations = [{"variant": name, "observations": samples[name], "medians": {key: statistics.median(sample[key] for sample in samples[name]) for key in samples[name][0]}} for name in names]

    return observations


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--kush", required=True)
    parser.add_argument("--toolchain", default="nightly")
    parser.add_argument("--n", type=int, default=2097152)
    parser.add_argument("--rounds", type=int, default=4)
    parser.add_argument("--repetitions", type=int, default=7)
    parser.add_argument("--cpu", type=int, default=max(os.sched_getaffinity(0)))
    parser.add_argument("--output", type=Path, default=ROOT / "results/optimization")
    args = parser.parse_args()
    if not 1 <= args.n <= 8000000 or not 1 <= args.rounds <= 32 or args.repetitions < 3 or args.cpu not in os.sched_getaffinity(0):
        parser.error("invalid workload, repetitions, or CPU")
    args.kush = str(Path(args.kush).resolve())
    BUILD.mkdir(parents=True, exist_ok=True)
    args.output.mkdir(parents=True, exist_ok=True)
    source = BUILD / "pipeline.kush"
    source.write_text(base.kush_source("kush-fused"))
    variants = [
        ("kush-default", "Kush / default", []),
        ("kush-speed", "Kush / speed only", ["--opt-level", "speed"]),
        ("kush-inline", "Kush / callback inlining only", ["--inline-scalars"]),
        ("kush-release", "Kush / release (speed + inlining)", ["--release"]),
    ]
    builds = []
    for name, label, flags in variants:
        command = [args.kush, "build", source, "-o", BUILD / name, *flags]
        started = time.perf_counter()
        base.run(command)
        builds.append({"variant": name, "command": [str(item) for item in command], "wall_s": time.perf_counter()-started, "binary_sha256": base.sha(BUILD/name)})
    rust_binary = BUILD / "rust-o3"
    command = base.rust_flags(args.toolchain) + [ROOT / "rust/main.rs", "-o", rust_binary]
    base.run(command)
    builds.append({"variant": "rust-o3", "command": [str(item) for item in command], "binary_sha256": base.sha(rust_binary)})
    # Runtime variants all have identical algorithms and safety/overflow policy.
    runtime = [(name, label, BUILD/name, 1) for name, label, _ in variants]
    runtime += [("rust-manual", "Rust CLIF O3 / manual fusion", rust_binary, 1), ("rust-iter", "Rust CLIF O3 / iterator chain", rust_binary, 2)]
    samples = {name: [] for name, _, _, _ in runtime}
    rng = random.Random(20261103)
    for at in range(args.repetitions + 2):
        order = list(runtime)
        rng.shuffle(order)
        for name, _, binary, mode in order:
            observation = base.measure(binary, args.n, args.rounds, mode, args.cpu)
            if at >= 2:
                samples[name].append(observation)
    # Clock probes are compiled separately and never used for headline timings.
    phase_results = phases(args.kush, args.toolchain, args.n, args.rounds, args.repetitions, args.cpu)
    data = {"metadata": {"utc":datetime.datetime.now(datetime.timezone.utc).isoformat(), "git_head":base.run(["git","rev-parse","HEAD"],cwd=base.REPO).stdout.strip(), "shuffle_seed":20261103, "warmups":2, "phase_warmups":1, "source_sha256":base.sha(source), "cpu_model": next(line.split(":",1)[1].strip() for line in Path('/proc/cpuinfo').read_text().splitlines() if line.startswith('model name')), "kush_binary_sha256":base.sha(args.kush), "rustc":base.run(['rustc',f'+{args.toolchain}','-vV']).stdout, "pinned_cpu":args.cpu,"repetitions":args.repetitions,"builds":builds}, "measurements":[{"variant":name,"label":label,"n":args.n,"rounds":args.rounds,"observations":samples[name]} for name,label,_,_ in runtime], "phases":phase_results, "safety":[], "source_lines":base.source_lines(), "text_sections":{}}
    base.report(data,args.output)
    page = (args.output/'report.html').read_text()
    page = re.sub(r'<p class="note">The plain Kush variant.*?</p>', '<p class="note">Only compiler controls differ between the four Kush variants. Release enables speed plus restricted scalar callback inlining. Rust uses the same Cranelift O3 builds as the original comparison. Phase timings use separate clock-probe binaries and are not included in the headline samples.</p>', page, flags=re.S)
    (args.output/'report.html').write_text(page)
    lines = ["# Native release optimization ablation", "", f"Host: {data['metadata']['cpu_model']}; pinned CPU {args.cpu}; {args.repetitions} samples after two warmups.", "", f"Workload: {args.n} elements × {args.rounds} batches. Fresh processes and shuffled implementation order.", "", "| Build | Median wall ms | Median peak RSS KiB |", "|---|---:|---:|"]
    for row in data['summary']:
        lines.append(f"| {row['label']} | {row['median_wall_ms']:.3f} | {row['median_peak_rss_kib']:.0f} |")
    lines += ["", "## Separate phase probes", "", "| Build | Initialize ms | Transform ms | Checksum ms |", "|---|---:|---:|---:|"]
    for phase in phase_results:
        values=phase['medians']
        lines.append(f"| {phase['variant']} | {values['initialize_ms']:.3f} | {values['map_ms']:.3f} | {values['checksum_ms']:.3f} |")
    lines += ["", "Phase probes contain explicit clock calls, use shuffled order, and run in separate binaries. Their medians need not sum to end-to-end medians. Finalization/output/startup are outside those phases.", "", "Both Rust and Kush use Cranelift, with different frontends/settings/standard libraries. RSS is process residency, not live payload. This ablation does not rerun the safety matrix; correctness, safety and ABI validation are covered by the native_release test target and the full compiler gate. See docs/native-optimizations.md and the benchmark README for eligibility and limitations."]
    (args.output/'report.md').write_text('\n'.join(lines)+'\n')
    for phase in phase_results:
        print(phase['variant'],phase['medians'])
    (args.output/'phases.json').write_text(json.dumps(phase_results,indent=2)+'\n')

if __name__ == '__main__':
    main()
