#!/usr/bin/env python3
"""Reproducible scalar pipeline comparison. Linux, no third-party Python deps."""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import platform
import random
import re
import resource
import shutil
import statistics
import subprocess
import time

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parents[1]
BUILD = ROOT / "build"
STATS = re.compile(r"allocation-stats: allocations=(\d+) deallocations=(\d+) peak-live=(\d+) buffer-growths=(\d+) reuses=(\d+) fusions=(\d+)")
RUST_STATS = re.compile(r"rust-alloc: allocations=(\d+) deallocations=(\d+) reallocations=(\d+) live-bytes=(\d+) peak-requested-bytes=(\d+)")
VARIANTS = [
    ("kush-fused", "Kush / automatic fusion", "kush", 1),
    ("kush-plain", "Kush / fusion, contracts removed", "kush", 1),
    ("kush-staged", "Kush / two passes", "kush", 0),
    ("rust-manual", "Rust CLIF O3 / manual fusion", "rust", 1),
    ("rust-iter", "Rust CLIF O3 / iterator chain", "rust", 2),
    ("rust-staged", "Rust CLIF O3 / two passes", "rust", 0),
    ("rust-o0", "Rust CLIF O0 / manual fusion", "rust", 1),
]


def run(command, **kwargs):
    result = subprocess.run([str(x) for x in command], capture_output=True, text=True, **kwargs)
    if result.returncode:
        raise RuntimeError(f"command failed ({result.returncode}): {command}\n{result.stdout}\n{result.stderr}")
    return result


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def rust_flags(toolchain, opt="3"):
    # Absence of the backend is fatal. There is deliberately no LLVM fallback.
    return ["rustc", f"+{toolchain}", "-Zcodegen-backend=cranelift", f"-Copt-level={opt}",
            "-Coverflow-checks=yes", "-Cpanic=abort", "-Ctarget-cpu=x86-64", "--edition=2024"]


def kush_source(variant):
    core = (ROOT / "kush/src/pipeline.kush").read_text()
    core = core.replace("module feature_pipeline.pipeline;", "")
    if variant == "kush-staged":
        core = core.replace("Vec.map_in_place(Vec.map_in_place(values, scrub), tag)",
                            "let intermediate = Vec.map_in_place(values, scrub);\n    Vec.map_in_place(intermediate, tag)")
    if variant == "kush-plain":
        # Same valid runtime path and ABI; remove only contracts/erased binders.
        core = core.replace("key: i64, erased approved: AuthorizedKey<key>, audit: i64 @[0]", "key: i64")
        core = core.replace("issue(23130, AuthorizedKey.Standard::<23130>, audit)", "issue(23130)")
        core = core.replace(" @[1]", "").replace(" @[2]", "")
        core = core.replace("#[noalloc]\n", "").replace("#[nosuspend]\n", "")
        assert "erased approved:" not in core and "@[" not in core
        assert "#[noalloc]" not in core and "#[nosuspend]" not in core
    main = (ROOT / "kush/main.kush").read_text()
    main = main.replace("module feature_pipeline;", "")
    main = main.replace("use feature_pipeline.pipeline;", "").replace("pipeline.batch", "batch")
    return "module feature_bench;\n" + core + "\n" + main


def build(kush, toolchain):
    BUILD.mkdir(exist_ok=True)
    builds = []
    for variant in [v[0] for v in VARIANTS if v[2] == "kush"]:
        source = BUILD / f"{variant}.kush"
        source.write_text(kush_source(variant))
        for instrument in [False, True]:
            output = BUILD / (variant + ("-stats" if instrument else ""))
            command = [kush, "build", source, "-o", output] + (["--stats"] if instrument else [])
            started = time.perf_counter()
            result = run(command)
            builds.append({"variant": output.name, "command": [str(x) for x in command],
                           "wall_s": time.perf_counter() - started, "stderr": result.stderr,
                           "source_sha256": sha(source), "binary_sha256": sha(output),
                           "binary_bytes": output.stat().st_size})
    for opt in ["3", "0"]:
        for instrument in [False, True]:
            name = ("rust-o3" if opt == "3" else "rust-o0") + ("-stats" if instrument else "")
            output = BUILD / name
            command = rust_flags(toolchain, opt) + [str(ROOT / "rust/main.rs"), "-o", str(output)]
            if instrument:
                command += ["--cfg", "instrument"]
            started = time.perf_counter()
            result = run(command)
            builds.append({"variant": name, "command": command, "wall_s": time.perf_counter() - started,
                           "stderr": result.stderr, "binary_sha256": sha(output), "binary_bytes": output.stat().st_size})
    return builds


def executable(variant, instrument=False):
    if variant.startswith("rust"):
        name = "rust-o0" if variant == "rust-o0" else "rust-o3"
    else:
        name = variant
    return BUILD / (name + ("-stats" if instrument else ""))


def expected(n, rounds):
    cycle = sum(((i & 65535) ^ (i & 255)) ^ 23130 for i in range(65536))
    tail = sum(((i & 65535) ^ (i & 255)) ^ 23130 for i in range(n % 65536))
    return rounds * (n // 65536 * cycle + tail + 23130)


def child_limits(cpu=None):
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    if cpu is not None:
        os.sched_setaffinity(0, {cpu})


def correctness():
    for variant, _, _, mode in VARIANTS:
        for n in [1, 257, 65537]:
            result = run([executable(variant), n, 2, mode], preexec_fn=child_limits)
            assert int(result.stdout.strip()) == expected(n, 2), (variant, n, result)
        for config in [(0, 1), (1, -1), (8_000_001, 1), (1, 33)]:
            result = subprocess.run([str(executable(variant)), *map(str, config), str(mode)], capture_output=True)
            assert result.returncode == 2, (variant, config, result)


def reference_correctness(kush):
    for variant, _, language, mode in VARIANTS:
        if language == "kush":
            result = run([kush, "eval", BUILD / f"{variant}.kush", "--", 257, 2, mode], timeout=30)
            assert int(result.stdout.strip()) == expected(257, 2), (variant, result)


def diagnostics(n, rounds):
    observations = []
    for variant, _, language, mode in VARIANTS:
        result = run([executable(variant, True), n, rounds, mode], preexec_fn=child_limits)
        assert int(result.stdout.strip()) == expected(n, rounds)
        if language == "kush":
            match = STATS.search(result.stderr)
            assert match, result.stderr
            values = dict(zip(["allocations", "deallocations", "peak_live", "buffer_growths", "reuses", "static_fusions"], map(int, match.groups())))
            baseline = run([executable(variant, True), n, 0, mode], preexec_fn=child_limits)
            base = dict(zip(values.keys(), map(int, STATS.search(baseline.stderr).groups())))
            values["whole_process_baseline"] = base
            values["workload_logical_allocations"] = values["allocations"] - base["allocations"]
            assert values["allocations"] == values["deallocations"], values
            assert values["static_fusions"] == (0 if variant == "kush-staged" else 1), values
            assert values["workload_logical_allocations"] == 2 * rounds, values
        else:
            match = RUST_STATS.search(result.stderr)
            assert match, result.stderr
            values = dict(zip(["workload_allocator_calls", "workload_deallocator_calls", "reallocations", "live_requested_bytes", "peak_requested_bytes"], map(int, match.groups())))
            assert values["workload_allocator_calls"] == values["workload_deallocator_calls"] and values["live_requested_bytes"] == 0, values
        observations.append({"variant": variant, **values})
    return observations


SAFETY = [
    ("use_after_move", False, r"move", r"E0382"),
    ("borrow_invalidation", False, r"borrow|live", r"E0505"),
    ("exclusive_alias", False, r"borrow|exclusive|live", r"E0499"),
    ("exact_use_grade", True, r"grade|used|use", None),
    ("linear_discard", True, r"linear|consum", None),
    ("unauthorized_key", False, r"expected|mismatch|proof", r"private"),
    ("noalloc_violation", True, r"noalloc|alloc", None),
    ("erased_observation", False, r"grade|observ", r"mismatched types"),
]


def safety(kush, toolchain):
    results = []
    for name, rust_accepts, kush_pattern, rust_pattern in SAFETY:
        k = subprocess.run([kush, "check", str(ROOT / f"safety/kush/{name}.kush")], capture_output=True, text=True)
        header = k.stderr.split(" -->")[0]
        assert k.returncode != 0 and re.search(kush_pattern, header, re.I), (name, k.stderr)
        output = BUILD / f"safety-{name}"
        r = subprocess.run(rust_flags(toolchain) + [str(ROOT / f"safety/rust/{name}.rs"), "-o", str(output)], capture_output=True, text=True)
        assert (r.returncode == 0) == rust_accepts, (name, r.stderr)
        if rust_pattern:
            assert re.search(rust_pattern, r.stderr), (name, r.stderr)
        row = {"case": name, "kush_compile": "rejected", "rust_compile": "accepted" if rust_accepts else "rejected",
               "kush_diagnostic": header.strip(), "rust_diagnostic": r.stderr[:1200]}
        if name == "linear_discard":
            runtime = subprocess.run([str(output)], capture_output=True, text=True, preexec_fn=child_limits)
            assert runtime.returncode != 0 and "batch ticket was not finished" in runtime.stderr
            row["rust_runtime"] = "drop guard aborts"
        results.append(row)
    output = BUILD / "safety-forget-ticket"
    run(rust_flags(toolchain) + [ROOT / "safety/rust/forget_ticket.rs", "-o", output])
    run([output], preexec_fn=child_limits)
    results.append({"case": "forget_ticket", "kush_compile": "no corresponding safe forget builtin in this API",
                    "rust_compile": "accepted", "rust_runtime": "exits normally; bypasses Drop guard"})
    return results


def measure(binary, n, rounds, mode, cpu):
    command = ["/usr/bin/time", "-f", "BENCH_RSS_KIB=%M\nBENCH_USER_S=%U\nBENCH_SYSTEM_S=%S", str(binary), str(n), str(rounds), str(mode)]
    started = time.perf_counter_ns()
    result = run(command, preexec_fn=lambda: child_limits(cpu), timeout=120)
    wall_ms = (time.perf_counter_ns() - started) / 1e6
    assert int(result.stdout.strip()) == expected(n, rounds)
    match = re.search(r"BENCH_RSS_KIB=(\d+)", result.stderr)
    assert match, result.stderr
    return {"wall_ms": wall_ms, "peak_rss_kib": int(match.group(1)),
            "user_s": float(re.search(r"BENCH_USER_S=([0-9.]+)", result.stderr).group(1)),
            "system_s": float(re.search(r"BENCH_SYSTEM_S=([0-9.]+)", result.stderr).group(1))}


def text_hashes():
    if not shutil.which("objcopy"):
        return {"available": False}
    hashes = {}
    for name in ["kush-fused", "kush-plain"]:
        output = BUILD / f"{name}.text"
        run(["objcopy", "-O", "binary", "--only-section=.text", executable(name), output])
        hashes[name] = sha(output)
    return {"available": True, "hashes": hashes, "identical_text": len(set(hashes.values())) == 1}


def source_lines():
    groups = {"Kush production": ["kush/main.kush", "kush/src/pipeline.kush"],
              "Rust production": ["rust/main.rs", "rust/pipeline.rs"],
              "Rust allocation instrumentation (excluded)": ["rust/allocation.rs"]}
    return {name: {"files": files, "nonblank_noncomment_lines": sum(sum(bool(line.strip()) and not line.lstrip().startswith("//") for line in (ROOT / file).read_text().splitlines()) for file in files)} for name, files in groups.items()}


def metadata(args, builds):
    sysroot = Path(run(["rustc", f"+{args.toolchain}", "--print", "sysroot"]).stdout.strip())
    backends = sorted(sysroot.glob("lib/rustlib/*/codegen-backends/*cranelift*"))
    backend_files = [{"file": str(path), "sha256": sha(path)} for path in backends]
    cpu = next((line.split(":", 1)[1].strip() for line in Path("/proc/cpuinfo").read_text().splitlines() if line.startswith("model name")), "unknown")
    return {"utc": datetime.datetime.now(datetime.timezone.utc).isoformat(), "host": platform.platform(),
            "cpu_model": cpu, "cpu_affinity": sorted(os.sched_getaffinity(0)), "pinned_cpu": args.cpu,
            "load_before": os.getloadavg(), "warmups": args.warmups, "repetitions": args.repetitions, "shuffle_seed": 20261103,
            "workload_sources": {str(path.relative_to(ROOT)): sha(path) for directory in ["kush", "rust"] for path in sorted((ROOT / directory).rglob("*")) if path.suffix in [".kush", ".rs"]}, "kush_version": run([args.kush, "--version"]).stdout.strip(),
            "kush_binary_sha256": sha(args.kush), "git_head": run(["git", "rev-parse", "HEAD"], cwd=REPO).stdout.strip(),
            "rustc": run(["rustc", f"+{args.toolchain}", "-vV"]).stdout.strip(),
            "kush_cranelift_dependency": re.search(r'cranelift-codegen = "([^"]+)"', (REPO / "crates/kush/Cargo.toml").read_text()).group(1),
            "rust_flags": rust_flags(args.toolchain), "rust_backend_libraries": backend_files, "builds": builds,
            "python": platform.python_version(), "c_compiler": run(["cc", "--version"]).stdout.splitlines()[0],
            "method": "fresh processes; shuffled blocks; pinned child CPU; high-resolution parent wall clock includes GNU time/spawn/startup/output; RSS from GNU time; stats builds excluded from timing",
            "stdlib_caveat": "Rust uses installed prebuilt standard libraries, potentially LLVM-built; Cranelift is explicitly selected for this crate and its monomorphizations. Kush links a cc-built C runtime. Backend versions/optimization pipelines need not match."}


def report(data, out):
    rows = []
    for sample in data["measurements"]:
        observations = sample["observations"]
        wall = [o["wall_ms"] for o in observations]
        rows.append({"variant": sample["variant"], "label": sample["label"], "n": sample["n"], "rounds": sample["rounds"],
                     "median_wall_ms": statistics.median(wall), "min_wall_ms": min(wall), "max_wall_ms": max(wall),
                     "median_peak_rss_kib": statistics.median(o["peak_rss_kib"] for o in observations)})
    data["summary"] = rows
    (out / "results.json").write_text(json.dumps(data, indent=2) + "\n")
    md = ["# Feature pipeline — measured results", "", f"Host: {data['metadata']['cpu_model']}", "", "| Case | Implementation | Median wall ms | Peak RSS KiB (median) |", "|---|---|---:|---:|"]
    for row in rows:
        md.append(f"| n={row['n']}, rounds={row['rounds']} | {row['label']} | {row['median_wall_ms']:.3f} | {row['median_peak_rss_kib']:.0f} |")
    md += ["", "Measurements include startup/output, use fresh processes and a pinned CPU, and exclude allocation instrumentation.",
           "RSS is process peak residency, not live payload bytes. These results describe this workload, machine and compiler configuration only.",
           "", "## Safety probes", "", "| Case | Kush compilation | Rust compilation | Rust runtime note |", "|---|---|---|---|"]
    for row in data["safety"]:
        md.append(f"| {row['case']} | {row['kush_compile']} | {row['rust_compile']} | {row.get('rust_runtime', '')} |")
    md += ["", "## Source size (not a quality score)", "", json.dumps(data["source_lines"], indent=2), "", "## Annotation erasure experiment", "", json.dumps(data["text_sections"], indent=2), "", "See the project README for the fairness limits and the exact meaning of each feature."]
    (out / "report.md").write_text("\n".join(md) + "\n")
    payload = json.dumps(rows).replace("</", "<\\/")
    page = '''<!doctype html><html><head><meta charset="utf-8"><title>Kush / Rust Cranelift benchmark</title><style>
body{font-family:var(--font-sans,system-ui);font-size:14px;color:var(--foreground,#182536);margin:0;padding:0}select{font:inherit;padding:7px;background:var(--secondary,#eef2f8);color:var(--foreground,#182536);border:1px solid var(--border,#b7c6d8);border-radius:var(--radius,6px)}label{display:inline-block;margin:0 12px 12px 0}.row{display:grid;grid-template-columns:minmax(140px,280px) minmax(60px,1fr) 100px;align-items:center;gap:10px;margin:12px 0}.track{background:var(--secondary,#e5edf5);border-radius:4px;height:26px}.bar{height:26px;background:var(--chart-1,#16866b);border-radius:4px}.rust{background:var(--chart-2,#c27e24)}.note{color:var(--muted-foreground,#52657a);line-height:1.55}#chart{min-height:290px}code{font-family:var(--font-mono,monospace)}@media(max-width:500px){.row{grid-template-columns:150px minmax(35px,1fr) 70px;gap:6px;font-size:12px}select{max-width:100%}}
</style></head><body>
<p><strong>Feature pipeline · both compilers use Cranelift</strong></p><p class="note">Local measured results · lower is better · one scalar workload, not a general language ranking.</p>
<label>Workload <select id="case"></select></label> <label>Metric <select id="metric"><option value="median_wall_ms">Median wall time (ms)</option><option value="median_peak_rss_kib">Median process peak RSS (KiB)</option></select></label><div id="chart"></div>
<p class="note">Fresh processes, shuffled repetitions, pinned CPU. Wall time includes startup and output; RSS includes runtimes and allocator retention. Rust O3 means rustc flags, not an identical optimization pipeline to Kush. Stats builds are excluded from timings.</p>
<p class="note">The plain Kush variant removes the usage/effect contracts and erased binders from the same valid program. Staged controls use two in-place passes. Rust's iterator chain is included alongside manual fusion. Safety results are compile/runtime probes, not performance scores or a proof of soundness.</p>
<script>const rows=PAYLOAD;const sel=document.getElementById('case'),metric=document.getElementById('metric');const keys=[...new Set(rows.map(r=>r.n+':'+r.rounds))];for(const key of keys){const [n,k]=key.split(':');sel.add(new Option(Number(n).toLocaleString()+' elements × '+k+' batches',key));}function draw(){const chosen=rows.filter(r=>r.n+':'+r.rounds===sel.value),max=Math.max(...chosen.map(r=>r[metric.value]));const box=document.getElementById('chart');box.replaceChildren();for(const r of chosen){const row=document.createElement('div');row.className='row';const label=document.createElement('span');label.textContent=r.label;const track=document.createElement('div');track.className='track';const bar=document.createElement('div');bar.className='bar '+(r.variant.startsWith('rust')?'rust':'');bar.style.width=(100*r[metric.value]/max)+'%';bar.title='Observed wall range: '+r.min_wall_ms.toFixed(3)+'–'+r.max_wall_ms.toFixed(3)+' ms';track.append(bar);const value=document.createElement('span');value.textContent=r[metric.value].toFixed(metric.value==='median_wall_ms'?3:0);row.append(label,track,value);box.append(row);}}sel.value=keys[keys.length-1];sel.onchange=draw;metric.onchange=draw;draw();</script></body></html>'''.replace("PAYLOAD", payload)
    (out / "report.html").write_text(page)
    for row in rows:
        print(f"{row['n']:>9} × {row['rounds']:>2} {row['variant']:<13} {row['median_wall_ms']:>10.3f} ms {row['median_peak_rss_kib']:>8.0f} KiB")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--kush", default=shutil.which("kush"))
    parser.add_argument("--toolchain", default="nightly")
    parser.add_argument("--repetitions", type=int, default=7)
    parser.add_argument("--warmups", type=int, default=2)
    parser.add_argument("--sizes", default="262144:8,2097152:4", help="comma-separated n:rounds")
    parser.add_argument("--cpu", type=int, default=max(os.sched_getaffinity(0)))
    parser.add_argument("--output", type=Path, default=ROOT / "results/latest")
    args = parser.parse_args()
    if not args.kush:
        parser.error("provide --kush /path/to/current/kush")
    args.kush = str(Path(args.kush).resolve())
    if args.cpu not in os.sched_getaffinity(0) or args.repetitions < 3 or args.warmups < 0:
        parser.error("invalid CPU/repetition/warmup configuration")
    try:
        sizes = [tuple(map(int, item.split(":"))) for item in args.sizes.split(",")]
    except ValueError:
        parser.error("sizes must be comma-separated integer n:rounds pairs")
    if any(len(case) != 2 or not 1 <= case[0] <= 8_000_000 or not 1 <= case[1] <= 32 for case in sizes):
        parser.error("sizes must be n:rounds, 1<=n<=8000000 and 1<=rounds<=32")
    args.output.mkdir(parents=True, exist_ok=True)
    builds = build(args.kush, args.toolchain)
    correctness()
    reference_correctness(args.kush)
    probes = safety(args.kush, args.toolchain)
    allocations = diagnostics(*sizes[-1])
    data = {"metadata": metadata(args, builds), "safety": probes, "allocations": allocations,
            "source_lines": source_lines(), "text_sections": text_hashes(), "measurements": []}
    rng = random.Random(20261103)
    for n, rounds in sizes:
        samples = {v[0]: [] for v in VARIANTS}
        for iteration in range(args.warmups + args.repetitions):
            order = list(VARIANTS)
            rng.shuffle(order)
            for variant, label, _, mode in order:
                observed = measure(executable(variant), n, rounds, mode, args.cpu)
                if iteration >= args.warmups:
                    samples[variant].append(observed)
        for variant, label, _, _ in VARIANTS:
            data["measurements"].append({"variant": variant, "label": label, "n": n, "rounds": rounds, "observations": samples[variant]})
    data["metadata"]["load_after"] = os.getloadavg()
    report(data, args.output)
    print(f"Reports: {args.output}")


if __name__ == "__main__":
    main()
