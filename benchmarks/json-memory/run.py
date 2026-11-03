#!/usr/bin/env python3
"""JSON editor memory comparison. Linux/glibc; no Python dependencies."""
import argparse
import datetime
import functools
import hashlib
import json
import os
import platform
from pathlib import Path
import random
import re
import resource
import shlex
import shutil
import statistics
import subprocess
import time

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parents[1]
BUILD = ROOT / "build"
WRAPS = ["malloc", "calloc", "realloc", "aligned_alloc", "posix_memalign", "free"]
VARIANTS = [("kush-rebuild", "Kush / rebuild", "kush", 0),
            ("kush-reuse", "Kush / reuse", "kush", 1),
            ("rust-rebuild", "Rust CLIF / rebuild", "rust", 0),
            ("rust-reuse", "Rust CLIF / deliberate reuse", "rust", 1)]

def run(command, **kwargs):
    result = subprocess.run([str(x) for x in command], capture_output=True, text=True, **kwargs)
    if result.returncode:
        raise RuntimeError(f"command failed ({result.returncode}): {command}\n{result.stdout}\n{result.stderr}")
    return result

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def limits(cpu=None):
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    if cpu is not None:
        os.sched_setaffinity(0, {cpu})

def build(kush, toolchain):
    BUILD.mkdir(parents=True, exist_ok=True)
    cc = shutil.which("cc")
    if not cc or not shutil.which("mbx"):
        raise RuntimeError("cc and mbx are required")
    metadata = []
    target = Path.home() / ".cache/kush-json-memory-rust"
    environment = dict(os.environ, RUSTUP_TOOLCHAIN=toolchain,
                       CARGO_PROFILE_RELEASE_DEBUG="0", CARGO_TARGET_DIR=str(target),
                       RUSTFLAGS="-Zcodegen-backend=cranelift -Ctarget-cpu=x86-64 -Coverflow-checks=yes")
    for kind, define in [("plain", None), ("trace", "TRACE_ALLOC"), ("rss", "PHASE_RSS")]:
        object_file = BUILD / f"probe-{kind}-{sha(ROOT/'probe.c')[:16]}.o"
        command = [cc, "-std=c11", "-O2", "-Wall", "-Wextra", "-Werror"]
        if define:
            command += [f"-D{define}=1"]
        command += ["-c", ROOT / "probe.c", "-o", object_file]
        run(command)
        shutil.copyfile(object_file, BUILD/f"probe-{kind}.o")
        wrapper_flags = [f"-Wl,--wrap={name}" for name in WRAPS] if kind == "trace" else []
        child_environment = dict(os.environ)
        if kind == "trace":
            directory = BUILD / "trace-compiler"
            directory.mkdir(exist_ok=True)
            wrapper = directory / "cc"
            wrapper.write_text("#!/bin/sh\nfor argument do\n case \"$argument\" in -c|-M|--version|-dumpmachine) exec " + shlex.quote(cc) + " \"$@\";; esac\ndone\nexec " + shlex.quote(cc) + " \"$@\" " + " ".join(wrapper_flags) + "\n")
            wrapper.chmod(0o700)
            child_environment["PATH"] = str(directory) + os.pathsep + os.environ["PATH"]
        output = BUILD / f"kush-{kind}"
        command = [kush, "build", ROOT / "kush/main.kush", "-o", output, "--release", "--link", object_file]
        if kind == "trace":
            command += ["--stats"]
        start = time.perf_counter()
        run(command, env=child_environment)
        metadata.append({"name": output.name, "command": list(map(str, command)), "wall_s": time.perf_counter()-start, "sha256": sha(output)})
        command = ["mbx", "rustc", "--manifest-path", ROOT / "rust/Cargo.toml", "--release", "--offline", "-j", "2", "--", "-C", f"link-arg={object_file}"]
        for flag in wrapper_flags:
            command += ["-C", f"link-arg={flag}"]
        start = time.perf_counter()
        run(command, env=environment)
        output = BUILD / f"rust-{kind}"
        shutil.copyfile(target / "release/json-memory", output)
        output.chmod(0o700)
        metadata.append({"name": output.name, "command": list(map(str, command)), "environment": {k:environment[k] for k in ["RUSTUP_TOOLCHAIN","CARGO_PROFILE_RELEASE_DEBUG","CARGO_TARGET_DIR","RUSTFLAGS"]}, "wall_s":time.perf_counter()-start, "sha256":sha(output)})
    command = [cc, "-std=c11", "-O0", ROOT/"probe_self_test.c", BUILD/"probe-trace.o", "-o", BUILD/"probe-self-test", *[f"-Wl,--wrap={name}" for name in WRAPS]]
    run(command)
    sources=[ROOT/"kush/main.kush",ROOT/"rust/src/main.rs",ROOT/"probe.c",ROOT/"probe_self_test.c",ROOT/"seed.json",ROOT/"rust/Cargo.toml",ROOT/"rust/Cargo.lock"]
    (BUILD/"manifest.json").write_text(json.dumps({"builds":metadata,"compiler_sha256":sha(kush),"sources":{str(path):sha(path) for path in sources}},indent=2))
    return metadata

def probe_correctness():
    result=run([BUILD/"probe-self-test"])
    frames=[json.loads(line.removeprefix("memory-alloc: ")) for line in result.stderr.splitlines() if line.startswith("memory-alloc: ")]
    assert [x["stage"] for x in frames]==[0,1,2,3,4,5,6],frames
    assert frames[1]["alloc_calls"]==2 and frames[1]["live_requested_bytes"]==80,frames
    assert frames[2]["realloc_calls"]==1 and frames[2]["live_requested_bytes"]==144,frames
    assert frames[3]["realloc_calls"]==1 and frames[3]["live_requested_bytes"]==144,frames
    assert frames[4]["alloc_calls"]==4 and frames[4]["live_requested_bytes"]==336,frames
    assert frames[-1]["requested_bytes_total"]==400 and frames[-1]["live_requested_bytes"]==0,frames
    assert frames[-1]["peak_live_requested_bytes"]==336,frames

def document(index, rounds):
    if rounds == 0:
        content, children = "seed", [1, 2, 3, 4]
    else:
        size = 512 if rounds % 2 else 16
        content = "".join(chr(65 + (index+rounds+i) % 26) for i in range(size))
        children = [index+rounds+i for i in range(32 if rounds % 2 else 4)]
    return {"id":index,"revision":rounds,"text":content,"children":children}

def encoded(value):
    return json.dumps(value, separators=(",", ":")).encode()

def checksum(value):
    result = 0
    for byte in value:
        result = (result*131+byte) % 1_000_000_007
    return result

@functools.lru_cache(None)
def expected(count, rounds):
    return sum(checksum(encoded(document(i, rounds))) for i in range(count)) + sum(checksum(encoded(document(i, 0))) for i in range(16))

def command(language, kind, count, rounds, mode, emit=0):
    return [BUILD/f"{language}-{kind}", count, rounds, mode, emit]

def correctness(kush):
    checks = []
    for name, _, language, mode in VARIANTS:
        for count, rounds in [(1, 0), (3, 1), (3, 2), (17, 5)]:
            result = run(command(language,"plain",count,rounds,mode,1), preexec_fn=limits)
            lines = result.stdout.splitlines()
            assert len(lines)==count+16+1, (name, lines)
            values = list(map(json.loads, lines[:-1]))
            assert values == [document(i,rounds) for i in range(count)]+[document(i,0) for i in range(16)], name
            assert int(lines[-1])==expected(count,rounds), name
            # Also require canonical byte-for-byte serialization, not just values.
            assert [line.encode() for line in lines[:-1]] == list(map(encoded, values)), name
            checks.append({"variant":name,"count":count,"rounds":rounds,"json_documents":count+16})
        for bad in [(0,1,mode,0),(32769,1,mode,0),(1,64,mode,0),(1,1,2,0)]:
            result = subprocess.run(list(map(str,[BUILD/f"{language}-plain",*bad])),capture_output=True)
            assert result.returncode==2,(name,bad,result)
    # Foreign probe hooks are no-ops in the reference validation only.
    source=(ROOT/"kush/main.kush").read_text()
    source=re.sub(r'^foreign\s+"memory_(?:begin|stage|end)"\s+fn[^;]*;\s*','',source,flags=re.M)
    source=re.sub(r'memory_(?:begin|end)\(\);|memory_stage\(\d+\);','',source)
    reference=BUILD/"reference.kush"
    reference.write_text(source)
    for mode in [0,1]:
        result=run([kush,"eval",reference,"--",2,2,mode,1],timeout=90,preexec_fn=limits)
        native=run(command("kush","plain",2,2,mode,1))
        assert result.stdout==native.stdout,mode
    return checks

def trace(kind,count,rounds):
    observations=[]
    for name,label,language,mode in VARIANTS:
        environment=dict(os.environ)
        if kind=="trace":environment["KUSH_ALLOCATOR_POOL_STATS"]="1"
        result=run(command(language,kind,count,rounds,mode),env=environment,preexec_fn=limits)
        assert int(result.stdout)==expected(count,rounds),name
        prefix="memory-alloc: " if kind=="trace" else "memory-rss: "
        frames=[json.loads(line[len(prefix):]) for line in result.stderr.splitlines() if line.startswith(prefix)]
        assert [x["stage"] for x in frames]==([0,1,2,3,4,5,6] if kind=="trace" else [0,1,2,3,4,5]),(name,result.stderr)
        if kind=="trace":
            # Startup objects can survive, but no new workload-owned bytes may
            # remain after the program's pool drain and normal shutdown.
            assert frames[-1]["workload_live_requested_bytes"]==0 and frames[-1]["workload_live_allocations"]==0,(name,frames)
        row={"variant":name,"label":label,"count":count,"rounds":rounds,"frames":frames,"stderr":result.stderr}
        for line in result.stderr.splitlines():
            if line.startswith("allocation-stats:") or line.startswith("allocator-pool:"):
                row[line.split(":",1)[0]]={key:int(value) for key,value in re.findall(r"([a-z-]+)=(\d+)",line)}
        observations.append(row)
    return observations

def measure(language,count,rounds,mode,cpu):
    marker="__memory_bench__"
    start=time.perf_counter()
    result=run(["/usr/bin/time","-f",marker+" %M",*command(language,"plain",count,rounds,mode)],preexec_fn=lambda:limits(cpu))
    elapsed=time.perf_counter()-start
    assert int(result.stdout)==expected(count,rounds),(language,count,rounds)
    peak=int(re.search(marker+r" (\d+)",result.stderr)[1])
    return {"wall_ms":elapsed*1000,"peak_rss_kib":peak}

def report(data,output):
    rows=[]
    for item in data["timings"]:
        trace_row=next(x for x in data["allocations"] if x["variant"]==item["variant"] and x["count"]==item["count"])
        frame=trace_row["frames"][-1]
        phase=next(x for x in data["phase_rss"] if x["variant"]==item["variant"] and x["count"]==item["count"])
        rows.append({"variant":item["variant"],"label":item["label"],"count":item["count"],"rounds":item["rounds"],
                     "median_wall_ms":statistics.median(x["wall_ms"] for x in item["samples"]),
                     "median_peak_rss_kib":statistics.median(x["peak_rss_kib"] for x in item["samples"]),
                     "allocator_calls":frame["alloc_calls"],"realloc_calls":frame["realloc_calls"],"allocator_requests":frame["alloc_calls"]+frame["realloc_calls"],
                     "requested_bytes_total":frame["requested_bytes_total"],"peak_live_requested_bytes":frame["peak_live_requested_bytes"],"peak_live_usable_bytes":frame["peak_live_usable_bytes"],"after_drop_rss_kib":phase["frames"][3]["rss_kib"]})
    data["summary"]=rows
    data["metadata"]["report_generator_sha256"]=sha(Path(__file__))
    output.mkdir(parents=True,exist_ok=True)
    (output/"results.json").write_text(json.dumps(data,indent=2)+"\n")
    lines=["# JSON document editor: memory and allocation benchmark","","Linux/glibc. Both compilers use Cranelift. Same seed and JSON output, rebuild/reuse controls. Instrumentation runs are separate from timing/RSS runs.","", "| Documents × edits | Implementation | Wall ms | Peak RSS KiB | Alloc calls | Realloc calls | Requested MiB total | Peak live requested MiB |", "|---|---|---:|---:|---:|---:|---:|---:|"]
    for r in rows:
        lines.append(f"| {r['count']} × {r['rounds']} | {r['label']} | {r['median_wall_ms']:.3f} | {r['median_peak_rss_kib']:.0f} | {r['allocator_calls']} | {r['realloc_calls']} | {r['requested_bytes_total']/1048576:.3f} | {r['peak_live_requested_bytes']/1048576:.3f} |")
    lines += ["", "Allocator calls are client-visible libc requests, not OS page allocations. Requested bytes include Kush's allocation headers/padding; usable bytes use glibc malloc_usable_size and exclude allocator metadata. Realloc transient internal peaks are not visible. Peak RSS comes from uninstrumented processes, not the fixed-table tracing binary.", "", "## Phase RSS (separate uninstrumented phase probe)","", "| Documents | Implementation | Before workload KiB | Loaded KiB | Edited KiB | Large corpus dropped KiB | Small corpus KiB | Workload dropped KiB |", "|---|---|---:|---:|---:|---:|---:|---:|"]
    for row in data["phase_rss"]:
        lines.append(f"| {row['count']} | {row['label']} | "+" | ".join(str(f['rss_kib']) for f in row['frames'])+" |")
    lines += ["", "Phase RSS values are single diagnostic snapshots, not medians. Memory can remain resident after logical frees because both the Kush pool and libc retain storage. Parser implementations differ (Kush std.json / Rust serde_json); parsing the small common seed is included. See README.md for representation differences, measurement scope and reproduction."]
    (output/"report.md").write_text("\n".join(lines)+"\n")
    # Self-contained theme-aware interactive comparison; no external resources.
    payload=json.dumps(rows)
    page='''<!doctype html><html><head><meta charset="utf-8"><style>
    :root{font-family:var(--font-sans);color:var(--foreground)}body{margin:0}h3{font-size:15px}p{color:var(--muted-foreground);font-size:13px;line-height:1.5}select{color:var(--foreground);background:var(--secondary);border:1px solid var(--border);padding:6px;border-radius:var(--radius)}.row{display:grid;grid-template-columns:minmax(140px,1fr) 1.3fr 90px;align-items:center;gap:10px;margin:15px 0;font-size:13px}.bar{height:25px;background:var(--secondary);border-radius:4px;overflow:hidden}.fill{height:100%;background:var(--chart-1)}.rust{background:var(--chart-2)}#chart{min-height:190px;margin-top:20px}.value{text-align:right;font-family:var(--font-mono)}label{font-size:13px;margin-right:12px;display:inline-block;margin-bottom:8px}
    </style></head><body><h3>Owned JSON documents · memory and allocation</h3><p>Matched edits and output. Lower is better. Rust uses Cranelift; this is one workload, not a general language ranking.</p><label>Documents <select id="size"></select></label><label>Metric <select id="metric"><option value="median_peak_rss_kib">Peak RSS (KiB)</option><option value="allocator_requests">Allocator requests (alloc + realloc)</option><option value="allocator_calls">Allocation calls only</option><option value="realloc_calls">Reallocation calls</option><option value="requested_bytes_total">Bytes requested cumulatively</option><option value="peak_live_requested_bytes">Peak live requested bytes</option><option value="median_wall_ms">Wall time (ms)</option><option value="after_drop_rss_kib">After-drop RSS (KiB, single probe)</option></select></label><div id="chart"></div><p>Allocation tracing and timing/RSS use separate binaries. Allocator requests are not OS allocations. Kush's headers/padding and pool retention count toward physical requested memory. Phase snapshots and raw data are in the linked report.</p><script>const rows=PAYLOAD;const sizes=[...new Set(rows.map(x=>x.count))];size.innerHTML=sizes.map(n=>`<option>${n}</option>`).join('');size.value=sizes[sizes.length-1];function draw(){const data=rows.filter(x=>x.count==size.value),key=metric.value,max=Math.max(...data.map(x=>x[key]),1);chart.innerHTML=data.map(x=>`<div class="row"><span>${x.label}</span><div class="bar"><div class="fill ${x.variant.startsWith('rust')?'rust':''}" style="width:${100*x[key]/max}%"></div></div><span class="value">${x[key].toLocaleString(undefined,{maximumFractionDigits:2})}</span></div>`).join('')}size.onchange=metric.onchange=draw;draw();</script></body></html>'''.replace("PAYLOAD",payload)
    (output/"report.html").write_text(page)
    print("\n".join(lines[:8+len(rows)]))

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--kush",default=shutil.which("kush"),required=not shutil.which("kush"))
    parser.add_argument("--toolchain",default="nightly")
    parser.add_argument("--sizes",type=int,nargs="+",default=[256,4096,16384])
    parser.add_argument("--rounds",type=int,default=31)
    parser.add_argument("--repetitions",type=int,default=7)
    parser.add_argument("--cpu",type=int,default=max(os.sched_getaffinity(0)))
    parser.add_argument("--output",type=Path,default=ROOT/"results/latest")
    parser.add_argument("--skip-build",action="store_true")
    parser.add_argument("--validate-only",action="store_true")
    args=parser.parse_args()
    if not args.sizes or any(n<1 or n>32768 for n in args.sizes) or not 0<=args.rounds<=63 or args.repetitions<3 or args.cpu not in os.sched_getaffinity(0):parser.error("invalid size, rounds, repetitions or CPU")
    kush=str(Path(args.kush).resolve())
    if args.skip_build:
        manifest=json.loads((BUILD/"manifest.json").read_text())
        assert manifest["compiler_sha256"]==sha(kush),"compiler changed; rebuild required"
        for path,digest in manifest["sources"].items():
            assert sha(path)==digest,f"source changed; rebuild required: {path}"
        builds=manifest["builds"]
        for item in builds:
            assert sha(BUILD/item["name"])==item["sha256"],f"binary changed: {item['name']}"
    else:
        builds=build(kush,args.toolchain)
    probe_correctness()
    checks=correctness(kush)
    print(f"Correctness: {len(checks)} JSON output cases; reference/native agreement and invalid arguments passed.",flush=True)
    if args.validate_only:return
    data={"metadata":{"utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),"git_head":run(["git","rev-parse","HEAD"],cwd=REPO).stdout.strip(),"compiler_sha256":sha(kush),"libc":platform.libc_ver(),"kernel":platform.release(),"cc":run(["cc","--version"]).stdout,"allocator_environment":{key:os.environ.get(key) for key in ["MALLOC_ARENA_MAX","MALLOC_TRIM_THRESHOLD_","MALLOC_MMAP_THRESHOLD_","GLIBC_TUNABLES","LD_PRELOAD"]},"rustc":run(["rustc",f"+{args.toolchain}","-vV"]).stdout,"cpu_model":next(line.split(":",1)[1].strip() for line in Path('/proc/cpuinfo').read_text().splitlines() if line.startswith('model name')),"pinned_cpu":args.cpu,"repetitions":args.repetitions,"warmups":2,"shuffle_seed":20261103,"builds":builds,"sources":{str(p.relative_to(ROOT)):sha(p) for p in [ROOT/"kush/main.kush",ROOT/"rust/src/main.rs",ROOT/"probe.c",ROOT/"probe_self_test.c",ROOT/"seed.json",ROOT/"rust/Cargo.lock",ROOT/"rust/Cargo.toml",ROOT/"Kush.toml",ROOT/"run.py"]}},"correctness":checks,"allocations":[],"phase_rss":[],"timings":[]}
    rng=random.Random(20261103)
    for count in args.sizes:
        data["allocations"]+=trace("trace",count,args.rounds)
        data["phase_rss"]+=trace("rss",count,args.rounds)
        observations={name:[] for name,_,_,_ in VARIANTS}
        for at in range(args.repetitions+2):
            order=list(VARIANTS);rng.shuffle(order)
            for name,label,language,mode in order:
                observation=measure(language,count,args.rounds,mode,args.cpu)
                if at>=2:observations[name].append(observation)
        for name,label,_,_ in VARIANTS:data["timings"].append({"variant":name,"label":label,"count":count,"rounds":args.rounds,"samples":observations[name]})
        print(f"Measured {count} documents × {args.rounds} edits",flush=True)
    report(data,args.output)

if __name__=="__main__":main()
