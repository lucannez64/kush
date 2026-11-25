#!/usr/bin/env python3
"""MIR explorer: write a Kush program, see its control-flow-graph IR.

Usage: scripts/mir-server.py [--port 4319] [--host 127.0.0.1] [--tailscale] [--kush PATH]
Open http://127.0.0.1:4319/. With --tailscale it also listens on this
machine's Tailscale address, for the other devices of the tailnet.
The page (scripts/mir-explorer.html) sends the
program to /api/mir, which runs `kush mir` three ways: as built, after a
release build's loop passes (`--release`), and after an LLVM release build's
(`--release --backend llvm`); see docs/mir-design.md section 8. It only
compiles: nothing the program says is run.

The kush binary defaults to target/release/kush, else target/debug/kush.
"""
import argparse
import json
import re
import subprocess
import tempfile
import threading
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PAGE = Path(__file__).resolve().parent / "mir-explorer.html"
STAGES = {
    "built": [],
    "release": ["--release"],
    "llvm": ["--release", "--backend", "llvm"],
}
LIMIT = 200_000
ANSI = re.compile(r"\x1b\[[0-9;]*m")

EXAMPLE = """enum Shape { Circle(i64), Rect(i64, i64) }

fn area(s: Shape) -> i64 {
    match s {
        Circle(r) => 3 * r * r,
        Rect(w, h) => w * h,
    }
}

fn total(xs: &[i64]) -> i64 {
    let mut i = 0;
    let mut sum = 0;
    while i < xs.len() {
        sum = sum + xs[i];
        i = i + 1;
    }
    sum
}

fn halves(xs: &[i64]) -> i64 {
    let mut i = 0;
    let mut sum = 0;
    while i < xs.len() {
        sum = sum + xs[i] / 2;
        i = i + 1;
    }
    sum
}

fn squares(n: i64) -> Vec<i64> ! {alloc} {
    let mut v: Vec<i64> = Vec.with_capacity(0);
    let mut i = 0;
    while i < n {
        v = Vec.push(v, i * i);
        i = i + 1;
    }
    v
}

fn main() -> Unit ! {io, alloc} {
    let mut areas = squares(3);
    areas = Vec.push(areas, area(Circle(2)));
    areas = Vec.push(areas, area(Rect(3, 4)));
    print_i64(total(&areas[..]) + halves(&areas[..]));
}
"""


def pretty(text):
    """Readable names for the rvalues whose operation is JSON in the text form."""

    def replace(match):
        kind = match.group(1)
        value = json.loads(json.loads('"' + match.group(2) + '"'))
        if kind == "deferred":
            return f"deferred.{value['mode'].lower()} {value['op'] or 'Neg'}("
        name = value if isinstance(value, str) else next(iter(value))
        snake = re.sub(r"(?<!^)([A-Z])", r"_\1", name).lower()
        return f"{kind}.{snake}("

    return re.sub(
        r'\b(loop|deferred|alloc|array|runtime|task|map) "((?:[^"\\]|\\.)*)"\(', replace, text
    )


def parse(text):
    """The functions of a `kush mir` dump, with each block's edges."""
    functions = []
    for chunk in re.split(r"^// function \d+\n", text, flags=re.M)[1:]:
        lines = chunk.rstrip("\n").split("\n")
        header = lines[0]
        if header.startswith("// fn "):
            functions.append(dict(name=header[6:].split(":")[0], uncovered=header[6:], blocks=[]))
            continue
        name = re.match(r'fn "([^"]+)"', header).group(1)
        builtins, locals_, blocks, current = {}, [], [], None
        for line in lines[1:]:
            s = line.strip()
            m = re.match(r'builtin (\d+) = "(.*)";$', s)
            if m:
                (group, value), = json.loads(json.loads('"' + m.group(2) + '"')).items()
                op = value[0] if isinstance(value, list) else value
                builtins[m.group(1)] = f"{group}.{op if isinstance(op, str) else next(iter(op))}"
                continue
            if s.startswith(("let ", "temp ")):
                locals_.append(s.rstrip(";"))
                continue
            m = re.match(r"bb(\d+)(?: \(unwind bb(\d+)\))?: \{$", s)
            if m:
                current = dict(
                    id=int(m.group(1)),
                    unwind=int(m.group(2)) if m.group(2) else None,
                    lines=[],
                )
                blocks.append(current)
                continue
            if s and s != "}" and current is not None:
                current["lines"].append(s)
        out = []
        for block in blocks:
            parsed = []
            for s in block["lines"]:
                m = re.match(r"(.*) @(\d+)\.\.(\d+);$", s)
                raw, span = (m.group(1), [int(m.group(2)), int(m.group(3))]) if m else (s.rstrip(";"), None)
                raw = re.sub(r"builtin (\d+)", lambda x: builtins.get(x.group(1), x.group(0)), raw)
                parsed.append(dict(text=pretty(raw), raw=raw, span=span))
            *statements, terminator = parsed
            t = terminator["raw"]
            edges = []
            if t.startswith("switch"):
                cases = re.search(r"\[(.*)\] otherwise bb(\d+)", t)
                for case in filter(None, cases.group(1).split(", ")):
                    value, target = re.match(r"(-?\d+) -> bb(\d+)", case).groups()
                    edges.append(dict(to=int(target), label=value, kind="normal"))
                edges.append(dict(to=int(cases.group(2)), label="else", kind="normal"))
            else:
                for target in re.findall(r"(?:goto|->) bb(\d+)", t):
                    edges.append(dict(to=int(target), label="", kind="normal"))
                for target in re.findall(r"unwind bb(\d+)", t):
                    edges.append(dict(to=int(target), label="unwind", kind="unwind"))
            kind = t.split()[0]
            if " = call " in t:
                kind = "call"
            out.append(dict(
                id=block["id"], unwind=block["unwind"], statements=statements,
                terminator=terminator, edges=edges, kind=kind,
            ))
        functions.append(dict(name=name, signature=header.rstrip(" {"), locals=locals_, blocks=out))
    names = {str(i): f["name"] for i, f in enumerate(functions)}
    for function in functions:
        for block in function["blocks"]:
            for s in block["statements"] + [block["terminator"]]:
                for key in ("text", "raw"):
                    s[key] = re.sub(r"call fn (\d+)", lambda x: "call " + names[x.group(1)], s[key])
    return functions


def passes(function):
    """The loop passes that left their mark on an optimized function."""
    text = "\n".join(
        s["raw"] for b in function["blocks"] for s in b["statements"] + [b["terminator"]]
    )
    found = []
    if 'deferred "' in text:
        found.append("deferred overflow")
    if re.search(r"= Eq\(copy _\d+\.2:i64", text):
        found.append("slice layout")
    if " shadow " in text:
        found.append("push shadow")
    if " below(" in text:
        found.append("upper bounds")
    return found


def explore(source, kush):
    with tempfile.TemporaryDirectory(prefix="kush-mir-") as directory:
        path = Path(directory) / "main.kush"
        path.write_text(source)
        stages = {}
        for stage, flags in STAGES.items():
            try:
                run = subprocess.run(
                    [str(kush), "mir", str(path), *flags],
                    capture_output=True, text=True, timeout=30, cwd=directory,
                )
            except subprocess.TimeoutExpired:
                return dict(error="kush mir took longer than 30 seconds")
            if run.returncode != 0:
                message = ANSI.sub("", run.stderr or run.stdout).replace(str(path), "main.kush")
                return dict(error=message.strip())
            stages[stage] = parse(run.stdout)
    # Source order: the first span each function covers.
    def start(function):
        spans = [s["span"][0] for b in function["blocks"]
                 for s in b["statements"] + [b["terminator"]]
                 if s["span"] and s["span"][1] > s["span"][0]]
        return min(spans, default=1 << 60)
    order = {f["name"]: start(f) for f in stages["built"]}
    built = {f["name"]: f for f in stages["built"]}
    for stage, functions in stages.items():
        functions.sort(key=lambda f: order.get(f["name"], 1 << 60))
        for function in functions:
            original = len(built.get(function["name"], function)["blocks"])
            function["original"] = original
            function["added"] = len(function["blocks"]) - original
            function["passes"] = passes(function) if stage != "built" else []
    return dict(source=source, stages=stages)


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--port", type=int, default=4319)
    parser.add_argument("--host", default="127.0.0.1")
    parser.add_argument(
        "--tailscale", action="store_true",
        help="also listen on this machine's Tailscale IPv4 address",
    )
    parser.add_argument("--kush", type=Path)
    args = parser.parse_args()
    kush = args.kush or next(
        (p for p in (ROOT / "target/release/kush", ROOT / "target/debug/kush") if p.exists()), None
    )
    if kush is None or not kush.exists():
        parser.error("no kush binary: build one (mbx build --release -p kush) or pass --kush PATH")

    class Handler(BaseHTTPRequestHandler):
        def send(self, status, body, kind):
            data = body if isinstance(body, bytes) else body.encode()
            self.send_response(status)
            self.send_header("Content-Type", kind)
            self.send_header("Content-Length", str(len(data)))
            self.send_header("Cache-Control", "no-store")
            self.end_headers()
            self.wfile.write(data)

        def do_GET(self):
            if self.path in ("/", "/index.html"):
                self.send(200, PAGE.read_bytes(), "text/html; charset=utf-8")
            elif self.path == "/api/example":
                self.send(200, json.dumps(dict(source=EXAMPLE)), "application/json")
            else:
                self.send(404, "not found", "text/plain")

        def do_POST(self):
            if self.path != "/api/mir":
                self.send(404, "not found", "text/plain")
                return
            length = int(self.headers.get("Content-Length", 0))
            if length > LIMIT:
                self.send(413, json.dumps(dict(error="the program is too large")), "application/json")
                return
            try:
                source = json.loads(self.rfile.read(length))["source"]
                result = explore(source, kush)
            except (ValueError, KeyError) as error:
                result = dict(error=f"bad request: {error}")
            self.send(200, json.dumps(result), "application/json")

        def log_message(self, format, *args):
            pass

    hosts = [args.host]
    if args.tailscale:
        try:
            address = subprocess.run(
                ["tailscale", "ip", "-4"], capture_output=True, text=True, timeout=5, check=True
            ).stdout.split()[0]
        except (OSError, subprocess.SubprocessError, IndexError):
            parser.error("--tailscale: `tailscale ip -4` gave no address; is Tailscale up?")
        if address not in hosts:
            hosts.append(address)
    servers = [ThreadingHTTPServer((host, args.port), Handler) for host in hosts]
    for host in hosts:
        print(f"MIR explorer on http://{host}:{args.port}/")
    print(f"kush: {kush}")
    for server in servers[1:]:
        threading.Thread(target=server.serve_forever, daemon=True).start()
    try:
        servers[0].serve_forever()
    except KeyboardInterrupt:
        pass


if __name__ == "__main__":
    main()
