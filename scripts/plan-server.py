#!/usr/bin/env python3
"""Local plan viewer: serves plan/index.html and live plan + repository state.

Usage: scripts/plan-server.py [--port 4318]
Open http://127.0.0.1:4318/. Edit plan/plan.json directly or with scripts/plan.py.
"""
import argparse
import json
import os
import subprocess
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PLAN = ROOT / "plan" / "plan.json"
PAGE = ROOT / "plan" / "index.html"


def git(*args):
    try:
        return subprocess.run(
            ["git", "-C", str(ROOT), *args], capture_output=True, text=True, timeout=5
        ).stdout.strip()
    except (OSError, subprocess.SubprocessError):
        return ""


def pushed_commits():
    """Commits reachable from origin/main, used for 'completed, not pushed'."""
    return set(git("rev-list", "origin/main", "--max-count=5000").split())


def state():
    plan = json.loads(PLAN.read_text())
    nodes = {node["id"]: node for node in plan["nodes"]}
    pushed = pushed_commits()
    counts = {"completed": 0, "in progress": 0, "ready": 0, "waiting": 0, "not pushed": 0}
    for node in plan["nodes"]:
        if node["status"] == "done":
            kind = "completed"
            commit = node.get("commit")
            if commit:
                full = git("rev-parse", "--verify", "--quiet", commit + "^{commit}")
                if full and full not in pushed:
                    kind = "not pushed"
        elif node["status"] == "in_progress":
            kind = "in progress"
        elif all(nodes.get(d, {}).get("status") == "done" for d in node["deps"]):
            kind = "ready"
        else:
            kind = "waiting"
        node["kind"] = kind
        counts[kind] += 1
    log = [
        dict(entry, node=node["id"])
        for node in plan["nodes"]
        for entry in node.get("log", [])
    ]
    log.sort(key=lambda entry: entry.get("time", ""), reverse=True)
    head = git("rev-parse", "--short", "HEAD")
    origin = git("rev-parse", "--short", "origin/main")
    return {
        "title": plan.get("title", "Plan"),
        "nodes": plan["nodes"],
        "counts": counts,
        "total": len(plan["nodes"]),
        "retries": sum(node.get("retries", 0) for node in plan["nodes"]),
        "log": log[:200],
        "repo": {
            "head": head,
            "origin": origin,
            "ahead": git("rev-list", "--count", "origin/main..HEAD") or "?",
            "branch": git("rev-parse", "--abbrev-ref", "HEAD"),
            "dirty": bool(git("status", "--porcelain")),
            "worktrees": max(0, len(git("worktree", "list").splitlines()) - 1),
        },
        "load": [round(x, 2) for x in os.getloadavg()],
    }


class Handler(BaseHTTPRequestHandler):
    def do_GET(self):
        if self.path.startswith("/api/state"):
            body = json.dumps(state()).encode()
            kind = "application/json"
        elif self.path in ("/", "/index.html"):
            body = PAGE.read_bytes()
            kind = "text/html; charset=utf-8"
        else:
            self.send_error(404)
            return
        self.send_response(200)
        self.send_header("Content-Type", kind)
        self.send_header("Cache-Control", "no-store")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def log_message(self, format, *args):  # noqa: A002 - base signature
        del format, args


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--port", type=int, default=4318)
    args = parser.parse_args()
    server = ThreadingHTTPServer(("127.0.0.1", args.port), Handler)
    print(f"Plan viewer on http://127.0.0.1:{args.port}/")
    server.serve_forever()


if __name__ == "__main__":
    main()
