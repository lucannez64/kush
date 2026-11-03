#!/usr/bin/env python3
"""Update plan/plan.json from the command line (used by people and agents).

  scripts/plan.py list                      status of every node
  scripts/plan.py start ID [message]        mark in progress
  scripts/plan.py done ID [--commit SHA] [message]
  scripts/plan.py todo ID                   back to not started
  scripts/plan.py log ID message [--who NAME]
  scripts/plan.py add ID "title" --size M [--deps A,B] [--desc TEXT] [--hard]
  scripts/plan.py deps ID A,B               replace dependencies
"""
import argparse
import datetime
import json
import sys
from pathlib import Path

PLAN = Path(__file__).resolve().parent.parent / "plan" / "plan.json"


def load():
    return json.loads(PLAN.read_text())


def save(plan):
    ids = {node["id"] for node in plan["nodes"]}
    for node in plan["nodes"]:
        missing = [d for d in node["deps"] if d not in ids]
        if missing:
            sys.exit(f"{node['id']}: unknown dependencies {missing}")
    seen, stack = set(), set()
    graph = {node["id"]: node["deps"] for node in plan["nodes"]}

    def visit(node):
        if node in stack:
            sys.exit(f"dependency cycle through {node}")
        if node in seen:
            return
        stack.add(node)
        for dep in graph[node]:
            visit(dep)
        stack.discard(node)
        seen.add(node)

    for node in graph:
        visit(node)
    tmp = PLAN.with_suffix(".tmp")
    tmp.write_text(json.dumps(plan, indent=2) + "\n")
    tmp.replace(PLAN)


def find(plan, node_id):
    for node in plan["nodes"]:
        if node["id"] == node_id:
            return node
    sys.exit(f"no node {node_id}")


def note(node, text, who):
    if text:
        node.setdefault("log", []).append(
            {"time": datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S"), "who": who, "text": text}
        )


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("command")
    parser.add_argument("id", nargs="?")
    parser.add_argument("rest", nargs="*")
    parser.add_argument("--commit")
    parser.add_argument("--who", default="agent")
    parser.add_argument("--size", default="M")
    parser.add_argument("--deps", default="")
    parser.add_argument("--desc", default="")
    parser.add_argument("--hard", action="store_true")
    args = parser.parse_args()
    plan = load()
    text = " ".join(args.rest)
    if args.command == "list":
        nodes = {n["id"]: n for n in plan["nodes"]}
        for n in plan["nodes"]:
            state = n["status"]
            if state == "todo":
                state = "ready" if all(nodes[d]["status"] == "done" for d in n["deps"]) else "waiting"
            print(f"{state:12} {n['id']:16} {n['title']}")
        return
    if args.command == "add":
        if any(n["id"] == args.id for n in plan["nodes"]):
            sys.exit(f"{args.id} already exists")
        plan["nodes"].append(dict(
            id=args.id, title=text, size=args.size, hard=args.hard,
            deps=[d for d in args.deps.split(",") if d], status="todo",
            desc=args.desc, commit=None, log=[],
        ))
    else:
        node = find(plan, args.id)
        if args.command == "start":
            node["status"] = "in_progress"
            note(node, text or "started", args.who)
        elif args.command == "done":
            node["status"] = "done"
            if args.commit:
                node["commit"] = args.commit
            note(node, text or f"done {args.commit or ''}".strip(), args.who)
        elif args.command == "todo":
            node["status"] = "todo"
            note(node, text or "reset", args.who)
        elif args.command == "log":
            note(node, text, args.who)
        elif args.command == "deps":
            node["deps"] = [d for d in (args.rest[0] if args.rest else "").split(",") if d]
        else:
            sys.exit(f"unknown command {args.command}")
    save(plan)


if __name__ == "__main__":
    main()
