#!/usr/bin/env python3
"""Write index.txt for a vendored W3C syntax suite from its manifest.

Each line is `positive FILE`, `negative FILE` or `eval FILE RESULT`, in manifest order, so the
Lean test runners never parse Turtle. Usage:
  python3 scripts/w3c-index.py Tests/data/rdf-n-triples
  python3 scripts/w3c-index.py Tests/data/rdf-turtle
"""
import re
import sys
from pathlib import Path

suite = Path(sys.argv[1] if len(sys.argv) > 1 else "Tests/data/rdf-n-triples")
manifest = (suite / "manifest.ttl").read_text(encoding="utf-8")

kinds = {
    "rdft:TestNTriplesPositiveSyntax": "positive",
    "rdft:TestNTriplesNegativeSyntax": "negative",
    "rdft:TestTurtlePositiveSyntax": "positive",
    "rdft:TestTurtleNegativeSyntax": "negative",
    "rdft:TestTurtleEval": "eval",
    "rdft:TestTurtleNegativeEval": "negative",
}
entries = re.findall(r"^<#([^>]+)>\s+rdf:type\s+(\S+)\s*;(.*?)\n\s*\.\s*$", manifest, re.S | re.M)
if not entries:
    entries = re.findall(r"^<#([^>]+)>\s+rdf:type\s+(\S+)\s*;(.*?)\.\s*$", manifest, re.S | re.M)
lines = []
for name, kind, body in entries:
    action = re.search(r"mf:action\s+<([^>]+)>", body)
    if kind not in kinds or not action:
        sys.exit(f"unexpected manifest entry {name}: {kind}")
    line = f"{kinds[kind]} {action.group(1)}"
    if kinds[kind] == "eval":
        result = re.search(r"mf:result\s+<([^>]+)>", body)
        if not result:
            sys.exit(f"eval entry {name} has no result")
        line += f" {result.group(1)}"
    lines.append(line)

(suite / "index.txt").write_text("\n".join(lines) + "\n", encoding="utf-8")
print(f"{len(lines)} entries")
