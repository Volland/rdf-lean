#!/usr/bin/env python3
"""Write Tests/data/rdf-n-triples/index.txt from the W3C manifest.

Each line is `positive <file>` or `negative <file>`, in manifest order, so the Lean test runner
never has to parse Turtle. Usage: python3 scripts/w3c-ntriples-index.py [suite-dir]
"""
import re
import sys
from pathlib import Path

suite = Path(sys.argv[1] if len(sys.argv) > 1 else "Tests/data/rdf-n-triples")
manifest = (suite / "manifest.ttl").read_text(encoding="utf-8")

kinds = {
    "rdft:TestNTriplesPositiveSyntax": "positive",
    "rdft:TestNTriplesNegativeSyntax": "negative",
}
entries = re.findall(r"^<#([^>]+)>\s+rdf:type\s+(\S+)\s*;(.*?)\.\s*$", manifest, re.S | re.M)
lines = []
for name, kind, body in entries:
    action = re.search(r"mf:action\s+<([^>]+)>", body)
    if kind not in kinds or not action:
        sys.exit(f"unexpected manifest entry {name}: {kind}")
    lines.append(f"{kinds[kind]} {action.group(1)}")

(suite / "index.txt").write_text("\n".join(lines) + "\n", encoding="utf-8")
print(f"{len(lines)} entries")
