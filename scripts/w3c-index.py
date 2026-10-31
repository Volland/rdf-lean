#!/usr/bin/env python3
"""Write index.txt for a vendored W3C syntax suite from its manifest.

Each line is `positive FILE`, `negative FILE`, `eval FILE RESULT` or `c14n FILE RESULT`, in
manifest order, so the Lean test runners never parse Turtle. Entries are taken from the manifest's
`mf:entries` list, so commented-out entries are skipped; both the RDF 1.1 style (`<#name>`) and
the RDF 1.2 style (`:name`, `trs:name`) of naming entries are read. Usage:
  python3 scripts/w3c-index.py Tests/data/rdf-n-triples
  python3 scripts/w3c-index.py Tests/data/rdf-turtle
  python3 scripts/w3c-index.py Tests/data/rdf-n-quads
  python3 scripts/w3c-index.py Tests/data/rdf-trig
  python3 scripts/w3c-index.py Tests/data/rdf12-n-triples/syntax
  python3 scripts/w3c-index.py Tests/data/rdf12-n-triples/c14n
  python3 scripts/w3c-index.py Tests/data/rdf12-n-quads/syntax
  python3 scripts/w3c-index.py Tests/data/rdf12-n-quads/c14n
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
    "rdft:TestNQuadsPositiveSyntax": "positive",
    "rdft:TestNQuadsNegativeSyntax": "negative",
    "rdft:TestTrigPositiveSyntax": "positive",
    "rdft:TestTrigNegativeSyntax": "negative",
    "rdft:TestTrigEval": "eval",
    "rdft:TestTrigNegativeEval": "negative",
    "rdft:TestNTriplesPositiveC14N": "c14n",
    "rdft:TestNQuadsPositiveC14N": "c14n",
}
entries = re.findall(r"^<#([^>]+)>\s+(?:rdf:type|a)\s+(\S+)\s*;(.*?)\n\s*\.\s*$", manifest, re.S | re.M)
if not entries:
    entries = re.findall(r"^<#([^>]+)>\s+(?:rdf:type|a)\s+(\S+)\s*;(.*?)\.\s*$", manifest, re.S | re.M)
if not entries:
    # RDF 1.2 manifests: prefixed entry names, listed in `mf:entries ( ... )`.
    listed = re.search(r"mf:entries\s*\((.*?)\)", manifest, re.S).group(1)
    names = [tok for line in listed.splitlines()
             for tok in line.split("#", 1)[0].split()]
    for name in names:
        block = re.search(r"^" + re.escape(name) + r"\s+(?:rdf:type|a)\s+(\S+)\s*;(.*?)\s\.\s*$",
                          manifest, re.S | re.M)
        if not block:
            sys.exit(f"manifest entry {name} not found")
        entries.append((name, block.group(1), block.group(2)))
lines = []
for name, kind, body in entries:
    action = re.search(r"mf:action\s+<([^>]+)>", body)
    if kind not in kinds or not action:
        sys.exit(f"unexpected manifest entry {name}: {kind}")
    line = f"{kinds[kind]} {action.group(1)}"
    if kinds[kind] in ("eval", "c14n"):
        result = re.search(r"mf:result\s+<([^>]+)>", body)
        if not result:
            sys.exit(f"eval entry {name} has no result")
        line += f" {result.group(1)}"
    lines.append(line)

(suite / "index.txt").write_text("\n".join(lines) + "\n", encoding="utf-8")
print(f"{len(lines)} entries")
