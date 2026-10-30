#!/bin/sh
# Run the W3C SPARQL 1.1 query tests on LeanRDF and on oxilite and write sparql/diff-report.md.
# Usage: scripts/sparql-diff.sh /path/to/oxilite
set -eu
OXILITE=${1:?usage: scripts/sparql-diff.sh /path/to/oxilite}
export OXILITE
cd "$(dirname "$0")/../sparql"
lake build SparqlTests.W3C >/dev/null
lake env lean ../scripts/SparqlDiff.lean
