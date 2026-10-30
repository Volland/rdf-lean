#!/bin/sh
# Record oxilite's SHACL results for the leanrdf-shacl comparison fixtures.
# Usage: scripts/shacl-oxilite-fixtures.sh /path/to/oxilite
# Each directory under shacl/ShaclTests/data/oxilite holds data.ttl and shapes.ttl; the run
# validates them with `oxilite check --json` (reasoning off) in a scratch project and writes
# oxilite.json next to them. lake test then compares them with LeanRDF's reports.
set -eu
OXILITE=${1:?usage: scripts/shacl-oxilite-fixtures.sh /path/to/oxilite}
cd "$(dirname "$0")/../shacl/ShaclTests/data/oxilite"
"$OXILITE" --version 2>/dev/null > OXILITE_VERSION || true
for d in */; do
  scratch=$(mktemp -d)
  cp "$d"data.ttl "$d"shapes.ttl "$scratch"/
  printf 'reasoning = "none"\n\n[[graph]]\niri = "urn:data"\nfiles = ["data.ttl"]\n\n[[graph]]\niri = "urn:shapes"\nrole = "shapes"\nfiles = ["shapes.ttl"]\n' \
    > "$scratch"/oxilite.toml
  (cd "$scratch" && "$OXILITE" check --json .) | sed 's|"root": "[^"]*"|"root": "."|' > "$d"oxilite.json || true
  rm -r "$scratch"
  echo "recorded $d"
done
