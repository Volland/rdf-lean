#!/bin/sh
# Record oxilite's answers and why trees for the oxilite-bridge fixtures.
# Usage: scripts/oxilite-fixtures.sh /path/to/oxilite
# Each directory under elpi/BridgeTests/data/oxilite holds data.ttl and pattern.ttl; the run
# writes results.json and why-N.json next to them. lake test then replays them without oxilite.
set -eu
OXILITE=${1:?usage: scripts/oxilite-fixtures.sh /path/to/oxilite}
cd "$(dirname "$0")/../elpi"
lake build leanrdf-oxilite >/dev/null
"$OXILITE" --version 2>/dev/null > BridgeTests/data/oxilite/OXILITE_VERSION || true
for d in BridgeTests/data/oxilite/*/; do
  rm -f "$d"results.json "$d"why-*.json
  .lake/build/bin/leanrdf-oxilite "$d"data.ttl "$d"pattern.ttl --oxilite "$OXILITE" --record "$d" \
    > "$d"report.txt || echo "$d: exit $?"
  echo "recorded $d"
done
