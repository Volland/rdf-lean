#!/bin/sh
# Record oxilite's outputs for the oxilite examples, to be replayed by scripts/examples.sh.
# Usage: scripts/examples-record.sh /path/to/oxilite
set -eu
OXILITE=${1:?usage: scripts/examples-record.sh /path/to/oxilite}
ROOT=$(cd "$(dirname "$0")/.." && pwd)
cd "$ROOT/elpi"
lake build leanrdf-oxilite >/dev/null
D="$ROOT/examples/owl-rl-family"
rm -rf "$D/recorded"
mkdir -p "$D/recorded"
"$OXILITE" --version 2>/dev/null > "$D/recorded/OXILITE_VERSION" || true
.lake/build/bin/leanrdf-oxilite "$D/data.ttl" "$D/pattern.ttl" --oxilite "$OXILITE" --profile owl \
  --record "$D/recorded" >/dev/null || true
.lake/build/bin/leanrdf-oxilite "$D/data.ttl" --materialized --oxilite "$OXILITE" \
  --record "$D/recorded" >/dev/null || true
echo "recorded $D/recorded"
