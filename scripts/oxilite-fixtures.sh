#!/bin/sh
# Record oxilite's answers and why trees for the oxilite-bridge fixtures.
# Usage: scripts/oxilite-fixtures.sh /path/to/oxilite
# Each directory under elpi/BridgeTests/data/oxilite holds data.ttl and pattern.ttl; the run
# writes results.json and why-N.json next to them. Directories named owl-* run under the OWL
# profile and also record oxilite's materialized OWL 2 RL closure (inferred.tsv). lake test then
# replays them without oxilite.
set -eu
OXILITE=${1:?usage: scripts/oxilite-fixtures.sh /path/to/oxilite}
cd "$(dirname "$0")/../elpi"
lake build leanrdf-oxilite >/dev/null
"$OXILITE" --version 2>/dev/null > BridgeTests/data/oxilite/OXILITE_VERSION || true
for d in BridgeTests/data/oxilite/*/; do
  rm -f "$d"results.json "$d"why-*.json "$d"inferred.tsv
  case "$(basename "$d")" in owl-*) profile=owl ;; *) profile=rdfs ;; esac
  .lake/build/bin/leanrdf-oxilite "$d"data.ttl "$d"pattern.ttl --oxilite "$OXILITE" --profile $profile \
    --record "$d" > "$d"report.txt || echo "$d: exit $?"
  if [ $profile = owl ]; then
    .lake/build/bin/leanrdf-oxilite "$d"data.ttl --materialized --oxilite "$OXILITE" --record "$d" \
      > "$d"materialized.txt || echo "$d materialized: exit $?"
  fi
  echo "recorded $d"
done
