#!/bin/sh
# Property paths with a constant endpoint: run the queries of `gen.py paths` with one
# leanrdf-sparql binary, printing wall time, peak RSS and a digest of the output of each.
#
# Usage: scripts/bench/paths.sh BIN DIR CASES [TIMEOUT]
#   BIN      a leanrdf-sparql executable
#   DIR      the output directory of `scripts/bench/gen.py paths N DIR`
#   CASES    space-separated GRAPH:QUERY pairs, e.g. "chain:s-plus chain:o-plus tangle:v-plus"
#   TIMEOUT  seconds per run (default 120)
#
# Outputs are kept as DIR/out/<label>-GRAPH-QUERY.json, where <label> is $LABEL (default "run"),
# so the outputs of two binaries can be compared byte for byte with cmp.
set -u
BIN=$1; DIR=$2; CASES=$3; LIMIT=${4:-120}; LABEL=${LABEL:-run}
mkdir -p "$DIR/out"
printf '%-22s %9s %10s %s\n' case wall_s peak_MB result
for c in $CASES; do
  g=${c%%:*}; q=${c#*:}
  out="$DIR/out/$LABEL-$g-$q.json"; err="$DIR/out/$LABEL-$g-$q.time"
  # perl's alarm is the time limit (macOS has no timeout(1)); /usr/bin/time -l reports peak RSS
  /usr/bin/time -l perl -e 'alarm shift; exec @ARGV' "$LIMIT" \
    "$BIN" query --location "$DIR/$g.nt" --query "$(cat "$DIR/$q.rq")" >"$out" 2>"$err"
  code=$?
  wall=$(awk '/ real /{print $1}' "$err")
  rss=$(awk '/maximum resident set size/{printf "%.0f", $1/1048576}' "$err")
  if [ $code -eq 0 ]; then res=$(shasum "$out" | cut -c1-12); else res="exit $code (timeout or error)"; fi
  printf '%-22s %9s %10s %s\n' "$g:$q" "$wall" "$rss" "$res"
done
