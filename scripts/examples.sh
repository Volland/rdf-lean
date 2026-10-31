#!/bin/sh
# Run the examples under examples/ and compare each output with its recorded copy.
# Usage: scripts/examples.sh [--update] [all|sparql|shacl|elpi]
# Every example writes examples/<dir>/expected/<name>.txt: the command's output, then a line
# "# exit N" with its exit code. --update rewrites those files instead of comparing. The oxilite
# examples replay outputs recorded with scripts/examples-record.sh, so oxilite is not needed.
set -eu
ROOT=$(cd "$(dirname "$0")/.." && pwd)
UPDATE=0
if [ "${1:-}" = "--update" ]; then UPDATE=1; shift; fi
WHICH=${1:-all}
FAIL=0

build() { # package executable
  (cd "$ROOT/$1" && lake build "$2" >/dev/null)
}

# check DIR NAME BIN ARGS...: run BIN ARGS in examples/DIR and compare with expected/NAME.txt
check() {
  dir=$1 name=$2 bin=$3
  shift 3
  exp="$ROOT/examples/$dir/expected/$name.txt"
  out=$(cd "$ROOT/examples/$dir" && { "$bin" "$@" 2>&1; echo "# exit $?"; } || true)
  if [ $UPDATE = 1 ]; then
    mkdir -p "$(dirname "$exp")"
    printf '%s\n' "$out" > "$exp"
    echo "recorded $dir/$name"
  elif [ -f "$exp" ] && [ "$out" = "$(cat "$exp")" ]; then
    echo "ok       $dir/$name"
  else
    echo "FAIL     $dir/$name"
    printf '%s\n' "$out" | diff "$exp" - || true
    FAIL=1
  fi
}

if [ "$WHICH" = all ] || [ "$WHICH" = sparql ]; then
  build sparql leanrdf-sparql
  SPARQL="$ROOT/sparql/.lake/build/bin/leanrdf-sparql"
  for q in "$ROOT"/examples/sparql-library/*.rq; do
    n=$(basename "$q" .rq)
    check sparql-library "$n" "$SPARQL" query --location library.ttl --query "$(cat "$q")" \
      --results-format tsv
  done
fi

if [ "$WHICH" = all ] || [ "$WHICH" = shacl ]; then
  build shacl leanrdf-shacl
  SHACL="$ROOT/shacl/.lake/build/bin/leanrdf-shacl"
  check shacl-employees valid "$SHACL" validate --data valid.ttl --shapes shapes.ttl
  check shacl-employees invalid "$SHACL" validate --data invalid.ttl --shapes shapes.ttl
fi

if [ "$WHICH" = all ] || [ "$WHICH" = elpi ]; then
  build elpi leanrdf-demo
  build elpi leanrdf-oxilite
  build elpi leanrdf-classify
  BIN="$ROOT/elpi/.lake/build/bin"
  for q in "$ROOT"/examples/rdfs-university/query-*.nt; do
    n=$(basename "$q" .nt)
    check rdfs-university "$n" "$BIN/leanrdf-demo" university.nt "$(basename "$q")"
  done
  for q in "$ROOT"/examples/rdf12-reification/query-*.nt; do
    n=$(basename "$q" .nt)
    check rdf12-reification "$n" "$BIN/leanrdf-demo" claims.nt "$(basename "$q")"
  done
  check owl-rl-family answers "$BIN/leanrdf-oxilite" data.ttl pattern.ttl --profile owl \
    --results recorded/results.json --why-dir recorded
  check owl-rl-family materialized "$BIN/leanrdf-oxilite" data.ttl --materialized \
    --inferred recorded/inferred.tsv
  check owl-el-anatomy classify "$BIN/leanrdf-classify" anatomy.ttl
fi

[ $UPDATE = 1 ] || { [ $FAIL = 0 ] && echo "examples: all match" || echo "examples: some differ"; }
exit $FAIL
