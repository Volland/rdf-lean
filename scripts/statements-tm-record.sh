#!/bin/sh
# Record tiramemsu's statement-graph exports for LeanRDF's tests.
# Usage: scripts/statements-tm-record.sh TIRAMEMSU_CHECKOUT
# Re-runs tiramemsu's `tm export --format sg-nt12` tests with TM_SG_UPDATE=1 (which rewrites
# crates/tiramemsu-cli/tests/sg/*.nt), copies the files to statements/StatementsTests/data/tm/,
# writes index.txt (file and view flags, from the file name) and records the source commit.
# StatementsTests/Golden.lean then checks that each file decodes in its view and exports back
# byte for byte. Review the diff before committing.
set -eu
ROOT=$(cd "$(dirname "$0")/.." && pwd)
TM=$(cd "$1" && pwd)
OUT="$ROOT/statements/StatementsTests/data/tm"
(cd "$TM" && TM_SG_UPDATE=1 cargo test -q -p tiramemsu-cli --test sg >/dev/null)
mkdir -p "$OUT"
rm -f "$OUT"/*.nt
cp "$TM"/crates/tiramemsu-cli/tests/sg/*.nt "$OUT"/
: > "$OUT/index.txt"
for f in "$OUT"/*.nt; do
  n=$(basename "$f")
  view=${n#*.}; view=${view%.nt}
  case $view in
    now) flags="--now" ;;
    history) flags="--history" ;;
    asof*) flags="--as-of ${view#asof}" ;;
    valid-at) flags="--now --valid-at 1800000000000" ;;
    *) echo "unknown view in $n" >&2; exit 3 ;;
  esac
  echo "$n $flags" >> "$OUT/index.txt"
done
COMMIT=$(cd "$TM" && git rev-parse --short HEAD)
DIRTY=$(cd "$TM" && git status --porcelain crates/tiramemsu-cli | head -1)
[ -z "$DIRTY" ] || COMMIT="$COMMIT (with uncommitted changes)"
printf '%s\n' "$COMMIT" > "$OUT/SOURCE"
echo "recorded $(ls "$OUT"/*.nt | wc -l | tr -d ' ') files from tiramemsu $COMMIT"
