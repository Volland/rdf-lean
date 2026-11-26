#!/bin/bash
# usage: run-check.sh <clone-dir-in-container> <label> <pkg>...
set -u
root=$1; label=$2; shift 2
logs=/logs
cd "$root"
echo "lake: $(command -v lake)  $(lake --version)" | tee -a $logs/$label.env.txt
git -C "$root" log --oneline -1 | tee -a $logs/$label.env.txt
for pkg in "$@"; do
  name=$([ "$pkg" = . ] && echo root || echo "$pkg")
  dir="$root/$pkg"
  pre=$(ls -d "$dir/.lake" 2>/dev/null || echo none)
  echo "== $label/$name start $(date -Is) pre-existing .lake: $pre" | tee -a $logs/$label.summary.txt
  s=$(date +%s)
  ( cd "$dir" && /usr/bin/time -v lake check --paranoid --json ) \
     > $logs/$label.$name.json 2> $logs/$label.$name.stderr.log
  rc=$?
  e=$(date +%s)
  j=$(jq -r '.judgement' $logs/$label.$name.json 2>/dev/null)
  echo "== $label/$name rc=$rc judgement=$j wall=$((e-s))s end $(date -Is)" | tee -a $logs/$label.summary.txt
done
