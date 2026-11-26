#!/bin/bash
# usage: run-comparator.sh <pkg>   (runs inside the rdf-lean-paranoid container as uid 1000)
set -u
pkg=$1
if [ "$pkg" = root ]; then dir=/work/comparator/root; else dir=/work/comparator/$pkg/$pkg; fi
log=/work/logs
cd "$dir"
echo "pkg=$pkg dir=$dir start=$(date -u +%FT%TZ)" > $log/$pkg.meta
ls -la "$dir"/.lake 2>&1 | head -3 >> $log/$pkg.meta
start=$(date +%s)
lake comparator --paranoid --json > $log/$pkg.json 2> $log/$pkg.stderr
rc=$?
end=$(date +%s)
echo "exit=$rc wall_seconds=$((end-start)) end=$(date -u +%FT%TZ)" >> $log/$pkg.meta
