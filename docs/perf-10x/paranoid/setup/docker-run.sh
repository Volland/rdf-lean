#!/bin/bash
# usage: docker-run.sh <pkg> : runs `lake comparator --paranoid --json` for <pkg> in the rdf-lean-paranoid image
P=$HOME/projects/rdf-lean-wt/paranoid
exec docker run --rm --name cmp-$1 --cpus 6 \
  --security-opt seccomp=unconfined --security-opt apparmor=unconfined --security-opt systempaths=unconfined \
  --tmpfs /run/user \
  -v $P/comparator:/work/comparator -v $P/logs/comparator:/work/logs \
  rdf-lean-paranoid /work/logs/run-comparator.sh $1
