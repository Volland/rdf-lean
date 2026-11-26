#!/bin/bash
# usage: launch.sh <head|base>
P=$HOME/projects/rdf-lean-wt/paranoid
w=$1
s=$(date +%s)
docker run --rm --name rdf-check-$w --platform linux/arm64 --cpus 6 --memory 10g -e LEAN_NUM_THREADS=6 \
 --security-opt seccomp=unconfined --security-opt apparmor=unconfined --security-opt systempaths=unconfined \
 -v $P/check-$w:/work/check-$w -v $P/logs/check/$w:/logs -v $P/docker:/scripts:ro rdf-lean-paranoid \
 /scripts/run-check.sh /work/check-$w $w . owl sparql shacl statements check elpi
echo "container total wall $(( $(date +%s) - s ))s"
