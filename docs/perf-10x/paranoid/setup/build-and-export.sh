#!/bin/bash
# usage (inside container): build-and-export.sh <base|head>
# Clean build of each package's library in /work/exports/<rev>, then leanexport of the main theorems.
set -u
rev=$1
root=/work/exports/$rev
out=/work/logs/exports/$rev
mkdir -p $out
echo "rev=$rev commit=$(git -C $root rev-parse HEAD) start=$(date -u +%FT%TZ)" > $out/meta
ls -d $root/.lake $root/*/.lake 2>&1 >> $out/meta
step() { # name dir cmd...
  local name=$1 dir=$2; shift 2
  local s=$(date +%s)
  (cd $dir && "$@") > $out/$name.out 2> $out/$name.err
  local rc=$?
  echo "$name exit=$rc wall_seconds=$(( $(date +%s) - s ))" >> $out/meta
  return $rc
}
step build-check $root/check lake build LeanRDFCheck
step build-sparql $root/sparql lake build LeanRDFSparql
step build-shacl $root/shacl lake build LeanRDFShacl
step build-statements $root/statements lake build LeanRDFStatements
exp() { # pkgdir module decls...
  local pkg=$1 mod=$2; shift 2
  local s=$(date +%s)
  (cd $root/$pkg && lake env leanexport $mod -- "$@") > $out/$pkg.ndjson 2> $out/$pkg.export.err
  echo "export-$pkg exit=$? wall_seconds=$(( $(date +%s) - s )) bytes=$(stat -c %s $out/$pkg.ndjson)" >> $out/meta
}
exp check LeanRDFCheck LeanRDF.Cert.checkQuery_sound LeanRDF.Cert.checkQuery_sound_rdf LeanRDF.Cert.checkQuery_sound_simple LeanRDF.Canon.canonical_iso LeanRDF.Model.checkCountermodel_sound_rdfs LeanRDF.Derives.owl_sound LeanRDF.Derives.el_sound LeanRDF.Cert.checkClash_sound_owl LeanRDF.Check.checkRegime_sound
exp sparql LeanRDFSparql LeanRDF.Sparql.evalN_perm LeanRDF.Sparql.runQuery_answer
exp shacl LeanRDFShacl LeanRDF.Shacl.validate_conforms LeanRDF.Shacl.validate_sound
exp statements LeanRDFStatements LeanRDF.Statements.decode_toRDF LeanRDF.Statements.toRDF_decode LeanRDF.Statements.StatementGraph.criterion LeanRDF.Statements.StatementGraph.kernel_greatest
echo "end=$(date -u +%FT%TZ)" >> $out/meta
