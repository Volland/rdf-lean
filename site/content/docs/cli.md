---
title: Command-line tools
order: 3
summary: Every executable, its arguments, input formats, output and exit codes.
---
# Command-line tools

Five executables ship with LeanRDF. Run them with `lake exe NAME` in their package directory, or call the binary in `.lake/build/bin/` after `lake build`. They share one convention for exit codes:

| Code | Meaning |
|---|---|
| `0` | everything the tool reports was proven, or the query ran |
| `1` | something was not derived, or the data does not conform |
| `2` | a certificate was rejected by the verified checker: a bug on the untrusted side |
| `3` | a usage, input, parse or process error: no verdict |

A `1` is never a claim that something is false. LeanRDF proves that certified things hold, but its rules are not proven complete, so "not derived" only reports that the search found nothing.

Input formats are chosen by file extension: `.nt` is N-Triples, `.nq` N-Quads, `.trig` TriG, and anything else is read as Turtle with the file's `file://` path as base IRI. The demo reads N-Triples only.

## leanrdf-demo

```
leanrdf-demo DATA.nt QUERY.nt [--cert OUT.json] [--datalog OUT.json]
```

Is the query graph RDFS-entailed by the data? Blank nodes in the query are existential, so `_:x rdf:type ex:Animal` asks whether something is an animal. The demo saturates the data in Elpi under the 80 RDFS rules, finds an instance of the query in the closure, cuts out a certificate, checks it with the compiled verified checker and prints:

- the number of data and query triples, and the size of the closure;
- the instance found, one `Query instance: _:b ↦ term` line per blank node;
- the certificate, one node per line, with its rule and premises;
- the verdict: `ENTAILED`, `NOT DERIVED` or `REJECTED`.

| Option | Effect |
|---|---|
| `--cert OUT.json` | write the certificate as JSON ([format](/docs/certificates/)) |
| `--datalog OUT.json` | write it as a CertifyingDatalog `GraphProblemInput`, for an independent check |

Exit codes: `0` entailed and checked, `1` not derived, `2` certificate rejected or search failed, `3` input error.

```bash
cd elpi
lake exe leanrdf-demo examples/pets.nt examples/query-mammal-owner.nt --cert cert.json
lake exe leanrdf-demo ../examples/rdfs-university/university.nt \
  ../examples/rdfs-university/query-staff-teaches.nt
```

## leanrdf-oxilite

```
leanrdf-oxilite DATA PATTERN [--oxilite PATH] [--profile rdfs|owl] [--mode elpi|why|both]
                [--results FILE] [--why-dir DIR] [--record DIR]
leanrdf-oxilite DATA --materialized [--oxilite PATH] [--inferred FILE] [--record DIR]
```

**Answers.** The first form loads `DATA` into a fresh oxilite store in a temporary directory, asks oxilite for the solutions of `PATTERN` (a graph whose blank nodes are the variables), and certifies each answer. For every solution it prints the bindings, the result of each route and a verdict:

```
[1] ?unit = <http://example.org/org#compilers>
    elpi: certified
    why:  untranslated (oxilite gave no rule: explained above)
    verdict: CERTIFIED
```

| Option | Default | Effect |
|---|---|---|
| `--oxilite PATH` | `oxilite` | the oxilite binary |
| `--profile rdfs` | yes | oxilite reasons with RDFS at query time; certificates are checked against the 80 RDFS rules |
| `--profile owl` | | oxilite materializes its OWL 2 RL closure; certificates are checked against `owlRules` (140 rules) |
| `--mode elpi` | | certify by Elpi search only |
| `--mode why` | | certify from oxilite's `why` trees only |
| `--mode both` | yes | both routes; an answer is certified when either certificate is accepted |
| `--record DIR` | | save oxilite's `results.json` and `why-N.json` in `DIR` |
| `--results FILE` | | replay recorded results instead of running oxilite |
| `--why-dir DIR` | | replay recorded `why-N.json` trees |

A route reports `certified`, `not derived`, `untranslated` (the tree could not be turned into a certificate, with the reason) or `REJECTED`. Exit codes: `0` every answer certified, `1` some answer not certified and none rejected, `2` a certificate rejected, `3` an input or process error.

**Materialized closure.** The second form runs oxilite's OWL 2 RL materialization and certifies every inferred triple it stored, each as its own query. It prints the totals (`oxilite inferences: 31, certified: 16`) and, per triple, the rule oxilite names and the result. `--inferred FILE` replays a recorded closure: one line per inference, the rule, a tab, and the triple in N-Triples.

See [oxilite](/docs/oxilite/) for the whole workflow.

## leanrdf-classify

```
leanrdf-classify ONTOLOGY
```

The certified class hierarchy of an OWL 2 EL ontology (Turtle or N-Triples). It saturates the ontology in Elpi under `owlELRules` (RDFS, OWL 2 RL and the EL rules), then certifies every derived `A rdfs:subClassOf B` between named classes as its own query. It prints only certified subsumptions, with names shortened to the part after `#` or the last `/`:

```
certified subsumptions: 36, unsatisfiable classes: 2
:Endocarditis ⊑ :Carditis
...
:PhantomPain ⊑ owl:Nothing (unsatisfiable)
```

A named class is an IRI outside the RDF, RDFS, OWL and XSD namespaces. Subsumption by `owl:Nothing` is printed as unsatisfiability. Exit codes: `0` every derived subsumption certified, `1` some not, `2` a certificate rejected, `3` an input or search error.

## leanrdf-sparql

```
leanrdf-sparql query --location FILE --query QUERY [--results-format FORMAT]
```

Runs a SPARQL 1.1 query with the evaluator that is proven to compute the SPARQL semantics. `FORMAT` is `json` (the default), `xml`, `csv` or `tsv`. The flags follow oxilite's and Oxigraph's. `FILE` may be N-Triples, N-Quads, Turtle or TriG. `QUERY` is the query text, not a file name, so use `--query "$(cat q.rq)"`.

| Query form | Output |
|---|---|
| `SELECT` | solutions in the chosen format, JSON by default |
| `ASK` | `true` or `false` in the chosen format |
| `CONSTRUCT`, `DESCRIBE` | N-Triples, whatever the format option |

A query with `FROM` or `FROM NAMED` is an error: the command line loads no graphs other than `FILE`. Exit codes: `0` the query ran, `3` an input, parse or evaluation error.

The evaluator is a reference for test-sized data. It is not meant for production.

## leanrdf-shacl

```
leanrdf-shacl validate --data DATA --shapes SHAPES
```

Validates the data graph against the SHACL Core shapes and prints a validation report in Turtle (`sh:ValidationReport` with `sh:conforms` and one `sh:result` per result). The blank nodes of the shapes graph are renamed apart from the data's. A file may serve as both, with `--data g.ttl --shapes g.ttl`. Shapes that refer to themselves, directly or through other shapes, are rejected with an error, because SHACL leaves their meaning undefined.

Exit codes: `0` the data conforms, `1` it does not, `3` an input error or ill-formed shapes.

## Scripts

| Script | Purpose |
|---|---|
| `scripts/examples.sh [--update] [GROUP]` | run the examples and compare their outputs with `expected/`; `GROUP` is `all` (the default), `sparql`, `shacl` or `elpi`; `--update` records them |
| `scripts/examples-record.sh OXILITE` | record oxilite's outputs for the oxilite examples |
| `scripts/oxilite-fixtures.sh OXILITE` | record oxilite's outputs for the bridge tests |
| `scripts/shacl-oxilite-fixtures.sh OXILITE` | record oxilite's SHACL reports for the SHACL tests |
| `scripts/sparql-diff.sh OXILITE` | run the W3C SPARQL suite on oxilite too and write `sparql/diff-report.md` |
| `scripts/check_release.py [--online]` | check the release contract: licences, metadata, CI workflow |
| `python3 site/build.py` | build this website into `_site/` |
