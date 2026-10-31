---
title: Testing and CI
order: 13
summary: What each package's test suite checks, the W3C suites, axiom guards, recorded fixtures, the examples script and the CI jobs.
---
# Testing and CI

Tests in LeanRDF are mostly Lean code that must compile: `#guard` checks evaluated at build time, theorems about concrete data, and `#print axioms` guards. `lake test` builds a package's test library and runs its test driver. A failed check is a build error that names the file and line.

## Test suites

| Package | Driver | What it covers |
|---|---|---|
| `leanrdf` | `Tests` | terms, literals, graphs and isomorphism; N-Triples, Turtle, N-Quads and TriG parsing and writing; the W3C syntax and evaluation suites of all four; XSD values; regex; the semantics, the small model and countermodels; every RDFS rule on examples; certificates and tampered certificates; the guide snippets |
| `leanrdf-sparql` | `SparqlTests` | mappings and the algebra semantics; the evaluator against the semantics; the parser; the W3C SPARQL 1.1 query suite (syntax and evaluation); the guide examples |
| `leanrdf-owl` | `OwlTests` | the OWL model and countermodels; OWL 2 RL and EL certificates; rule counts; axiom guards |
| `leanrdf-shacl` | `shaclW3C` | shape reading and the semantics on scenarios; the oxilite comparison; axiom guards; the guide examples; then the W3C SHACL Core suite as compiled code |
| `leanrdf-statements` | `statementsTests` | every spec scenario; golden exports per view; tiramemsu's recorded `tm export --format sg-nt12` files, decoded and exported back byte for byte; the `leanrdf-sg` scenarios; the guide example; then, compiled, an exhaustive check over all 406,901 statement graphs of at most four records (kernel against brute force, quoting, `decode` against `toRDF`) |
| `leanrdf-elpi` | `BridgeTests` | Elpi encoding and decoding; saturation, including cycles; every RDFS rule through Elpi; end-to-end certificates; the demo; oxilite replay under RDFS and OWL; classification; the custom-rule example |

Scenario tests carry `@tg: verifies::` annotations that point to the OpenSpec scenario they prove, so `tg trace --gaps` reports any scenario that no test proves.

## The W3C suites

The suites are vendored under each package's test data, with their licences, and are read at build time through `input_dir`, so a change to the data rebuilds the tests.

| Suite | Result |
|---|---|
| RDF 1.1 N-Triples | 70 / 70 |
| RDF 1.1 Turtle | 313 / 313 |
| RDF 1.1 N-Quads, TriG | all pass |
| SPARQL 1.1 Query | 97 syntax and 257 evaluation tests pass; 10 subqueries with RDF/XML data skipped |
| SHACL Core | 98 / 98, empty skip list |

A test on a skip list that starts passing fails the build, so a skip list cannot outlive its reason.

## Axiom guards

Each package has an `Axioms.lean` that runs `#print axioms` on its main theorems and compares the output with the expected list, usually `propext`, `Classical.choice` and `Quot.sound`. A proof that picks up `sorryAx`, a new axiom or `Lean.ofReduceBool` (from `native_decide`) changes the output and fails the build.

## Recorded fixtures

External engines are never run in CI. Their outputs are recorded and replayed:

| Fixtures | Recorded by | Replayed by |
|---|---|---|
| `elpi/BridgeTests/data/oxilite/*/` | `scripts/oxilite-fixtures.sh` | `BridgeTests/Oxilite.lean`, `OxiliteOwl.lean` |
| `shacl/ShaclTests/data/oxilite/*/` | `scripts/shacl-oxilite-fixtures.sh` | `ShaclTests/Oxilite.lean` |
| `examples/owl-rl-family/recorded/` | `scripts/examples-record.sh` | `scripts/examples.sh` |
| `sparql/diff-report.md` | `scripts/sparql-diff.sh` | read by people, committed |

## Examples

`scripts/examples.sh` runs every example in `examples/` with the built tools and compares the output, including the exit code, with `examples/*/expected/*.txt`. `scripts/examples.sh --update` rewrites the expected files after an intended change. Review the diff before you commit it. Pass `sparql`, `shacl`, `elpi` or `statements` to run one group.

## CI

`.github/workflows/ci.yaml` runs on every push to `main` and every pull request, with one job per package:

| Job | Steps |
|---|---|
| core | `lake build`, `lake test`, `scripts/check_release.py` |
| sparql | `lake build`, `lake test`, `scripts/examples.sh sparql` |
| owl | `lake build`, `lake test` |
| shacl | `lake build`, `lake test`, `scripts/examples.sh shacl` |
| elpi | `lake build`, `lake test`, the demo, the EL classification, `scripts/examples.sh elpi` |
| statements | `lake build`, `lake test`, `scripts/examples.sh statements` |

`.github/workflows/pages.yml` builds this site with `python3 site/build.py` and publishes it on pushes that change `site/`.
