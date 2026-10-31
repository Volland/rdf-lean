# Examples

Runnable examples for every LeanRDF command-line tool. Each directory holds its input files and, in `expected/`, the output of each run followed by a line `# exit N` with its exit code. `scripts/examples.sh` runs them all and compares the output, and CI runs it on every push.

```bash
scripts/examples.sh              # run all and compare; prints "examples: all match"
scripts/examples.sh shacl        # one group: sparql, shacl, elpi or statements
scripts/examples.sh --update     # record new expected outputs after an intended change
```

| Directory | Tool | What it shows |
|---|---|---|
| [`rdfs-university/`](rdfs-university/) | `leanrdf-demo` | RDFS entailment with a checked certificate, and an honest "not derived" |
| [`rdf12-reification/`](rdf12-reification/) | `leanrdf-demo` | RDF 1.2 reification: an asserted annotation, a reified triple that is not asserted, propositions |
| [`statement-graphs/`](statement-graphs/) | `leanrdf-sg` | bitemporal statement records exported to RDF 1.2 reification, decoded back exactly, and their export kernel |
| [`sparql-library/`](sparql-library/) | `leanrdf-sparql` | SPARQL 1.1 queries run by the proven evaluator |
| [`shacl-employees/`](shacl-employees/) | `leanrdf-shacl` | SHACL Core validation with a conforming and a non-conforming graph |
| [`owl-rl-family/`](owl-rl-family/) | `leanrdf-oxilite` | oxilite's OWL 2 RL answers and closure, certified from a recording |
| [`owl-el-anatomy/`](owl-el-anatomy/) | `leanrdf-classify` | certified classification of an OWL 2 EL ontology |

The pet ontology of the book and the demo is in [`elpi/examples/`](../elpi/examples/). Lean examples that use the libraries directly are compiled with the tests: `elpi/BridgeTests/CustomRule.lean` (a rule of your own, end to end), `sparql/SparqlTests/Examples.lean`, `shacl/ShaclTests/Examples.lean` and `Tests/Guide/Core.lean`.

The website explains each example: https://volland.github.io/rdf-lean/examples/
