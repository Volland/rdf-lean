# LeanRDF

<img src="site/assets/logo.svg" alt="LeanRDF logo" width="72" align="right">

**Website, book, documentation and examples: https://volland.github.io/rdf-lean/**

LeanRDF is RDF semantics you can prove. It is a set of Lean 4 libraries with a native RDF 1.2 data model (triple terms, reification and base directions included) and the W3C semantics of RDF, RDFS, OWL 2 RL and EL, SPARQL 1.1 and SHACL Core, written as Lean definitions. Untrusted engines find answers. A verified checker, or an engine proven against the semantics, turns them into theorems.

- **Elpi finds, Lean checks.** Elpi (λProlog, through [lean-elpi](https://github.com/Volland/lean-elpi)) saturates a graph and produces a proof certificate. The checker is proven sound, so an accepted certificate gives the theorem `g.RDFSEntails q` or `g.OWLEntails q`. A bug in the search can only produce a rejected certificate, never a wrong answer.
- **oxilite finds and stores, LeanRDF proves.** [oxilite](https://oxilitedb.com), a SPARQL store on SQLite, answers queries and materializes OWL closures. LeanRDF certifies each answer from oxilite's own explanation or from Elpi, and audits the whole closure.
- **Where certificates are not enough, the engine is proven.** A certificate shows that something follows, not that nothing is missing. The SPARQL evaluator and the SHACL validator are therefore proven to compute their semantics exactly.

## What is proven

| Package | Directory | Main theorem |
|---|---|---|
| `leanrdf` | `.` | `checkQuery_sound`: an accepted certificate gives `g.RDFSEntails q`, under 80 RDFS rules each proven sound; `checkQuery_sound_rdf` and `checkQuery_sound_simple` for the RDF and simple regimes |
| `leanrdf-owl` | `owl/` | `Derives.owl_sound`, `Derives.el_sound`: 60 OWL 2 RL rules and 10 EL rules proven sound for the OWL 2 RDF-Based conditions |
| `leanrdf-sparql` | `sparql/` | `evalN_perm`, `runQuery_answer`: the evaluator's solutions are the SPARQL 1.1 semantics, up to order |
| `leanrdf-shacl` | `shacl/` | `validate_conforms`, `validate_sound`: "conforms" exactly when the data conforms, and every result is a real violation |
| `leanrdf-statements` | `statements/` | `decode_toRDF`, `toRDF_decode`: tiramemsu's bitemporal statement records export to RDF 1.2 reification and decode back exactly; `criterion` and `kernel_greatest`: the paper's Statement Graph criterion and export kernel |
| `leanrdf-elpi` | `elpi/` | the untrusted search: Elpi saturation, certificates, the demo, the oxilite bridge and the classifier |

The libraries contain no `sorry` and no new axioms. They use only `propext`, `Quot.sound` and `Classical.choice`, and tests pin the axioms of every main theorem. There is no Mathlib dependency: the core package depends on nothing.

| Test suite | Result |
|---|---|
| W3C RDF 1.1 N-Triples, Turtle, N-Quads, TriG | all pass |
| W3C RDF 1.2 N-Triples, N-Quads (with canonicalization), Turtle, TriG | all pass |
| W3C RDF 1.2 Semantics | 20 run: 16 certified, 4 not derived; 9 need datatypes outside D |
| W3C SPARQL 1.1 Query | 97 syntax and 257 evaluation tests pass |
| W3C SHACL Core | 98 / 98 |
| Statement graphs, exhaustive | all 406,901 graphs of at most 4 records |

## Quick start

Install [elan](https://github.com/leanprover/elan). Every package pins Lean 4.35.0.

```bash
git clone https://github.com/Volland/rdf-lean && cd rdf-lean
lake build && lake test
cd elpi && lake build
lake exe leanrdf-demo examples/pets.nt examples/query-mammal-owner.nt
```

```
Query instance: _:owner ↦ <http://example.org/bob>
Query instance: _:pet ↦ <http://example.org/tom>
Certificate: 6 nodes, goals [1, 4, 5]
  [4] <http://example.org/bob> rdf:type <http://example.org/Person>  (rdfs2 [2, 1])
  [5] <http://example.org/tom> rdf:type <http://example.org/Mammal>  (rdfs9 [0, 3])
Verdict: ENTAILED. The certificate was accepted by the verified checker (compiled).
```

In Lean, the same pipeline ends in a theorem:

```lean
def cert : Certificate := (entailmentCertificate g q).toOption.getD default
theorem g_entails_q : g.RDFSEntails q := checkQueryB_sound (c := cert) (by native_decide)
```

## Tools

| Command | Package | Purpose |
|---|---|---|
| `leanrdf-demo DATA.nt QUERY.nt [--cert OUT.json]` | `elpi/` | RDFS entailment of a query graph, with a checked certificate |
| `leanrdf-oxilite DATA PATTERN [--profile owl]` | `elpi/` | certify oxilite's answers; `--materialized` audits its OWL closure |
| `leanrdf-classify ONTOLOGY` | `elpi/` | certified class hierarchy of an OWL 2 EL ontology |
| `leanrdf-sparql query --location FILE --query Q` | `sparql/` | run a SPARQL 1.1 query with the proven evaluator |
| `leanrdf-shacl validate --data DATA --shapes SHAPES` | `shacl/` | SHACL Core validation, report in Turtle |
| `leanrdf-sg check\|export\|decode\|kernel\|quote FILE` | `statements/` | statement records to RDF 1.2 and back, the export kernel, the quoting view |

Exit codes are the same for every tool: `0` proven or ran, `1` not derived or does not conform, `2` a certificate was rejected (a bug on the untrusted side), `3` input error. "Not derived" is never a claim that something is false, because the rules are proven sound, not complete.

## Examples

[`examples/`](examples/) has a runnable example for every tool, with recorded outputs. `scripts/examples.sh` checks them, and CI runs it on every push:

- RDFS entailment on a university ontology;
- RDF 1.2 reification: annotations, reified triples and propositions;
- statement graphs: bitemporal records exported per view, decoded back, and their kernel;
- six SPARQL queries over a library;
- SHACL validation of employees;
- oxilite's OWL 2 RL answers and closure, certified from a recording (including an explanation of oxilite's that LeanRDF rejects);
- certified classification of a SNOMED-style EL ontology.

Lean examples that compile with the tests show each library from code. `elpi/BridgeTests/CustomRule.lean` walks through adding a rule of your own: the rule, its soundness proof, Elpi search and the theorem.

## Use it as a dependency

```lean
require leanrdf from git "https://github.com/Volland/rdf-lean" @ "main"
require «leanrdf-shacl» from git "https://github.com/Volland/rdf-lean" @ "main" / "shacl"
```

Sub-packages are named by their directory: `sparql`, `owl`, `shacl`, `statements` or `elpi`. See [Packages and installation](https://volland.github.io/rdf-lean/docs/packages/).

## Build and test everything

```bash
lake build && lake test                    # leanrdf
(cd sparql && lake build && lake test)     # leanrdf-sparql, with the W3C SPARQL suite
(cd owl && lake build && lake test)        # leanrdf-owl
(cd shacl && lake build && lake test)      # leanrdf-shacl, with the W3C SHACL Core suite
(cd statements && lake build && lake test) # leanrdf-statements, with the exhaustive check
(cd elpi && lake build && lake test)       # leanrdf-elpi
scripts/examples.sh                        # the runnable examples
```

## Read more

- **[The book](https://volland.github.io/rdf-lean/book/)**: sixteen short chapters, from triples to model theory, rules, countermodels, Elpi, certificates, your own rules, certifying oxilite, SPARQL, OWL, SHACL and statement graphs, and what is proven and trusted.
- **[The documentation](https://volland.github.io/rdf-lean/docs/)**: installation, every tool, the library API of each package, the certificate format, testing and contributing.
- **[The roadmap](https://volland.github.io/rdf-lean/roadmap/)**: what was built, phase by phase.
- **Design and requirements**: decisions, constraints and simplifications are a typed graph in `tg.md/`, and the requirements are OpenSpec capabilities in `openspec/specs/`. Read them with `tg search`, `tg section` and `tg trace --gaps`.

The site is built from `site/` with `python3 site/build.py`, using the Python standard library only.

## Licence

LeanRDF is licensed under either of the [MIT licence](LICENSE-MIT) or the [Apache License 2.0](LICENSE-APACHE), at your option. The W3C test suites vendored under the packages' test data keep their own licences.
