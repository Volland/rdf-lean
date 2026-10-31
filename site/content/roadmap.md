---
title: Roadmap
summary: What LeanRDF built, phase by phase: a v0.1 release, datasets and XSD values, certificates for oxilite's answers, SPARQL, OWL 2 RL, SHACL Core, OWL EL RDF 1.2 (v0.2) and statement graphs (v0.3), and what comes next.
---
# Roadmap

LeanRDF will not become a second database. [oxilite](https://oxilitedb.com) already stores RDF in SQLite, answers SPARQL through an Oxigraph-compatible API, and reasons with RDFS, OWL 2 RL, Datalog and SHACL. LeanRDF is its proof layer: **oxilite finds and stores, LeanRDF proves.**

Each phase below is an OpenSpec change, implemented, archived (`openspec/changes/archive/`) and committed in order. The seven phases of v0.1, the three RDF 1.2 changes of v0.2 and statement graphs (v0.3) are done. A phase started only when the phases it needs were done. New layers are separate Lake packages in this repository, so the core stays free of dependencies.

<figure><img src="{{BASE}}/assets/roadmap.svg" alt="Roadmap: P0 release, P1 core additions, P2 certify oxilite's RDFS answers, P3 SPARQL in Lean, P4 OWL 2 RL, P5 SHACL Core, P6 OWL EL, RDF 1.2 and statement graphs, with their dependencies"><figcaption>Nine phases in four lanes. An arrow means the later phase needs the earlier one.</figcaption></figure>

## Who does what

| Concern | oxilite: fast, not trusted | LeanRDF: the proof |
| --- | --- | --- |
| Storage and SPARQL | SQLite, D1 and Turso backends; SPARQL compiled to SQL | SPARQL semantics and a reference evaluator proven to compute it |
| RDFS | Query rewriting against a schema closure | A certificate per answer, checked against the 80 proven rules |
| Explanations | `why` proof trees over OWL 2 RL and RDFS templates | Each tree translated to a certificate and checked |
| OWL 2 RL | Materialized inferences, tagged with their producer | OWL 2 RL rules proven sound; each inference certified |
| SHACL | Validation through the rudof validators | SHACL Core semantics and a validator proven against it |

## Phases

| Phase | OpenSpec change | Package | Done when | Result |
| --- | --- | --- | --- | --- |
| P0 Release v0.1 | `release-v0-1` | all | MIT or Apache-2.0 licence; CI builds and tests both packages; `v0.1.0` tagged; the repository is public | Done: dual licence, CI for every package, `v0.1.0`, public repository |
| P1 Datasets | `add-datasets` | `leanrdf` | `Dataset`, N-Quads and TriG; the W3C N-Quads and TriG suites pass | Done: both W3C suites pass |
| P1 XSD values | `add-xsd-values` | `leanrdf` | Value spaces for integer, decimal, boolean, string and dateTime; canonical forms parse back to the same value, by proof | Done: canonical forms proven to read back |
| P2 Certify oxilite | `add-oxilite-certify` | `leanrdf-elpi` | Each RDFS answer oxilite gives is certified, either from oxilite's own `why` tree or by Elpi; a wrong answer is never accepted | Done: every recorded answer certified, tampered ones rejected |
| P3 SPARQL algebra | `add-sparql-algebra` | `leanrdf-sparql` | The SPARQL 1.1 algebra semantics in Lean, and an evaluator proven to return exactly its solution multisets for the core operators | Done: `evalN_perm`, `runQuery_answer` |
| P3 SPARQL syntax | `add-sparql-syntax` | `leanrdf-sparql` | SPARQL 1.1 queries parsed and translated to the algebra; W3C syntax tests pass; evaluation tests pass for the supported fragment; a CLI with oxilite's flags, and a differential run against oxilite | Done: 97/97 syntax and 257 evaluation tests, a differential report |
| P4 OWL 2 RL | `add-owl-rl` | `leanrdf-owl` | The fixed-arity OWL 2 RL rules proven sound against the OWL 2 RDF-Based semantics; oxilite's OWL `why` trees and materialized inferences certified | Done: 49 rules proven sound; 18 of 31 oxilite inferences certified, the rest have no OWL 2 RL rule |
| P5 SHACL Core | `add-shacl-core` | `leanrdf-shacl` | SHACL Core semantics; a validator proven to compute it; W3C core tests pass for the supported components | Done: `validate_conforms`, `validate_sound`; 98/98 W3C tests; agrees with oxilite |
| P6 OWL EL | `add-owl-el` | `leanrdf-owl` | EL classification rules proven sound; subsumptions of a small ontology certified | Done: 10 rules proven sound; the example hierarchy certified |
| R1 RDF 1.2 core | `add-rdf12-core` | all | Triple terms and base directions in the model, `IT` in the semantics, N-Triples and N-Quads 1.2; every package accepts the new terms | Done: W3C RDF 1.2 N-Triples and N-Quads suites pass, canonicalization included |
| R2 RDF 1.2 syntax | `add-rdf12-syntax` | `leanrdf` | Turtle and TriG 1.2: triple terms, reified triples, annotations | Done: W3C RDF 1.2 Turtle and TriG suites pass |
| R3 RDF 1.2 semantics | `add-rdf12-semantics` | `leanrdf`, `leanrdf-elpi` | `rdf:dirLangString`, `rdfs:Proposition`, rdfs14 proven sound; simple and RDF regimes; `v0.2.0` | Done: 80 RDFS rules; 20 W3C RDF 1.2 semantics tests run (16 certified, 4 not derived), 9 listed as needing other datatypes |
| S1 Statement graphs | `add-statement-graphs` | `leanrdf-statements` | tiramemsu's bitemporal records, an exact RDF 1.2 export, the export criterion and kernel proven; `v0.3.0` | Done: `decode_toRDF`, `toRDF_decode`, `criterion`, `kernel_greatest`; 406,901 small graphs checked exhaustively |

## Proven, not just certified

A certificate proves that a found answer is right. It cannot prove that nothing is missing. SPARQL needs both, because `OPTIONAL`, `MINUS`, `FILTER NOT EXISTS` and aggregates depend on what is absent. So LeanRDF's SPARQL evaluator is proven against the semantics, while reasoning answers are certified one at a time. Under RDFS or OWL reasoning a certified answer is proven sound, not complete.

## Later

A matching `tm export --format sg-nt12` in tiramemsu, so the statement-graph goldens are cross-checked against the store. Certificates for oxilite's Datalog programs, SHACL-SPARQL, a SPARQL HTTP endpoint, certifying oxilite's SPARQL-to-SQL translation itself, an ALC tableau, and lean-elpi's LF proof terms as a second certificate backend.
