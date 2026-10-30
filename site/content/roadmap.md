---
title: Roadmap
summary: What LeanRDF builds next: a v0.1 release, datasets and XSD values, certificates for oxilite's answers, SPARQL, OWL 2 RL, SHACL Core and OWL EL.
---
# Roadmap

LeanRDF will not become a second database. [oxilite](https://oxilitedb.com) already stores RDF in SQLite, answers SPARQL through an Oxigraph-compatible API, and reasons with RDFS, OWL 2 RL, Datalog and SHACL. LeanRDF is its proof layer: **oxilite finds and stores, LeanRDF proves.**

Each phase below is an OpenSpec change in `openspec/changes/`, implemented, archived and committed in order. A phase starts only when the phases it needs are done. New layers are separate Lake packages in this repository, so the core stays free of dependencies.

<figure><img src="{{BASE}}/assets/roadmap.svg" alt="Roadmap: P0 release, P1 core additions, P2 certify oxilite's RDFS answers, P3 SPARQL in Lean, P4 OWL 2 RL, P5 SHACL Core, P6 OWL EL, with their dependencies"><figcaption>Seven phases in four lanes. An arrow means the later phase needs the earlier one.</figcaption></figure>

## Who does what

| Concern | oxilite: fast, not trusted | LeanRDF: the proof |
| --- | --- | --- |
| Storage and SPARQL | SQLite, D1 and Turso backends; SPARQL compiled to SQL | SPARQL semantics and a reference evaluator proven to compute it |
| RDFS | Query rewriting against a schema closure | A certificate per answer, checked against the 67 proven rules |
| Explanations | `why` proof trees over OWL 2 RL and RDFS templates | Each tree translated to a certificate and checked |
| OWL 2 RL | Materialized inferences, tagged with their producer | OWL 2 RL rules proven sound; each inference certified |
| SHACL | Validation through the rudof validators | SHACL Core semantics and a validator proven against it |

## Phases

| Phase | OpenSpec change | Package | Done when |
| --- | --- | --- | --- |
| P0 Release v0.1 | `release-v0-1` | all | MIT or Apache-2.0 licence; CI builds and tests both packages; `v0.1.0` tagged; the repository is public |
| P1 Datasets | `add-datasets` | `leanrdf` | `Dataset`, N-Quads and TriG; the W3C N-Quads and TriG suites pass |
| P1 XSD values | `add-xsd-values` | `leanrdf` | Value spaces for integer, decimal, boolean, string and dateTime; canonical forms parse back to the same value, by proof |
| P2 Certify oxilite | `add-oxilite-certify` | `leanrdf-elpi` | Each RDFS answer oxilite gives is certified, either from oxilite's own `why` tree or by Elpi; a wrong answer is never accepted |
| P3 SPARQL algebra | `add-sparql-algebra` | `leanrdf-sparql` | The SPARQL 1.1 algebra semantics in Lean, and an evaluator proven to return exactly its solution multisets for the core operators |
| P3 SPARQL syntax | `add-sparql-syntax` | `leanrdf-sparql` | SPARQL 1.1 queries parsed and translated to the algebra; W3C syntax tests pass; evaluation tests pass for the supported fragment; a CLI with oxilite's flags, and a differential run against oxilite |
| P4 OWL 2 RL | `add-owl-rl` | `leanrdf-owl` | The fixed-arity OWL 2 RL rules proven sound against the OWL 2 RDF-Based semantics; oxilite's OWL `why` trees and materialized inferences certified |
| P5 SHACL Core | `add-shacl-core` | `leanrdf-shacl` | SHACL Core semantics; a validator proven to compute it; W3C core tests pass for the supported components |
| P6 OWL EL | `add-owl-el` | `leanrdf-owl` | EL classification rules proven sound; subsumptions of a small ontology certified |

## Proven, not just certified

A certificate proves that a found answer is right. It cannot prove that nothing is missing. SPARQL needs both, because `OPTIONAL`, `MINUS`, `FILTER NOT EXISTS` and aggregates depend on what is absent. So LeanRDF's SPARQL evaluator is proven against the semantics, while reasoning answers are certified one at a time. Under RDFS or OWL reasoning a certified answer is proven sound, not complete.

## Later

Certificates for oxilite's Datalog programs, SHACL-SPARQL, a SPARQL HTTP endpoint, certifying oxilite's SPARQL-to-SQL translation itself, an ALC tableau, and lean-elpi's LF proof terms as a second certificate backend.
