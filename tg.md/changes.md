---
type: Change
status: proposed
date: 2026-10-29
---
# Changes

The OpenSpec changes that build LeanRDF, one per milestone, in order. Each lives in `openspec/changes/<name>/` (`openspec/changes/archive/` once done) and is archived, and committed, when its acceptance criteria pass.

Do not start a change before the one it depends on is archived; the Elpi bridge depends on stable `Rule` definitions.

## M0 skeleton

Task 0 and the empty skeleton: [[integration-contract]], both Lake packages building and `lake test` running in each. Done on 2026-10-29 without an OpenSpec change.

- status:: applied

## add-rdf-core

M1: terms, literals, generalized triples with `WellFormed`, the opaque graph with its membership lemmas, blank-node isomorphism as a definition, and the `rdf:`, `rdfs:`, `xsd:` vocabulary.

Capability `rdf-core`. Unit tests for term equality, triples and graph operations; no `sorry`. `Literal` is declared in `Core/Term.lean` because `Term` contains it; its operations are in `Core/Literal.lean`.

- status:: archived

## add-ntriples

M2: native N-Triples parser and sorted serializer, passing the W3C `rdf-n-triples` positive and negative syntax tests, with stable round-trips.

Capability `ntriples`. Depends on [[changes#add-rdf-core]].

- status:: archived

## add-rdfs-entailment

M3: `SimpleInterp`, `RDFInterp`, `RDFSInterp` and `RDFSCore`; `Rule` with guards; `Derives`; `Derives.sound` and `Derives.sound_graph` for rdfs2, 3, 5, 7, 9 and 11; the vacuity tests.

Capabilities `rdf-semantics` and `rdfs-entailment`. See [[decisions#Semantics tested against vacuity]].

- status:: archived

## add-elpi-bridge

M4: a hand-written Elpi term encoding, generated `step` clauses, the `saturate.elpi` driver and closure readout; subclass and domain/range golden cases.

Capability `elpi-bridge`, in the `leanrdf-elpi` package.

- status:: archived

## add-certificates

M5: certificate format and JSON, `check` and `check_sound`, the CertifyingDatalog exporter, negative tests on tampered certificates, and the end-to-end test from N-Triples to `Derives`.

Capability `certificates`.

- status:: archived

## add-rdfs-full

The remaining RDFS 1.1 patterns (`rdfs1`, `rdfD2`, `GrdfD1`, `rdfs4a` to `rdfs13`) with their guards and the finite axiomatic triples, each proven sound.

Extends `rdfs-entailment`. Comes after [[changes#add-certificates]] and before the demo, so the demo shows a full closure.

- status:: archived

## add-demo

M6: `lake exe leanrdf-demo` per [[decisions#Demo never claims non-entailment]], with an example ontology and queries.

- status:: archived

## add-turtle

M7: native Turtle parser on the W3C `rdf-turtle` suite.

Capability `turtle`. See [[decisions#N-Triples first, native Turtle later]].

- status:: archived

## release-v0-1

P0: licence `MIT OR Apache-2.0`, package metadata, CI for both packages, the public repository and the `v0.1.0` release.

Capability `release`. Starts the roadmap of [[decisions#LeanRDF is the proof layer for oxilite]]. See [[decisions#Dual licence, CI and a tagged release]]. Released on 2026-10-30.

- status:: archived

## add-datasets

P1: `Quad` and `Dataset`, N-Quads and TriG with the W3C suites.

Capability `datasets`. See [[decisions#Datasets as sets of quads]] and [[decisions#TriG on the Turtle statement parser]], which supersede [[decisions#No datasets in v0.x]].

- status:: archived

## add-xsd-values

P1: XSD value spaces, canonical forms with round-trip proofs, and comparison with numeric promotion.

Capability `xsd-values`. See [[decisions#Exact XSD values with proven canonical forms]].

- status:: archived

## add-oxilite-certify

P2: certify oxilite's RDFS answers from its `why` trees or with Elpi; `leanrdf-oxilite`.

Capability `oxilite-bridge`. Depends on [[changes#release-v0-1]]. See [[decisions#Two ways to certify oxilite's answers]].

- status:: archived

## add-sparql-algebra

P3: package `leanrdf-sparql` with the §18 algebra semantics, expressions, a regex engine and an evaluator proven against the semantics.

Capability `sparql-algebra`. Depends on [[changes#add-datasets]] and [[changes#add-xsd-values]]. See [[decisions#Layers as packages in one repository]] and [[decisions#A proven reference evaluator for SPARQL]].

- status:: archived

## add-sparql-syntax

P3: SPARQL 1.1 parser and translation, result formats, `leanrdf-sparql`, the W3C query tests and a differential report against oxilite.

Capability `sparql-syntax`. Depends on [[changes#add-sparql-algebra]]. See [[decisions#SPARQL syntax, extensions and the W3C suite]].

- status:: archived

## add-owl-rl

P4: package `leanrdf-owl` with the OWL 2 RDF-Based conditions and the fixed-arity OWL 2 RL rules proven sound; OWL why trees and materialized inferences from oxilite certified.

Capabilities `owl-rl` and `oxilite-bridge`. Depends on [[changes#add-oxilite-certify]]. See [[decisions#OWL 2 RL as sound rules over a subset of the RDF-Based conditions]].

- status:: archived

## add-shacl-core

P5: package `leanrdf-shacl` with the SHACL Core semantics, a validator proven against it and the W3C core tests.

Capability `shacl-core`. Depends on [[changes#add-datasets]], [[changes#add-xsd-values]] and the regex engine of [[changes#add-sparql-algebra]]. See [[decisions#SHACL Core with a validator proven against its semantics]].

- status:: archived

## add-owl-el

P6: EL completion rules proven sound and certified classification with `leanrdf-classify`.

Capability `owl-el`. Depends on [[changes#add-owl-rl]]. See [[decisions#EL classification by fixed-length lists and certified subsumptions]].

- status:: archived

## add-rdf12-core

R1: `Term.triple`, `Literal.dirLang`, recursive `WellFormed`, `Basic`, isomorphism through triple terms, `IT` in simple interpretations, N-Triples and N-Quads 1.2, and opaque pass-through in every package.

Capabilities `rdf-core`, `ntriples`, `datasets`, `rdf-semantics`, `elpi-bridge`, `certificates`, `sparql-algebra`, `sparql-syntax`, `shacl-core`, `oxilite-bridge`. Depends on [[changes#add-owl-el]]. See [[rdf12]].

- status:: archived

## add-rdf12-syntax

R2: Turtle and TriG 1.2, covering version directives, `LANG_DIR`, triple terms, reified triples and annotations desugared by §7.3, plus the W3C RDF 1.2 Turtle and TriG suites.

Capabilities `turtle` and `datasets`. Depends on [[changes#add-rdf12-core]]. See [[rdf12#Reification as sugar in the statement parser]].

- status:: proposed

## add-rdf12-semantics

R3: the RDF and RDFS layers of RDF 1.2 Semantics: `rdf:dirLangString` recognized, `rdfs:Proposition`, the new axioms, rdfs14 and rdfs14a proven sound, and the W3C RDF 1.2 semantics tests. Release v0.2.0.

Capabilities `rdf-semantics`, `rdfs-entailment` and the bridge capabilities. Depends on [[changes#add-rdf12-syntax]]. See [[rdf12]].

- status:: proposed

## add-statement-graphs

S1: package `leanrdf-statements`, adding bitemporal statement records, views, the exact reifier export to RDF 1.2, the paper's kernel, criterion, history and quoting results, and `leanrdf-sg`. Release v0.3.0.

Capabilities `statement-graphs` and `xsd-values`. Depends on [[changes#add-rdf12-semantics]]. See [[statement-graphs]] and [[concepts]].

- status:: proposed
