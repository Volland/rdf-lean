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

- status:: proposed

## add-rdfs-entailment

M3: `SimpleInterp`, `RDFInterp`, `RDFSInterp` and `RDFSCore`; `Rule` with guards; `Derives`; `Derives.sound` and `Derives.sound_graph` for rdfs2, 3, 5, 7, 9 and 11; the vacuity tests.

Capabilities `rdf-semantics` and `rdfs-entailment`. See [[decisions#Semantics tested against vacuity]].

- status:: proposed

## add-elpi-bridge

M4: `deriving Elpi` encodings, generated `step` clauses, the `saturate.elpi` driver and closure readout; subclass and domain/range golden cases.

Capability `elpi-bridge`, in the `leanrdf-elpi` package.

- status:: proposed

## add-certificates

M5: certificate format and JSON, `check` and `check_sound`, the CertifyingDatalog exporter, negative tests on tampered certificates, and the end-to-end test from N-Triples to `Derives`.

Capability `certificates`.

- status:: proposed

## add-rdfs-full

The remaining RDFS 1.1 patterns (`rdfs1`, `rdfD2`, `GrdfD1`, `rdfs4a` to `rdfs13`) with their guards and the finite axiomatic triples, each proven sound.

Extends `rdfs-entailment`. Comes after [[changes#add-certificates]] and before the demo, so the demo shows a full closure.

- status:: proposed

## add-demo

M6: `lake exe leanrdf-demo` per [[decisions#Demo never claims non-entailment]], with an example ontology and queries.

- status:: proposed

## add-turtle

M7: native Turtle parser on the W3C `rdf-turtle` suite.

Capability `turtle`. See [[decisions#N-Triples first, native Turtle later]].

- status:: proposed
