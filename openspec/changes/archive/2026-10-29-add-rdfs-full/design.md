## Context

RDF 1.1 Semantics §9.2.1 lists rdfs1–rdfs13; §8.1.1 lists rdfD1 and rdfD2, and gives GrdfD1 as the generalized replacement for rdfD1. All are Horn over generalized RDF; some need side conditions (`ddd ∈ D`, `rdf:_n`). The rule format has had a `guards` field since M3, so this change adds no format change.

## Goals / Non-Goals

**Goals:** every RDFS 1.1 pattern for `D = {xsd:string, rdf:langString}`, each proven sound; guards decided by code proven to agree with their meaning.

**Non-Goals:** completeness; datatypes beyond D; `rdf:_n` axioms for IRIs that occur only in subject or object position.

## Decisions

### Three guards, one meaning each

`containerMembership v` means `σ v = rdf:_(n+1)`. It is decided by reading the digits after `rdf:_` and recomputing the IRI (`containerIndex?`), so `rdf:_0`, `rdf:_03` and other near misses fail without any reasoning about decimal syntax. `stringLiteral v` and `langLiteral v` test the literal's form. `Guard.check_sound` is the only fact the checker's proof needs.

### GrdfD1 as two rules

A head is a fixed pattern, so the datatype of the literal cannot be read off the variable. GrdfD1 splits into `GrdfD1-string` (guard `stringLiteral`, head `… rdf:type xsd:string`) and `GrdfD1-langString`.

### Axioms as rules without premises

The 8 RDF and 38 RDFS axiomatic triples without `rdf:_n`, plus the two rdfs1 triples for D, become `axiomRule`s named after their triple. One proof covers all of them through the new `RDFSCore.axioms` field. In Elpi they are `rdf.axiom` facts added after the input facts. The `rdf:_n` axioms are three guarded rules on predicate position, `rdfs-axiom-cmp-*`.

### RDFSCore grows, toCore moves

The new rules need conditions from both the RDF (§8) and RDFS (§9) tables, plus two consequences of the D-interpretation conditions for literal values. So `RDFSCore` gains those fields, and `RDFSConditions.toCore` becomes `DInterp.IsRDFS.toCore`.

### Elpi guards

`stringLiteral` and `langLiteral` become unification goals. `containerMembership` becomes `rdf.is-cmp V`, whose facts Lean asserts for the container IRIs of the input graph. The rules invent no IRIs, so no other `rdf:_n` can appear.

## Constraints

[[constraints#RDF interpretations recognize two datatypes]], [[constraints#RDFS interpretation conditions]], [[constraints#Entailment rules use generalized RDF]].

## Risks / Trade-offs

- **Closure size.** One triple closes to 153 triples under the full rules; golden closure tests stay on `rdfsBasicRules` so they remain hand-checkable.
- **Container IRIs in subject or object position** get no axioms; recorded in [[simplifications#Container axioms only for occurring rdf:_n]].
