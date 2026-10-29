## Why

The six rules of M3 miss most of what RDFS entails: resource and property typing (rdfs4a/4b, rdfD2), reflexivity (rdfs6, rdfs10), the class and datatype rules (rdfs8, rdfs12, rdfs13), literal typing (GrdfD1) and the axiomatic triples. This change adds every remaining RDFS 1.1 pattern, the guards they need, and their soundness proofs, before the demo shows a full closure.

## What Changes

- Give `Guard` three constructors (container membership IRI, `xsd:string` literal, language-tagged literal), each with a meaning, a checker and `Guard.check_sound`.
- Add rdfD2, rdfs4a, rdfs4b, rdfs6, rdfs8, rdfs10, rdfs12, rdfs13, GrdfD1 for both datatypes, the container membership axioms for `rdf:_n` used as predicates, and the 48 finite axiomatic triples (RDF, RDFS, rdfs1 for D) as rules without premises; prove each sound.
- Extend `RDFSCore` with the conditions these rules use, now derived from `IsRDFS` (`DInterp.IsRDFS.toCore`).
- Check guards in the certificate checker; generate guard goals and `rdf.axiom` facts for Elpi, and assert `rdf.is-cmp` facts per graph.
- Split `rdfsRules` into `rdfsBasicRules`, `rdfsExtraRules` and `axiomRules`.

## Capabilities

### New Capabilities

None.

### Modified Capabilities

- `rdfs-entailment`: guards gain constructors (new requirement `Guards`); `Rule format` and `RDFS rule set` change.
- `elpi-bridge`: `Rule clauses` supports guards and rules without premises.
- `certificates`: `Checker` evaluates guards.

## Impact

**Milestone:** between M5 and M6. Depends on `add-certificates` (archived).

**Code:** `LeanRDF/Entailment/{Rule,Rules,Soundness}.lean`, `LeanRDF/Semantics/{Axioms,RDFS}.lean`, `LeanRDF/Cert/Check.lean`, `elpi/LeanRDFElpi/{Codegen,Saturate}.lean`, `elpi/LeanRDFElpi/elpi/saturate.elpi`, tests.

**Motivating decisions** (tg.md): [[decisions#Horn rules matched by the checker]], [[decisions#Layered interpretations with a core]], [[decisions#Rules generated from Lean]].

**Constraints honoured:** [[constraints#RDF interpretations recognize two datatypes]], [[constraints#RDFS interpretation conditions]], [[constraints#Entailment rules use generalized RDF]].

**Simplifications:** [[simplifications#Container axioms only for occurring rdf:_n]].
