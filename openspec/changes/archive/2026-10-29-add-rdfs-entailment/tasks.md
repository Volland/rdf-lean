## 1. Semantics

- [x] 1.1 `LeanRDF/Semantics/Interpretation.lean`: `SimpleInterp`, denotation, `Holds`, `Satisfies`, `InClass`, `SubClass`, `SubProp`, `HoldsIRI`, `DInterp`; annotate `@tg: implements::` for `Simple interpretations` and `D-interpretations`
- [x] 1.2 `LeanRDF/Semantics/Axioms.lean`: RDF and RDFS axiomatic triples without `rdf:_n`
- [x] 1.3 `LeanRDF/Semantics/RDFS.lean`: `RDFConditions`, `RDFSConditions`, `IsRDF`, `IsRDFS`, `RDFSCore`, `toCore`, `IP_IR`; annotate `RDF interpretations` and `RDFS interpretations`
- [x] 1.4 `LeanRDF/Semantics/Entails.lean`: the four entailment relations and their implications; annotate `Entailment relations`

## 2. Entailment

- [x] 2.1 `LeanRDF/Entailment/Rule.lean`: `Pat`, `TPat`, `Subst`, `Guard`, `Rule`, `RangeRestricted`, `UniqueNames`; annotate `Rule format`
- [x] 2.2 `LeanRDF/Entailment/Rules.lean`: rdfs2, 3, 5, 7, 9, 11 and `rdfsRules`; annotate `RDFS rule set`
- [x] 2.3 `LeanRDF/Entailment/Derivation.lean`: `Derives`, `Triple.instantiate`; annotate `Derivation relation`
- [x] 2.4 `LeanRDF/Entailment/Soundness.lean`: per-rule soundness, `Derives.holds`, `Derives.sound`, `Derives.sound_graph`; annotate `Soundness`

## 3. Tests

- [x] 3.1 `Tests/Semantics/Basics.lean`: scenarios of the interpretation and entailment requirements, annotated `@tg: verifies::`
- [x] 3.2 `Tests/Semantics/SmallModel.lean`: the parametric RDFS model and `isRDFS`; annotate `Semantics is not vacuous` as implemented
- [x] 3.3 `Tests/Semantics/Vacuity.lean`: model existence and three countermodel non-entailments, annotated `@tg: verifies::`
- [x] 3.4 `Tests/Semantics/HandProofs.lean`: one semantic proof per rule, annotated `@tg: verifies::`
- [x] 3.5 `Tests/Entailment/Rules.lean`: rule data, a derivation, `Derives.sound` and `Derives.sound_graph` on it, annotated `@tg: verifies::`
- [x] 3.6 `Tests/Entailment/Axioms.lean`: `#guard_msgs` on the axioms of the soundness theorems

## 4. Docs and checks

- [x] 4.1 Update `tg.md/simplifications.md` and `tg.md/decisions.md` with the readings of the tables; add `rdf-semantics` and `rdfs-entailment` to the `openspec:` frontmatter
- [x] 4.2 Mark `add-rdfs-entailment` as applied in `tg.md/changes.md`
- [x] 4.3 No `sorry`, `admit`, `axiom` or `native_decide` in `LeanRDF/` or the vacuity tests
- [x] 4.4 Run `lake build`, `lake test` (both packages), `tg check`, `tg ontology check` and `tg trace rdf-semantics rdfs-entailment --gaps`, and close every gap
