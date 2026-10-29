## 1. Terms and literals

- [ ] 1.1 `LeanRDF/Core/Term.lean`: `IRI`, `BlankNode`, `Term` with `DecidableEq`, `Hashable`, `Ord`, `Repr`; doc comments citing RDF 1.1 Concepts §3.2 and §3.4; annotate with `@tg: implements:: [[openspec:rdf-core#RDF terms]]`
- [ ] 1.2 `LeanRDF/Core/Literal.lean`: `Literal`, `datatype`, `WellFormed`, `mk?`, `lang'`, `str`; annotate with `@tg: implements:: [[openspec:rdf-core#Literal forms]]`
- [ ] 1.3 `LeanRDF/Core/Vocab.lean`: namespaces, RDF and RDFS vocabulary, `xsd:string`, `rdf.member n`; annotate with `@tg: implements:: [[openspec:rdf-core#Vocabulary constants]]`

## 2. Triples and graphs

- [ ] 2.1 `LeanRDF/Core/Triple.lean`: `Triple`, decidable `WellFormed`, `mk?`, `renameBNodes`; annotate with `@tg: implements:: [[openspec:rdf-core#Generalized triples]]`
- [ ] 2.2 `LeanRDF/Core/Graph.lean`: opaque `Graph`, operations, decidable membership, the six `mem_*` theorems, sorted `toList`; annotate with `@tg: implements:: [[openspec:rdf-core#Graph membership API]]`
- [ ] 2.3 `LeanRDF/Core/Iso.lean`: `Graph.Iso`, `Graph.Iso.refl`; annotate with `@tg: implements:: [[openspec:rdf-core#Blank node isomorphism]]`
- [ ] 2.4 Import every Core module from `LeanRDF.lean`

## 3. Tests

- [ ] 3.1 `Tests/Core/Term.lean`: scenarios of `RDF terms`, each test annotated `@tg: verifies:: [[openspec:rdf-core#RDF terms#<Scenario>]]`
- [ ] 3.2 `Tests/Core/Literal.lean`: scenarios of `Literal forms`, annotated `@tg: verifies::`
- [ ] 3.3 `Tests/Core/Triple.lean`: scenarios of `Generalized triples`, annotated `@tg: verifies::`
- [ ] 3.4 `Tests/Core/Graph.lean`: scenarios of `Graph membership API`, annotated `@tg: verifies::`
- [ ] 3.5 `Tests/Core/Iso.lean`: scenarios of `Blank node isomorphism`, annotated `@tg: verifies::`
- [ ] 3.6 `Tests/Core/Vocab.lean`: scenarios of `Vocabulary constants`, annotated `@tg: verifies::`
- [ ] 3.7 `Tests/Core/Axioms.lean`: `#print axioms` guard on the `mem_*` theorems (only `propext`, `Quot.sound`, `Classical.choice`)

## 4. Docs and checks

- [ ] 4.1 Record any new decision or simplification found while implementing in `tg.md/decisions.md` or `tg.md/simplifications.md` with typed edges; add `openspec: [rdf-core]` to the frontmatter of the tg.md file that explains the capability
- [ ] 4.2 Mark `add-rdf-core` as applied in `tg.md/changes.md`
- [ ] 4.3 `grep -rn "sorry\|admit\|axiom " LeanRDF/` is empty
- [ ] 4.4 Run `lake build`, `lake test`, `tg check`, `tg ontology check` and `tg trace rdf-core --gaps`, and close every gap they report
