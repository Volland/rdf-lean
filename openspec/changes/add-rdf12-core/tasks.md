## 1. Data model

- [ ] 1.1 `LeanRDF/Core/Term.lean`: `Direction`, `Literal.dirLang`, `Term.triple`; recursive `Term.renameBNodes` with `renameBNodes_id`/`renameBNodes_comp`; `Triple.toTerm`, `Term.asTriple?`; annotate `RDF terms`
- [ ] 1.2 `LeanRDF/Core/Literal.lean`: `datatype` for `dirLang`, `Literal.dirLang'`, `mk?` rejecting `rdf:dirLangString`; annotate `Literal forms`
- [ ] 1.3 `LeanRDF/Core/Triple.lean`: recursive `WellFormed` with its `DecidablePred`, `mk?_wellFormed`; annotate `Generalized triples`
- [ ] 1.4 `Term.Basic`, `Triple.Basic`, `Graph.Basic`, `Dataset.Basic` with decidability and `Basic_union`; annotate `RDF 1.2 Basic`
- [ ] 1.5 `LeanRDF/Core/Iso.lean`: isomorphism through triple terms; annotate `Blank node isomorphism`
- [ ] 1.6 `LeanRDF/Core/Vocab.lean`: `rdf.reifies`, `rdf.dirLangString`, `rdfs.Proposition` with doc comments citing RDF 1.2 Semantics §8, §9; annotate `Vocabulary constants`
- [ ] 1.7 Check run time of the W3C suites before and after the recursive `Term`; hand-write `Ord` if needed

## 2. Simple interpretations

- [ ] 2.1 `LeanRDF/Semantics/Interpretation.lean`: `IT`, `IT_inj`, `IT_IR`; `denote` on triple terms; annotate `Simple interpretations`
- [ ] 2.2 Re-prove `Derives.sound`, `Derives.sound_graph`, the RDFS core lifts and the checker soundness with the new cases; `#print axioms` unchanged
- [ ] 2.3 `Free D` triple-term extension for the vacuity models in `Tests/Semantics`; port every existing countermodel; add the "triple term is not asserted" countermodel

## 3. N-Triples and N-Quads 1.2

- [ ] 3.1 `LeanRDF/Parse/NTriples/Parser.lean`: `tripleTerm` (object only, recursive), `LANG_DIR`, `versionDirective`; annotate `Document parsing` and `Term syntax`
- [ ] 3.2 `LeanRDF/Parse/NTriples/Serializer.lean`: canonical 1.2 triple terms and directions in `Term.toNTriples` and `Graph.toNTriples`; annotate `Canonical serialization`
- [ ] 3.3 `LeanRDF/Parse/NQuads/*`: 1.2 terms, graph label still IRI or blank node; annotate `N-Quads`
- [ ] 3.4 `LeanRDF/Cert/Json.lean`: terms read and written through the 1.2 term syntax; annotate `Certificate format`
- [ ] 3.5 Vendor `rdf/rdf12/rdf-n-triples` and `rdf/rdf12/rdf-n-quads` (syntax, `c14n`) from `w3c/rdf-tests` at a pinned commit into `Tests/data/rdf12-n-triples/` and `Tests/data/rdf12-n-quads/` with their licence and README; do not follow the `mf:include` of `../../rdf11/…`, because the RDF 1.1 suites stay where they are; teach `scripts/w3c-index.py` sub-manifests and the canonicalization test types

## 4. Downstream packages

- [ ] 4.1 `elpi/`: `rdf.tt` and `rdf.dirlang` in `saturate.elpi`, encoder and decoder; annotate `Term encoding`
- [ ] 4.2 `sparql/`: binding and comparison of triple terms, term tests and accessors; annotate `Triple terms in evaluation`; re-prove the evaluator correctness theorem
- [ ] 4.3 `sparql/`: JSON `triple`, XML `<triple>`, TSV/CSV `<<( … )>>`, `its:dir`, after checking these forms against the current SPARQL 1.2 Query Results drafts; annotate `Result formats`
- [ ] 4.4 `shacl/`: node kinds and literal components on triple terms; annotate `Triple terms in validation`; re-prove `results_nil`
- [ ] 4.5 `owl/`: new match arms only; `lake build` and `lake test` green
- [ ] 4.6 Oxilite results reader: `triple` bindings and `its:dir`; annotate `Results reading`

## 5. Tests

- [ ] 5.1 `Tests/Core`: the new and modified `rdf-core` scenarios, each with `@tg: verifies::`
- [ ] 5.2 `Tests/NTriples`: the new `ntriples` scenarios; `Tests/NTriples/W3C.lean` runs the 1.2 syntax and `c14n` manifests; annotate `W3C conformance` scenarios
- [ ] 5.3 `Tests/Datasets`: N-Quads scenarios and the 1.2 N-Quads suite; annotate `Dataset W3C conformance`
- [ ] 5.4 `Tests/Semantics`: `Triple terms denote through IT`, `Different triple terms can be told apart`, `A triple term is not asserted`
- [ ] 5.5 `Tests/Cert`: `RDF 1.2 terms in certificates`
- [ ] 5.6 `elpi/BridgeTests`, `sparql/SparqlTests`, `shacl/ShaclTests`, oxilite bridge tests: the new scenarios, each with `@tg: verifies::`

## 6. Docs and checks

- [ ] 6.1 Move the add-rdf12-core sections of `tg.md/rdf12.md` into `tg.md/decisions.md` with status accepted: supersede `Generalized triples inside` and `Literals are typed or language-tagged`; amend `Single-carrier interpretations`, `Small-model family for vacuity`, `Canonical N-Triples output`, `Recursive-descent N-Triples parser`, `Hand-written Elpi term encoding`
- [ ] 6.2 In `tg.md/constraints.md`, mark `Language tag iff langString`, `N-Triples grammar` and `N-Quads grammar` as RDF 1.1 history, pointing to the RDF 1.2 constraints that replace them
- [ ] 6.3 Mark `add-rdf12-core` archived in `tg.md/changes.md`; update the book chapters on the data model and syntax and the reference page
- [ ] 6.4 Builds and tests in all five packages; `tg check`, `tg ontology check` and `tg trace rdf-core ntriples datasets rdf-semantics elpi-bridge certificates sparql-algebra sparql-syntax shacl-core oxilite-bridge --gaps` show no new gaps
