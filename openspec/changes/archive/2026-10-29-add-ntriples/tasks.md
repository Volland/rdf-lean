## 1. Parser and serializer

- [x] 1.1 `LeanRDF/Parse/NTriples/Chars.lean`: character classes of the §7 terminals (`PN_CHARS_BASE`, `PN_CHARS_U`, `PN_CHARS`, IRIREF-forbidden, HEX), absolute-IRI, label and language-tag checks
- [x] 1.2 `LeanRDF/Parse/NTriples/Parser.lean`: `ParseError`, `NTriples.parseTriples`, `NTriples.parse`; annotate with `@tg: implements:: [[openspec:ntriples#Document parsing]]` and `@tg: implements:: [[openspec:ntriples#Term syntax]]`
- [x] 1.3 `LeanRDF/Parse/NTriples/Serializer.lean`: `Term.toNTriples`, `Graph.toNTriples`; annotate with `@tg: implements:: [[openspec:ntriples#Canonical serialization]]`
- [x] 1.4 Import the modules from `LeanRDF.lean`

## 2. Test data

- [x] 2.1 Copy the W3C `rdf/rdf11/rdf-n-triples` `.nt` files, `manifest.ttl` and the suite `LICENSE.md` (commit `d01b141`) to `Tests/data/rdf-n-triples/`, with a `README.md` naming the source and commit
- [x] 2.2 `scripts/w3c-ntriples-index.py`: generate `Tests/data/rdf-n-triples/index.txt` from the manifest
- [x] 2.3 `lakefile.lean`: an `input_dir` over `Tests/data` that the `Tests` library needs

## 3. Tests

- [x] 3.1 `Tests/NTriples/Parse.lean`: scenarios of `Document parsing` and `Term syntax`, each annotated `@tg: verifies::`
- [x] 3.2 `Tests/NTriples/Serialize.lean`: scenarios of `Canonical serialization`, annotated `@tg: verifies::`
- [x] 3.3 `Tests/NTriples/W3C.lean`: run the suite and the round-trip at build time; annotate the `W3C conformance` and `Round-trip stability` scenarios with `@tg: verifies::`

## 4. Docs and checks

- [x] 4.1 Record the constraints `N-Triples grammar` and `W3C tests reject colons in blank-node labels` in `tg.md/constraints.md`, and any decision found while implementing in `tg.md/decisions.md`; add `ntriples` to the `openspec:` frontmatter
- [x] 4.2 Mark `add-ntriples` as applied in `tg.md/changes.md`
- [x] 4.3 `grep -rn "sorry\|admit\|axiom \|native_decide" LeanRDF/` is empty
- [x] 4.4 Run `lake build`, `lake test` (both packages), `tg check`, `tg ontology check` and `tg trace ntriples --gaps`, and close every gap
