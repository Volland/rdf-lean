Depends on `add-rdf12-core` being archived (`Term.triple`, `Literal.dirLang`, strict `WellFormed`, `rdf:reifies`, N-Triples/N-Quads 1.2).

## 1. Test data first

- [ ] 1.1 Vendor `rdf/rdf12/rdf-turtle/{syntax,eval}` and `rdf/rdf12/rdf-trig/{syntax,eval}` (whatever sub-manifests the pinned `w3c/rdf-tests` commit has) into `Tests/data/rdf12-turtle/` and `Tests/data/rdf12-trig/`, with `LICENSE.md` and a README naming the commit, the draft dates and `mf:assumedTestBase`; do not follow `mf:include` of the RDF 1.1 suites
- [ ] 1.2 Extend `scripts/w3c-index.py` for sub-manifests and any new `rdft:` test types; generate one `index.txt` per sub-directory; record the test counts in the READMEs
- [ ] 1.3 Make the test isomorphisms (`Tests/Turtle/Iso.lean`, `Tests/Datasets/Iso.lean`) map blank nodes inside triple terms

## 2. Lexical and directive layer

- [ ] 2.1 `LANG_DIR` in `rdfLiteral`: optional `--` direction after the tag, built with the Core directional smart constructor; unknown directions are a `ParseError`
- [ ] 2.2 `@version` (case-sensitive, string then `.`) and `VERSION` (case-insensitive, no `.`) in `directive`; single- and double-quoted short strings only; label discarded; annotate `Version directives`

## 3. Triple terms, reified triples, annotations

- [ ] 3.1 `tripleTerm` with `ttSubject`/`ttObject`, `<<(` matched before `<<` and `<`; annotate `@tg: implements:: [[openspec:turtle#Triple terms in Turtle]]`
- [ ] 3.2 `reifiedTriple` with `rtSubject`/`rtObject`/`reifier`, in `object` and as a `triples` subject; emits `r rdf:reifies <<( s p o )>>` and returns `r`; annotate `Reified triples`
- [ ] 3.3 `annotation` after each object in `objectList`: reifiers and blocks per §7.3.1, §7.3.3, §7.3.4; annotate `Annotations`
- [ ] 3.4 `renameFresh` and the document-label scan recurse into triple terms; annotate `Blank nodes`
- [ ] 3.5 Update the doc comments of `Turtle/Parser.lean` and `TriG/Parser.lean` to RDF 1.2 Turtle §6.5/§7 and RDF 1.2 TriG §5/§6; keep `@tg: implements::` for `Turtle parsing` and `TriG`

## 4. Tests

- [ ] 4.1 `Tests/Turtle/Parse.lean`: the new scenarios of `Turtle parsing` and `Blank nodes`, each with `@tg: verifies:: [[openspec:turtle#<Requirement>#<Scenario>]]` above it
- [ ] 4.2 `Tests/Turtle/Rdf12.lean`: every scenario of `Triple terms in Turtle`, `Reified triples`, `Annotations` and `Version directives`, each with its `@tg: verifies::` line
- [ ] 4.3 `Tests/Turtle/W3C.lean`: run the RDF 1.2 indexes; annotate the three scenarios of `RDF 1.2 Turtle conformance`; the RDF 1.1 run is unchanged
- [ ] 4.4 `Tests/Datasets/TriG.lean`: `Reification inside a graph block` and `Version directive only at the top level`; `Tests/Datasets/W3C.lean`: `The whole RDF 1.2 TriG suite`; each with its `@tg: verifies::` line
- [ ] 4.5 Any test that cannot pass gets a `simplifications.md` section (`deviates_from::` the constraint it breaks) and an explicit skip list entry naming that section; target: none

## 5. Docs and checks

- [ ] 5.1 `tg.md/constraints.md`: add `Turtle 1.2 grammar`, `Turtle 1.2 reification mapping` and `TriG 1.2 grammar` with `source::` lines (draft dates) and `constrains::` edges to the decisions below, `{strength: must}`
- [ ] 5.2 `tg.md/decisions.md`: add `Reification as sugar in the statement parser`, `Triple terms parsed by restricted productions`, `Version announcements are hints` and `Generated reifiers share the genid scheme`, each with `motivated_by::` edges as in design.md; add the change to [[decisions#TriG on the Turtle statement parser]]'s consequences
- [ ] 5.3 `tg.md/changes.md`: mark `add-rdf12-syntax`; confirm `turtle` and `datasets` are in the `openspec:` frontmatter of `decisions.md`
- [ ] 5.4 Update the purposes of `openspec/specs/turtle/spec.md` and `datasets` on archive (RDF 1.2), the book chapter on syntax and the site reference page with a reified-triple and an annotation example
- [ ] 5.5 `lake build`, `lake test` in the core package and in `elpi/`, `sparql/`, `shacl/`, `owl/` (they read Turtle fixtures)
- [ ] 5.6 `tg check`, `tg ontology check` and `tg trace turtle datasets --gaps` show no new gaps
