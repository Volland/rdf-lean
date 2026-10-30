## 1. Model

- [ ] 1.1 `LeanRDF/Core/Dataset.lean`: `Quad`, `Dataset` and the membership lemmas; annotate `Datasets`

## 2. Parsers

- [ ] 2.1 `LeanRDF/Parse/NQuads/{Parser,Serializer}.lean`; annotate `N-Quads`
- [ ] 2.2 Graph name in the Turtle parser state; `LeanRDF/Parse/TriG/Parser.lean`; annotate `TriG`

## 3. Test data and tests

- [ ] 3.1 Vendor `rdf-n-quads` and `rdf-trig` (commit `d01b141`) with their licence; extend `scripts/w3c-index.py`
- [ ] 3.2 `Tests/Datasets/{Model,NQuads,TriG}.lean`: the scenarios, with `@tg: verifies::` annotations
- [ ] 3.3 `Tests/Datasets/W3C.lean`: both suites, dataset isomorphism for evaluation tests; annotate `Dataset W3C conformance`

## 4. Docs and checks

- [ ] 4.1 Supersede `No datasets in v0.x` with a dataset decision; add constraints `N-Quads grammar` and `TriG grammar`; add `datasets` to the `openspec:` frontmatter; mark the change in `tg.md/changes.md`; update the book chapter on syntax and the reference page
- [ ] 4.2 Builds and tests in both packages, `tg check`, `tg ontology check`, `tg trace datasets --gaps`
