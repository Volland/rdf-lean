## 1. Bridge

- [x] 1.1 `elpi/LeanRDFElpi/Encode.lean`: encoder, decoder and Elpi source text of terms; annotate `Term encoding`
- [x] 1.2 `elpi/LeanRDFElpi/Codegen.lean`: `stepClauses`; annotate `Rule clauses`
- [x] 1.3 `elpi/LeanRDFElpi/elpi/saturate.elpi`: semi-naive driver with string-keyed deduplication
- [x] 1.4 `elpi/LeanRDFElpi/Saturate.lean`: `program`, `saturate`, `Closure`, `find?`, `wellOrdered`; annotate `Saturation` and `Reflection`
- [x] 1.5 `elpi/lakefile.lean`: `input_dir` over the Elpi sources

## 2. Tests

- [x] 2.1 `elpi/BridgeTests/Encode.lean`: encoding and clause scenarios, annotated `@tg: verifies::`
- [x] 2.2 `elpi/BridgeTests/Saturate.lean`: golden closures, cycle, chain and reflection scenarios, annotated `@tg: verifies::`

## 3. Docs and checks

- [x] 3.1 Record the encoding decision and the lean-elpi constraints in `tg.md/`, add `elpi-bridge` to the `openspec:` frontmatter
- [x] 3.2 Mark `add-elpi-bridge` applied in `tg.md/changes.md`
- [x] 3.3 Run `lake build` and `lake test` in both packages, `tg check`, `tg ontology check`, `tg trace elpi-bridge --gaps`
