## 1. Reading oxilite

- [ ] 1.1 `Oxilite/Results.lean`: SPARQL results JSON to solutions; annotate `Results reading`
- [ ] 1.2 `Oxilite/Pattern.lean`: `patternQuery`, `instantiate`; annotate `Query patterns`
- [ ] 1.3 `Oxilite/Why.lean`: the `why` tree type and its JSON reader

## 2. Certifying

- [ ] 2.1 Mode `elpi`: one saturation, one certificate per answer; annotate `Certification by Elpi`
- [ ] 2.2 `Oxilite/Translate.lean`: tree to certificate with rule matching and the name map; annotate `Certification of why trees`
- [ ] 2.3 `Oxilite/Run.lean` and `OxiliteMain.lean`: processes, MCP calls, recorded inputs, verdicts and exit codes; `lean_exe leanrdf-oxilite`; annotate `Oxilite runner`

## 3. Fixtures and tests

- [ ] 3.1 `scripts/oxilite-fixtures.sh` and the recorded outputs in `elpi/BridgeTests/data/oxilite/` (pets, subclass, chain, domain, range, subproperty)
- [ ] 3.2 `BridgeTests/Oxilite.lean`: every scenario with `@tg: verifies::`, including the tampered answer and the tampered tree; annotate `oxilite reasoning scenarios`
- [ ] 3.3 Run the runner against a real oxilite build once and record the output in the change notes

## 4. Docs and checks

- [ ] 4.1 Decision on the two modes and constraints `oxilite why trees` and `SPARQL results JSON`; add `oxilite-bridge` to the `openspec:` frontmatter; mark the change in `tg.md/changes.md`; an examples entry and a book note in the Elpi chapter
- [ ] 4.2 Builds and tests in both packages, `tg check`, `tg ontology check`, `tg trace oxilite-bridge --gaps`
