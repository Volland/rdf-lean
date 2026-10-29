## 1. Demo

- [x] 1.1 `elpi/LeanRDFElpi/Demo.lean`: `Args`, `parseArgs`, `verdict`, `run`; annotate `Demo command` and `Exit codes and verdicts`
- [x] 1.2 `elpi/DemoMain.lean` and the `leanrdf-demo` executable
- [x] 1.3 `elpi/examples/`: `pets.nt` and three queries

## 2. Tests

- [x] 2.1 `elpi/BridgeTests/Demo.lean`: entailed, not derived, rejected and bad-input runs; outputs written

## 3. Docs and checks

- [x] 3.1 `README.md` with the demo; mark `add-demo` applied in `tg.md/changes.md`; add `demo` to the `openspec:` frontmatter
- [x] 3.2 Run builds and tests in both packages, the demo on every example, `tg check`, `tg ontology check`, `tg trace demo --gaps`
