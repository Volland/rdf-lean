## 1. Rename

- [x] 1.1 `tm.validFromMs`, `tm.validToMs` in `Model.lean`; proofs and tests build
- [x] 1.2 Re-record goldens, examples and the docs that show the predicates; drop "pending tm cross-check"

## 2. tiramemsu cross-check

- [x] 2.1 `scripts/statements-tm-record.sh TM`: record `tm export --format sg-nt12` from tiramemsu's sg fixtures into `statements/StatementsTests/data/tm/` with an index of views
- [x] 2.2 Test: each recorded file decodes in its view and re-exports byte for byte; annotate `Statement graph test corpus#tiramemsu exports round-trip`

## 3. Release v0.3.1

- [x] 3.1 Versions 0.3.1, `check_release.py`, release notes `docs/releases/v0.3.1.md`
- [x] 3.2 tg.md: update the two decisions; `tg check`, `tg ontology check`, `tg trace statement-graphs release --gaps`
- [x] 3.3 Archive, commit, push, CI green, tag `v0.3.1`, GitHub release
