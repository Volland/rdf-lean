## 1. Core

- [x] 1.1 `LeanRDF/Cert/Match.lean`: `PSubst`, `matchPat`, `matchTPat`, `matchBody` and their specs
- [x] 1.2 `LeanRDF/Cert/Check.lean`: `Node`, `Certificate`, `checkNode`, `checkNodes`, `checkCert`, `check`, `checkQuery`, soundness theorems, Boolean forms; annotate `Checker` and `Checker soundness`
- [x] 1.3 `LeanRDF/Cert/Json.lean`: JSON form and parser; annotate `Certificate format`
- [x] 1.4 `LeanRDF/Cert/Datalog.lean`: `toDatalog`; annotate `CertifyingDatalog export`
- [x] 1.5 `NTriples.parseTerm`

## 2. Bridge

- [x] 2.1 `elpi/LeanRDFElpi/Certify.lean`: `findMu`, `certify`, `entailmentCertificate`; annotate `Certificates from Elpi` and `End-to-end`

## 3. Tests

- [x] 3.1 `Tests/Cert/Check.lean`: accepted and tampered certificates, propositions by `native_decide`, JSON, export shape
- [x] 3.2 `Tests/Cert/Axioms.lean`: axioms of the soundness theorems
- [x] 3.3 `elpi/BridgeTests/EndToEnd.lean`: N-Triples to `RDFSEntails`, pruning, non-derived queries, tampering, JSON and export

## 4. Docs and checks

- [x] 4.1 Update the decisions on query mappings and certificates in `tg.md/decisions.md`; add `certificates` to the `openspec:` frontmatter
- [x] 4.2 Mark `add-certificates` applied in `tg.md/changes.md`
- [x] 4.3 Run `lake build` and `lake test` in both packages, `tg check`, `tg ontology check`, `tg trace certificates --gaps`
