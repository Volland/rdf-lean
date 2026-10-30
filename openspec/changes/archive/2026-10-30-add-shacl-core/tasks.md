## 1. Package and shapes

- [x] 1.1 `shacl/` package `leanrdf-shacl`
- [x] 1.2 `Shapes.lean` and `Read.lean`: the shape type and the reader with cycle detection; annotate `Shapes`

## 2. Semantics and validator

- [x] 2.1 `Path.lean`: `ValueNode` and the computed value nodes with `valueNodes_iff`
- [x] 2.2 `Semantics.lean`: `Conforms` per component; annotate `SHACL Core semantics`
- [x] 2.3 `Validate.lean`, `Report.lean`, `Correct.lean`: the validator, the Turtle report, `validate_conforms`, `validate_sound`; annotate `Proven validator`

## 3. Conformance and CLI

- [x] 3.1 Vendor the W3C SHACL Core tests with their licence; `ShaclTests/W3C.lean`, run compiled by the `shaclW3C` test driver, and `skip.txt`; annotate `SHACL W3C conformance`
- [x] 3.2 `ShaclMain.lean` and `lean_exe leanrdf-shacl`; record oxilite results for the samples; the comparison test; annotate `SHACL command line and oxilite comparison`
- [x] 3.3 Scenario tests with `@tg: verifies::`, `#print axioms` guards

## 4. Docs and checks

- [x] 4.1 Decisions on non-recursive shapes, paths and the validator theorems; constraint `SHACL Core`; add `shacl-core` to the `openspec:` frontmatter; mark the change; CI for the package; a book chapter and reference entry
- [x] 4.2 Builds and tests in all packages, `tg check`, `tg ontology check`, `tg trace shacl-core --gaps`
