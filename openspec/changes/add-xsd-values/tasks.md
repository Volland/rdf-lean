## 1. Values

- [ ] 1.1 `LeanRDF/Xsd/Value.lean`: `XsdValue`, derived integer ranges, `Literal.value?`; annotate `Lexical-to-value mapping`
- [ ] 1.2 `LeanRDF/Xsd/Lexical.lean`: lexical parsers and canonical forms with the round-trip theorems; annotate `Canonical forms`
- [ ] 1.3 `LeanRDF/Xsd/Compare.lean`: `compare?` with promotion and the agreement theorems; annotate `Value comparison`
- [ ] 1.4 `LeanRDF/Xsd/DateTime.lean`: parsing, normalization and comparison; annotate `dateTime comparison`

## 2. Tests

- [ ] 2.1 `Tests/Xsd/*.lean`: every scenario with `@tg: verifies::`, plus `#print axioms` guards on the theorems

## 3. Docs and checks

- [ ] 3.1 Record the value decisions and constraints `XSD datatypes` and `SPARQL operator mapping`; add `xsd-values` to the `openspec:` frontmatter; mark the change in `tg.md/changes.md`; add the module to the reference page
- [ ] 3.2 Builds and tests, `tg check`, `tg ontology check`, `tg trace xsd-values --gaps`
