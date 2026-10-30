## 1. Package and semantics

- [ ] 1.1 `owl/` package `leanrdf-owl`; `Vocab.lean` with the OWL vocabulary
- [ ] 1.2 `Semantics.lean`: `OWLConditions`, `IsOWL`, `OWLEntails`, the sameAs lemma; annotate `OWL conditions`

## 2. Rules and proofs

- [ ] 2.1 `Rules.lean`: `owlRLRules`, `owlRules`; annotate `OWL 2 RL rules`
- [ ] 2.2 `Soundness.lean`: one proof per rule, `owlRules_sound`, `Derives.owl_sound`; annotate `OWL soundness`
- [ ] 2.3 `Vacuity.lean`: the finite model and the two countermodels; annotate `OWL non-vacuity`

## 3. Bridge

- [ ] 3.1 `leanrdf-elpi` requires `leanrdf-owl`; profiles in the oxilite bridge; the OWL name map; annotate `OWL profile`
- [ ] 3.2 `--materialized`: run or read inferences, certify each; annotate `Materialized inferences`
- [ ] 3.3 Record fixtures from the local oxilite (an OWL sample ontology, why trees with OWL templates, materialized inferences)

## 4. Tests

- [ ] 4.1 `OwlTests/*.lean` and `BridgeTests/OxiliteOwl.lean`: every scenario with `@tg: verifies::`, `#print axioms` guards

## 5. Docs and checks

- [ ] 5.1 Decisions on the condition subset and the rule set; constraints `OWL 2 RDF-Based Semantics` and `OWL 2 RL rules`; the excluded rules in `tg.md/simplifications.md`; add `owl-rl` to the `openspec:` frontmatter; mark the change; CI for the new package; a book chapter on OWL 2 RL and a reference entry
- [ ] 5.2 Builds and tests in all packages, `tg check`, `tg ontology check`, `tg trace owl-rl oxilite-bridge --gaps`
