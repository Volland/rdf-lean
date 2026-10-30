## 1. Package and semantics

- [x] 1.1 `owl/` package `leanrdf-owl`; `Vocab.lean` with the OWL vocabulary
- [x] 1.2 `Semantics.lean`: `OWLConds`, `IsOWL`, `OWLEntails`, the sameAs lemma; annotate `OWL conditions`

## 2. Rules and proofs

- [x] 2.1 `Rules.lean`: `owlRLRules`, `owlRules`; annotate `OWL 2 RL rules`
- [x] 2.2 `Soundness.lean`: one proof per rule, `owlRules_sound`, `Derives.owl_sound`; annotate `OWL soundness`
- [x] 2.3 `OwlTests/Model.lean`: the model and the two countermodels; annotate `OWL non-vacuity`

## 3. Bridge

- [x] 3.1 `leanrdf-elpi` requires `leanrdf-owl`; profiles in the oxilite bridge; the OWL name map; annotate `OWL profile`
- [x] 3.2 `--materialized`: run or read inferences, certify each; annotate `Materialized inferences`
- [x] 3.3 Record fixtures from the local oxilite (an OWL sample ontology, why trees with OWL templates, materialized inferences)

## 4. Tests

- [x] 4.1 `OwlTests/*.lean` and `BridgeTests/OxiliteOwl.lean`: every scenario with `@tg: verifies::`, `#print axioms` guards

## 5. Docs and checks

- [x] 5.1 Decisions on the condition subset and the rule set; constraints `OWL 2 RDF-Based Semantics` and `OWL 2 RL rules`; the excluded rules in `tg.md/simplifications.md`; add `owl-rl` to the `openspec:` frontmatter; mark the change; CI for the new package; a book chapter on OWL 2 RL and a reference entry
- [x] 5.2 Builds and tests in all packages, `tg check`, `tg ontology check`, `tg trace owl-rl oxilite-bridge --gaps`
