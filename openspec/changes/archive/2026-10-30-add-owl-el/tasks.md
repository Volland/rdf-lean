## 1. Semantics

- [x] 1.1 `Lists.lean`: `ListOf`, the intersection condition in `OWLConds`; lemmas for two and three in `ELSoundness.lean`; annotate `Intersection condition`

## 2. Rules and proofs

- [x] 2.1 `EL.lean`: `elRules`, `owlELRules`; annotate `EL completion rules`
- [x] 2.2 `ELSoundness.lean`: per-rule proofs, `elRules_sound`, `Derives.el_sound`; annotate `EL soundness`

## 3. Classification

- [x] 3.1 `Classify.lean`, `ClassifyMain.lean`, `lean_exe leanrdf-classify`; `examples/el-ontology.ttl` with its hand-computed hierarchy; annotate `Certified classification`

## 4. Tests

- [x] 4.1 `OwlTests/EL*.lean` and `BridgeTests/Classify.lean`: every scenario with `@tg: verifies::`, `#print axioms` guards

## 5. Docs and checks

- [x] 5.1 Decisions on lists by length and the completion rules; constraint `OWL 2 EL profile`; add `owl-el` to the `openspec:` frontmatter; mark the change; book and reference entries; update the roadmap page
- [x] 5.2 Builds and tests in all packages, `tg check`, `tg ontology check`, `tg trace owl-el --gaps`
