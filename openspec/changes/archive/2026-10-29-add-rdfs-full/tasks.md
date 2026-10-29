## 1. Rules and semantics

- [x] 1.1 `Guard` constructors, `Guard.Holds`, `Guard.check`, `containerIndex?`, `Guard.check_sound`; annotate `Guards`
- [x] 1.2 New rules, `axiomRule`, `axiomRules`, `rdfsBasicRules`, `rdfsExtraRules`, `rdfsRules`
- [x] 1.3 `datatypeAxioms`; `RDFSCore` fields; `DInterp.IsRDFS.toCore`
- [x] 1.4 Soundness of every new rule, `axiomRules_sound`, `rdfsRules_sound`

## 2. Checker and bridge

- [x] 2.1 Guards in `checkNode` and its soundness proof
- [x] 2.2 Guard goals and `rdf.axiom` facts in `stepClauses`; `rdf.axiom` and `rdf.is-cmp` in the driver; `containerIRIs` asserted in `saturateWith`

## 3. Tests

- [x] 3.1 `Tests/Entailment/Rules.lean`: the full rule set; `Tests/Entailment/FullRules.lean`: guards and a certificate over the new rules
- [x] 3.2 `elpi/BridgeTests/FullRules.lean`: full-rule saturation; golden closures on `rdfsBasicRules`

## 4. Docs and checks

- [x] 4.1 Update the container simplification and the core decision in `tg.md/`
- [x] 4.2 Mark `add-rdfs-full` applied in `tg.md/changes.md`
- [x] 4.3 Run builds, tests, `tg check`, `tg ontology check`, `tg trace rdfs-entailment elpi-bridge certificates --gaps`
