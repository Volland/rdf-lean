## 0. Preconditions

- [ ] 0.1 Confirm that [[changes#add-rdf12-syntax]] is archived and that `denote` gives a triple term a referent only on `IT`'s domain, as add-rdf12-core specifies (constraint `Triple-term denotation`).

## 1. Interpretations

- [ ] 1.1 `LeanRDF/Semantics/Interpretation.lean`: `DInterp.dirLangVal`, `dirLangVal_inj`, `IL_dirLang` (§7.1). Update the doc comment and annotate `@tg: implements:: [[openspec:rdf-semantics#D-interpretations]]`.
- [ ] 1.2 `LeanRDF/Semantics/Axioms.lean`: `rdf:reifies rdf:type rdf:Property` in `rdfAxioms`; `rdf:reifies rdfs:domain rdfs:Resource`, `rdf:reifies rdfs:range rdfs:Proposition` and `rdfs:Proposition rdfs:subClassOf rdfs:Resource` in `rdfsAxioms`; `rdf:dirLangString rdf:type rdfs:Datatype` in `datatypeAxioms`. Cite RDF 1.2 Semantics §8 and §9.
- [ ] 1.3 `LeanRDF/Semantics/RDFS.lean`: `RDFConditions.dirLangString_class`, and `RDFSConditions.dirLangString_ext` and `proposition`. Extend `datatypes`. Annotate `RDF interpretations` and `RDFS interpretations`.
- [ ] 1.4 `RDFSCore`: add `dirLang_lit` and `proposition`, and extend `DInterp.IsRDFS.toCore`. Add `RDFCore` and `DInterp.IsRDF.toRDFCore`.
- [ ] 1.5 `LeanRDF/Semantics/Entails.lean`: doc comments for the three recognized datatypes. Annotate `Entailment relations`.

## 2. Rule format and checker

- [ ] 2.1 `LeanRDF/Entailment/Rule.lean`: `Pat.triple`, with `Pat.apply` and `Pat.vars` recursing into it. Update `RangeRestricted` and its decidability. Annotate `@tg: implements:: [[openspec:rdfs-entailment#Rule format]]`.
- [ ] 2.2 `Guard.dirLangLiteral` with `Holds`, `check` and the `check_sound` case. Annotate `Guards`.
- [ ] 2.3 `LeanRDF/Cert/Match.lean`: `matchPat` on `Pat.triple`, and `matchPat_spec` and `Fits` by induction on the pattern. `check_sound` keeps its statement.

## 3. Rules and soundness

- [ ] 3.1 `LeanRDF/Entailment/Rules.lean`: `grdfD1DirLang`, `Grdfs14-{s,p,o}`, `Grdfs14-in-{s,p,o}` and `rdfs14a` in `rdfsExtraRules`, in the spec's order. Annotate `@tg: implements:: [[openspec:rdfs-entailment#Proposition rules]]`.
- [ ] 3.2 `LeanRDF/Entailment/Soundness.lean`: soundness cases for each new rule from `RDFSCore`. `rdfsRules_sound` is total again. Annotate `RDFS rule set`.
- [ ] 3.3 `simpleRules`, `rdfRules`, `Derives.sound_graph_simple` (from the interpolation lemma) and `Derives.sound_graph_rdf` (from `RDFCore`). Annotate `@tg: implements:: [[openspec:rdfs-entailment#Regime rule sets]]`.
- [ ] 3.4 `LeanRDF/Cert/Check.lean`: `checkQuery_sound_simple` and `checkQuery_sound_rdf`. Annotate `@tg: implements:: [[openspec:certificates#Checker soundness]]`.

## 4. Elpi bridge

- [ ] 4.1 `elpi/LeanRDFElpi/Codegen.lean`: `patSrc` for `Pat.triple`, using the Elpi triple-term constructor of add-rdf12-core, and `guardSrc` for `dirLangLiteral`. Annotate `Rule clauses`.
- [ ] 4.2 Check that saturation terminates on nested triple terms. Rule heads reuse body subterms, so the closure is bounded by the input's subterms, the axioms and the `rdfs14a` witness.

## 5. Tests

- [ ] 5.1 `Tests/Entailment/*.lean`: the scenarios of `Rule format`, `RDFS rule set` (53 axiom rules, 80 rules), `Guards`, `Proposition rules` and `Regime rule sets`. Put `@tg: verifies:: [[openspec:rdfs-entailment#<Requirement>#<Scenario>]]` above each test.
- [ ] 5.2 `Tests/Cert/*.lean`: the proposition certificate and the regime certificates. Axiom checks cover `checkQuery_sound_simple` and `checkQuery_sound_rdf`. Annotate `Checker soundness` scenarios.
- [ ] 5.3 `Tests/Semantics/Basics.lean`: the `D-interpretations`, `RDF interpretations`, `RDFS interpretations` and `Entailment relations` scenarios, with `@tg: verifies::` annotations.
- [ ] 5.4 `Tests/Semantics/SmallModel.lean`:
  - add `rdfs:Proposition` to `universalClasses`;
  - give `rdf:dirLangString` an exact extension;
  - discharge the new condition fields.
- [ ] 5.5 `Tests/Semantics/{Vacuity,HandProofs}.lean`:
  - a model with a reifier;
  - a countermodel for "a triple term is not asserted";
  - hand proofs of rdfs14 and the `rdf:reifies` axioms;
  - annotate the `Semantics is not vacuous` scenarios.
- [ ] 5.6 `elpi/BridgeTests/*.lean`: the `Proposition rules run in Elpi` scenario, annotated.
- [ ] 5.7 Vendor `rdf/rdf12/rdf-semantics` from w3c/rdf-tests at a pinned commit, with its licence, into `elpi/BridgeTests/data/rdf12-semantics/`, and extend `scripts/w3c-index.py` to read `mf:entailmentRegime`.
- [ ] 5.8 `elpi/BridgeTests/Rdf12Semantics.lean`: the runner by regime, the expected-not-run file with reasons, and kernel countermodels referenced for the listed negative tests. Annotate `@tg: verifies::` for `RDF 1.2 semantics conformance` and its scenarios.
- [ ] 5.9 `#print axioms` checks for the new soundness theorems in `Tests/Cert/Axioms.lean`.

## 6. Docs (tg.md and book)

- [ ] 6.1 Record the design's decisions in `tg.md/decisions.md` as typed sections with edges, using only edge names from `tg ontology`:
  - `Three recognized datatypes with abstract values`;
  - `Propositions are the image of IT on its domain`;
  - `Triple-term patterns in rules`;
  - `rdfs14 as generalized Horn rules plus graph queries`;
  - `Regime rule sets for simple and RDF entailment`;
  - `The W3C semantics suite in the bridge package`;
  - `Vacuity with propositions`.

  Each gets `- motivated_by::` and `- amends::` edges as in design.md.
- [ ] 6.2 Add the constraints `RDF 1.2 RDF interpretations`, `RDF 1.2 RDFS conditions`, `RDF 1.2 entailment patterns` and `RDF 1.2 semantics test suite` to `tg.md/constraints.md`, each with `- source::` and `- constrains:: [[openspec:<capability>#<Requirement>]] {strength: must}` or a decision target. Move the source of `RDFS interpretation conditions` to RDF 1.2 Semantics §9, and retire `RDF interpretations recognize two datatypes` in favour of the RDF 1.2 version.
- [ ] 6.3 `tg.md/simplifications.md`: rename and extend `Two recognized datatypes with abstract values` to three datatypes, and add `Datatype rules see asserted positions only` with `- deviates_from::`.
- [ ] 6.4 Mark `add-rdf12-semantics` in `tg.md/changes.md`, and check that `rdf-semantics`, `rdfs-entailment`, `certificates` and `elpi-bridge` are in `tg.md/decisions.md`'s `openspec:` frontmatter.
- [ ] 6.5 Update the book chapter on semantics and entailment: propositions, rdfs14 by instance mapping, and regimes.

## 7. Release v0.2.0

- [ ] 7.1 Bump `version` to `0.2.0` in `lakefile.lean` and in the `elpi`, `sparql`, `owl` and `shacl` lakefiles, and change the description to "Native RDF 1.2 model with formal entailment semantics and a verified certificate checker." Update the `Package metadata` test.
- [ ] 7.2 `site/content/roadmap.md` and `site/assets/roadmap.svg`: RDF 1.2 done, statement graphs next.
- [ ] 7.3 `examples/`: a runnable example of reified triples (Turtle 1.2 with `~` and `{| |}`), saturated and certified, with its recorded output via `scripts/examples-record.sh`.
- [ ] 7.4 Release notes for v0.2.0 covering the three RDF 1.2 changes and the breaking Lean API changes, plus a README update.

## 8. Checks

- [ ] 8.1 `lake build` and `lake test` in the root, `elpi`, `sparql`, `owl` and `shacl` packages; no `sorry`; the axiom checks pass.
- [ ] 8.2 `openspec validate add-rdf12-semantics`.
- [ ] 8.3 `tg check`, `tg ontology check` and `tg trace rdf-semantics rdfs-entailment certificates elpi-bridge --gaps` show no new gaps.
