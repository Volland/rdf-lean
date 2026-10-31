## Why

After [[changes#add-rdf12-core]] and [[changes#add-rdf12-syntax]], LeanRDF reads and writes RDF 1.2 and gives triple terms a referent through `IT`. But its RDF and RDFS layers still follow RDF 1.1. `rdf:dirLangString` is not recognized, `rdf:reifies` has no axioms, and nothing makes a triple term a `rdfs:Proposition`. RDFS entailment over RDF 1.2 data is therefore weaker than the specification's. This change brings the RDF and RDFS layers of RDF 1.2 Semantics into LeanRDF, proves the new entailment patterns sound, and runs the W3C RDF 1.2 semantics suite. With it RDF 1.2 is complete, and it ships as v0.2.0.

## What Changes

- D-interpretations recognize `rdf:dirLangString`. A directional language-tagged string denotes the triple of its lexical form, lowercased tag and base direction, through a new abstract injective value field `dirLangVal` (RDF 1.2 Semantics §7.1). D becomes `{xsd:string, rdf:langString, rdf:dirLangString}`.
- RDF interpretations (§8):
  - `rdf:reifies` joins the RDF vocabulary, with the axiom `rdf:reifies rdf:type rdf:Property`.
  - A value-space condition for `rdf:dirLangString` is added.
  - The three datatypes are recognized.
- RDFS interpretations (§9):
  - `ICEXT(I(rdf:dirLangString))` is the set of values of directional language-tagged strings.
  - Every value of `IT` on `IR × IP × IR` is in `ICEXT(I(rdfs:Proposition))`.
  - New axioms: `rdf:reifies rdfs:domain rdfs:Resource`, `rdf:reifies rdfs:range rdfs:Proposition`, `rdfs:Proposition rdfs:subClassOf rdfs:Resource`, and the rdfs1 triple for `rdf:dirLangString`.
- `RDFSCore` gains the conditions the new rules use.
- Rule patterns gain a triple-term position, `Pat.triple`, so a rule can match inside a triple term and build one in its head. The checker's matcher and the Elpi clause generator follow.
- New sound rules:
  - `Grdfs14-s`, `Grdfs14-p`, `Grdfs14-o`: a triple term in a derived triple is a `rdfs:Proposition`.
  - `Grdfs14-in-s`, `Grdfs14-in-p`, `Grdfs14-in-o`: a triple term inside a proposition is one.
  - `rdfs14a`: a ground witness proposition.
  - `GrdfD1-dirLangString`, with a new guard `dirLangLiteral`.
  - The five new axiomatic triples, as rules.
  - The existential forms rdfs14 and rdfs14a are answered by graph queries with instance mappings, as rdfD1 is today.
- Regime rule sets: `simpleRules` (no rules) and `rdfRules` (rdfD2, GrdfD1, the RDF axioms), with soundness theorems for simple and RDF entailment. They are needed to prove positive tests of those regimes.
- The W3C RDF 1.2 `rdf-semantics` suite is vendored and run in `leanrdf-elpi`:
  - A positive test passes when its certificate is accepted under its regime's rules.
  - A negative test passes when its conclusion is not derived. Tests on triple-term behaviour also get a kernel countermodel.
  - `RDFS-Plus` tests and tests that need XSD value reasoning are listed, with reasons, as not run.
- Release v0.2.0:
  - The version is bumped and the package description becomes "Native RDF 1.2 model…".
  - The site roadmap is updated.
  - A runnable example of reified triples is added.
  - Release notes are written.

## Capabilities

### New Capabilities

None.

### Modified Capabilities

- `rdf-semantics`: D-, RDF and RDFS interpretations and the entailment relations become RDF 1.2. Vacuity evidence covers propositions. New requirement `RDF 1.2 semantics conformance`.
- `rdfs-entailment`: the rule format gains triple-term patterns, the rule set and guards grow, and there are new requirements `Proposition rules` and `Regime rule sets`.
- `certificates`: checker soundness gains the simple and RDF regimes.
- `elpi-bridge`: rule clauses cover triple-term patterns and the `dirLangLiteral` guard.

## Impact

**Roadmap:** third of four changes, add-rdf12-core → add-rdf12-syntax → **add-rdf12-semantics** (v0.2.0) → [[changes#add-statement-graphs]] (v0.3.0). It depends on [[changes#add-rdf12-syntax]] being archived, because the W3C semantics suite is written in Turtle 1.2.

**Code:**
- core: `LeanRDF/Semantics/{Interpretation,RDFS,Axioms,Entails}.lean`, `LeanRDF/Entailment/{Rule,Rules,Soundness}.lean`, `LeanRDF/Cert/{Match,Check}.lean`, `LeanRDF/Core/Vocab.lean` (only if a name is missing)
- elpi: `elpi/LeanRDFElpi/Codegen.lean`, `elpi/BridgeTests/Rdf12Semantics.lean`, `elpi/BridgeTests/data/rdf12-semantics/`
- tests: `Tests/Semantics/{SmallModel,Vacuity,HandProofs}.lean`, `Tests/Entailment/*.lean`, `Tests/Cert/*.lean`
- release: `lakefile.lean`, the `*/lakefile.lean` versions, `site/content/roadmap.md`, `site/assets/roadmap.svg`, `examples/`, `README.md`, `CHANGELOG`

**tg.md sections touched:**
- decisions amended: [[decisions#Layered interpretations with a core]], [[decisions#Readings of the condition tables]], [[decisions#Small-model family for vacuity]], [[decisions#Horn rules matched by the checker]], [[decisions#Rules generated from Lean]], [[decisions#Graph queries with instance mappings]], [[decisions#Semantics tested against vacuity]]
- simplification amended: [[simplifications#Two recognized datatypes with abstract values]], now three recognized datatypes

**Constraints binding the area:**
- [[constraints#RDF interpretations recognize two datatypes]] (replaced by its RDF 1.2 version)
- [[constraints#RDFS interpretation conditions]]
- [[constraints#Entailment rules use generalized RDF]]
- [[constraints#Entailed blank nodes are existential]]
- `Triple-term denotation`, from add-rdf12-core
- new: `RDF 1.2 RDF interpretations`, `RDF 1.2 RDFS conditions`, `RDF 1.2 entailment patterns`, `RDF 1.2 semantics test suite`

**Requirements:**
- modified: [[openspec:rdf-semantics#D-interpretations]], [[openspec:rdf-semantics#RDF interpretations]], [[openspec:rdf-semantics#RDFS interpretations]], [[openspec:rdf-semantics#Entailment relations]], [[openspec:rdf-semantics#Semantics is not vacuous]], [[openspec:rdfs-entailment#Rule format]], [[openspec:rdfs-entailment#RDFS rule set]], [[openspec:rdfs-entailment#Guards]], [[openspec:certificates#Checker soundness]], [[openspec:elpi-bridge#Rule clauses]]
- added: `rdf-semantics#RDF 1.2 semantics conformance`, `rdfs-entailment#Proposition rules`, `rdfs-entailment#Regime rule sets`
