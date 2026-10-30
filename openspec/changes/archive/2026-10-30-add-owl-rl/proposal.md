## Why

oxilite materializes OWL 2 RL inferences, and its `why` trees use OWL 2 RL templates (`cax-eqc`, `prp-inv`, `prp-trp`, `eq-rep-s`, …) that `add-oxilite-certify` cannot yet translate. Phase P4 extends LeanRDF's proven rules from RDFS to the fixed-arity OWL 2 RL rules, so oxilite's OWL answers and materialized inferences can be certified too.

## What Changes

- New Lake package `leanrdf-owl` in `owl/`, requiring `leanrdf`.
- The OWL 2 RDF-Based Semantics conditions that the rules need, as an extension of RDFS interpretations (`IsOWL`), with `OWLEntails`.
- The OWL 2 RL/RDF rules of OWL 2 Profiles §4.3 with a fixed number of premises, as `Rule` values: the equality rules, the property rules, the class rules, `cax-sco` and `cax-eqc`, and the schema rules. Each rule is proven sound.
- Evidence of non-vacuity: an OWL interpretation that satisfies a nontrivial graph, and two non-entailments with countermodels.
- `leanrdf-elpi` requires `leanrdf-owl`. The oxilite bridge gains an `owl` profile: `why` trees with OWL templates translate to the new rules, and `leanrdf-oxilite --materialized` certifies each inference that `oxilite materialize` stores.

## Capabilities

### New Capabilities

- `owl-rl`: OWL 2 RDF-Based conditions, the OWL 2 RL rules and their soundness.

### Modified Capabilities

- `oxilite-bridge`: an `owl` profile for why trees and certification of materialized inferences.

## Impact

**Roadmap:** P4. Depends on `add-oxilite-certify`.

**Code:** `owl/lakefile.lean`, `owl/LeanRDFOwl/{Vocab,Semantics,Rules,Soundness}.lean`, `owl/OwlTests/*.lean`, `elpi/lakefile.lean`, `elpi/LeanRDFElpi/Oxilite/*.lean`, `elpi/BridgeTests/OxiliteOwl.lean` and fixtures.

**Motivating decisions** (tg.md): [[decisions#LeanRDF is the proof layer for oxilite]], [[decisions#Semantics tested against vacuity]], [[decisions#Layered interpretations with a core]], [[decisions#Layers as packages in one repository]].

**Not included:** the list rules (`prp-spo2`, `prp-key`, `cls-int*`, `cls-uni`, `cls-oo`, `cax-adc`, `eq-diff2/3`, `scm-int`, `scm-uni`), the rules that signal inconsistency, and the datatype rules. They are listed in [[simplifications]].
