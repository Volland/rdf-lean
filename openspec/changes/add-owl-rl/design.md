## Context

The OWL 2 RDF-Based Semantics (W3C Recommendation, 2012) §5 extends D-interpretations with conditions on the OWL vocabulary. OWL 2 Profiles §4.3 lists the OWL 2 RL/RDF rules in Tables 4 to 9. LeanRDF's `Rule` is a Horn rule over triple patterns with guards; `Derives.sound` lifts per-rule soundness to derivations.

## Goals / Non-Goals

**Goals:** every included rule proven sound; the same certificate format and checker; non-vacuity evidence like M3's.

**Non-Goals:** completeness of OWL 2 RL; rules over lists; rules that conclude `false`; datatype reasoning; OWL 2 Direct Semantics.

## Decisions

### Only the conditions the rules need

`OWLConditions` transcribes the §5 conditions for `owl:Thing`, `owl:Nothing`, `owl:sameAs`, `owl:equivalentClass`, `owl:equivalentProperty`, `owl:inverseOf`, the property characteristics (functional, inverse functional, symmetric, transitive), `owl:someValuesFrom`, `owl:allValuesFrom`, `owl:hasValue`, `owl:onProperty`, `owl:maxCardinality` and `owl:maxQualifiedCardinality` with `onClass`, and the class and property declarations, one field per condition. Leaving out the other conditions admits more interpretations. Entailment under these conditions therefore implies entailment under the full semantics, so the soundness proofs remain valid for full OWL 2 RDF-Based entailment. This is recorded as a soundness-neutral simplification.

### Cardinality via the literal term

`cls-maxc2` and `cls-maxqc3/4` match the literal `"1"^^xsd:nonNegativeInteger` (and `"0"` for `maxqc`) as a constant in the pattern. The semantic condition is stated for the interpretation of that literal term, so no value space is needed. Other lexical forms of 1 do not fire the rule.

### The rule set

Derivation rules with a fixed number of premises:
- Equality: `eq-ref`, `eq-sym`, `eq-trans`, `eq-rep-s`, `eq-rep-p`, `eq-rep-o`.
- Properties: `prp-ap` (axioms), `prp-dom`, `prp-rng`, `prp-fp`, `prp-ifp`, `prp-symp`, `prp-trp`, `prp-spo1`, `prp-eqp1`, `prp-eqp2`, `prp-inv1`, `prp-inv2`.
- Classes: `cls-thing`, `cls-nothing1`, `cls-svf1`, `cls-svf2`, `cls-avf`, `cls-hv1`, `cls-hv2`, `cls-maxc2`, `cls-maxqc3`, `cls-maxqc4`.
- Class axioms: `cax-sco`, `cax-eqc1`, `cax-eqc2`.
- Schema: `scm-cls`, `scm-sco`, `scm-eqc1`, `scm-eqc2`, `scm-op`, `scm-dp`, `scm-spo`, `scm-eqp1`, `scm-eqp2`, `scm-dom1`, `scm-dom2`, `scm-rng1`, `scm-rng2`, `scm-hv`, `scm-svf1`, `scm-svf2`, `scm-avf1`, `scm-avf2`.

`owlRules := rdfsRules ++ owlRLRules`, proven sound against `IsOWL`.

### Bridge profile

The oxilite bridge takes a profile. `rdfs` uses `rdfsRules`; `owl` uses `owlRules` and maps oxilite's OWL template names (`cax-eqc`, `prp-eqp`, `prp-inv`, `prp-symp`, `prp-trp`, `eq-rep-s`, `eq-rep-o`, `eq-sym`) to rule preferences. `--materialized` runs `oxilite materialize`, reads the inferred triples (a query with inferences minus one without), and certifies each one with Elpi under `owlRules`. An inference that needs an excluded rule is reported `not derived`, never `certified`.

## Constraints

- New: `OWL 2 RDF-Based Semantics` (W3C 2012, §5), binding `OWLConditions`.
- New: `OWL 2 RL rules` (OWL 2 Profiles §4.3), binding the rule bodies and heads.
- [[constraints#Lake requires per package]]: `leanrdf-owl` requires only the core.

## Risks / Trade-offs

- **`eq-ref` makes every term `sameAs` itself**, which multiplies the closure. The bridge saturates only small graphs. Certificates use `eq-ref` only when a proof needs it.
- **Non-vacuity needs a hand-built model**, because sameAs and the restriction conditions rule out the plain term model. A small finite model over `Fin n`, with every other IRI mapped to a junk element, keeps the proofs decidable.
