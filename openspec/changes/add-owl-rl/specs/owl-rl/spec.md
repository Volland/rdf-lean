## ADDED Requirements

### Requirement: OWL conditions
`leanrdf-owl` SHALL define `OWLConditions` over an RDFS interpretation, transcribing the OWL 2 RDF-Based Semantics §5 conditions for the vocabulary that the included rules use, one field per condition, and `IsOWL` and `Graph.OWLEntails` from them. Every omitted condition SHALL be listed as a soundness-neutral simplification.

#### Scenario: sameAs is identity
- **WHEN** an interpretation satisfies `IsOWL`
- **THEN** `⟨x, y⟩ ∈ IEXT(I(owl:sameAs))` holds exactly when `x = y`, as a lemma

### Requirement: OWL 2 RL rules
`owlRLRules` SHALL encode, as `Rule` values, the OWL 2 RL/RDF rules of OWL 2 Profiles §4.3 that have a fixed number of premises and a triple as conclusion: `eq-ref`, `eq-sym`, `eq-trans`, `eq-rep-s`, `eq-rep-p`, `eq-rep-o`, `prp-ap`, `prp-dom`, `prp-rng`, `prp-fp`, `prp-ifp`, `prp-symp`, `prp-trp`, `prp-spo1`, `prp-eqp1`, `prp-eqp2`, `prp-inv1`, `prp-inv2`, `cls-thing`, `cls-nothing1`, `cls-svf1`, `cls-svf2`, `cls-avf`, `cls-hv1`, `cls-hv2`, `cls-maxc2`, `cls-maxqc3`, `cls-maxqc4`, `cax-sco`, `cax-eqc1`, `cax-eqc2` and the `scm-*` rules other than `scm-int` and `scm-uni`; and `owlRules` SHALL be `rdfsRules ++ owlRLRules`.

#### Scenario: Inverse and symmetric properties derive
- **WHEN** a certificate derives `b :hasParent a` from `a :hasChild b` and `:hasChild owl:inverseOf :hasParent` with `prp-inv1`
- **THEN** the checker accepts it under `owlRules`

#### Scenario: sameAs rewriting
- **WHEN** a certificate derives `b :p c` from `a :p c` and `a owl:sameAs b` with `eq-rep-s`
- **THEN** the checker accepts it under `owlRules`

### Requirement: OWL soundness
Every rule in `owlRLRules` SHALL be proven sound against `IsOWL`, and `Derives owlRules g t` SHALL imply `g.OWLEntails (Graph.singleton t)`, with no `sorry` and only Lean's standard axioms.

#### Scenario: Soundness theorem
- **WHEN** the package is built
- **THEN** `owlRules_sound` and `Derives.owl_sound` are theorems, and `#print axioms` shows only `propext`, `Quot.sound` and `Classical.choice`

### Requirement: OWL non-vacuity
There SHALL be kernel-checked evidence that the OWL conditions are satisfiable and not trivial: an interpretation satisfying `IsOWL` and a graph using `owl:inverseOf`, `owl:sameAs` and a someValuesFrom restriction, and at least two non-entailments proven by countermodels.

#### Scenario: A model and two countermodels
- **WHEN** the vacuity tests are built
- **THEN** the model theorem and `¬ OWLEntails` theorems for `{p inverseOf q} ⊭ {p equivalentProperty q}` and `{a type C} ⊭ {a sameAs b}` are proven without `native_decide`
