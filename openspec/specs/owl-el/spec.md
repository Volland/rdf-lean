# owl-el Specification

## Purpose
TBD - created by archiving change add-owl-el. Update Purpose after archive.

## Requirements

### Requirement: Intersection condition
`OWLConds` SHALL include the OWL 2 RDF-Based condition for `owl:intersectionOf` over sequences built from `rdf:first` and `rdf:rest`, with lemmas for sequences of two and three classes.

#### Scenario: Two-element intersection
- **WHEN** `⟨x, l⟩ ∈ IEXT(owl:intersectionOf)` and `l` denotes the sequence `a, b`
- **THEN** a lemma gives `ICEXT(x) = ICEXT(a) ∩ ICEXT(b)`

### Requirement: EL completion rules
`elRules` SHALL encode `el-int-e1`, `el-int-e2`, `el-int-e1-3`, `el-int-e2-3`, `el-int-e3`, `el-int-i2`, `el-int-i3`, `el-ex`, `el-ex-sub` and `el-ex-bot` over the RDF encoding of intersections and existential restrictions, and `owlELRules` SHALL be `owlRules ++ elRules`.

#### Scenario: Existential monotonicity
- **WHEN** a certificate derives `:Hand ⊑ :R2` from `:Hand ⊑ :R1`, `:R1 = ∃:hasPart.:Thumb`, `:Thumb ⊑ :Finger` and `:R2 = ∃:hasPart.:Finger` with `el-ex`
- **THEN** the checker accepts it under `owlELRules`

### Requirement: EL soundness
Every rule in `elRules` SHALL be proven sound against `IsOWL`, and `Derives owlELRules g t` SHALL imply `g.OWLEntails (Graph.singleton t)`, with no `sorry` and only Lean's standard axioms.

#### Scenario: Soundness theorem
- **WHEN** the package is built
- **THEN** `elRules_sound` and `Derives.el_sound` are theorems, and `#print axioms` shows only `propext`, `Quot.sound` and `Classical.choice`

### Requirement: Certified classification
`lake exe leanrdf-classify ONTOLOGY` SHALL saturate the ontology with Elpi under `owlELRules`, certify every derived subsumption between named classes, and print the hierarchy using only certified subsumptions. It SHALL exit with 0 when every derived subsumption is certified, 2 when a certificate is rejected and 3 on an input error.

#### Scenario: The example ontology
- **WHEN** `leanrdf-classify` runs on `examples/el-ontology.ttl`
- **THEN** it prints exactly the hand-computed subsumptions, each certified, and exits with 0

#### Scenario: A subsumption through an intersection and an existential
- **WHEN** the example defines `:Parent ≡ :Person ⊓ ∃:hasChild.:Person` and states `:Mother ⊑ :Woman ⊓ ∃:hasChild.:Person` and `:Woman ⊑ :Person`
- **THEN** `:Mother ⊑ :Parent` is derived and certified
