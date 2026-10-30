## Context

OWL 2 EL (OWL 2 Profiles §2) allows `ObjectIntersectionOf`, `ObjectSomeValuesFrom`, `owl:Thing` and `owl:Nothing`, class and property hierarchies. In RDF, an intersection is a class with `owl:intersectionOf` pointing to an `rdf:first`/`rdf:rest` list, and an existential is a restriction node with `owl:onProperty` and `owl:someValuesFrom`. The OWL 2 RDF-Based Semantics §5.4 interprets `owl:intersectionOf` through sequences.

## Goals / Non-Goals

**Goals:** sound, certified subsumptions between named classes for EL ontologies with intersections of up to three conjuncts.

**Non-Goals:** completeness; longer intersections; role chains (`owl:propertyChainAxiom`); nominals; a consequence-based reasoner.

## Decisions

### Lists by length

`ListOf I l [c₁, …, cₙ]` says that `l` denotes the sequence `c₁ … cₙ` through `IEXT(rdf:first)` and `IEXT(rdf:rest)`, ending in `rdf:nil`. The new condition says that if `⟨x, l⟩ ∈ IEXT(owl:intersectionOf)` and `ListOf I l cs`, then `ICEXT(x)` is the intersection of the `ICEXT(c)` for `c` in `cs`. Rules match lists of length 2 and 3 with fixed patterns: `?l rdf:first ?a . ?l rdf:rest ?l2 . ?l2 rdf:first ?b . ?l2 rdf:rest rdf:nil`.

### The completion rules

With `C ⊑ D` meaning `C rdfs:subClassOf D`:
- `el-int-e1`, `el-int-e2` (and `e3` for length 3): from `C ⊑ X` and `X ≡ A ⊓ B` (as a list), derive `C ⊑ A` and `C ⊑ B`.
- `el-int-i2`, `el-int-i3`: from `C ⊑ A`, `C ⊑ B` and `X` the intersection of `A` and `B`, derive `C ⊑ X`.
- `el-ex`: from `C ⊑ R`, `R = ∃p.D`, `D ⊑ E` and `S = ∃p.E`, derive `C ⊑ S`.
- `el-ex-sub`: from `C ⊑ R`, `R = ∃p.D`, `p ⊑ q` and `S = ∃q.D`, derive `C ⊑ S`.
- `el-ex-bot`: from `C ⊑ R`, `R = ∃p.D` and `D ⊑ owl:Nothing`, derive `C ⊑ owl:Nothing`.

Together with `scm-cls`, `scm-sco`, `scm-eqc*` and `cax-sco` from `owlRules`, these classify the usual EL test ontologies whose class expressions occur in the ontology.

### Classification as a set of queries

`leanrdf-classify` saturates once. It then certifies each derived `A rdfs:subClassOf B` between named classes (IRIs) as its own query, and prints the hierarchy with only certified edges. An uncertified subsumption is never printed as one.

## Constraints

- New: `OWL 2 EL profile` (OWL 2 Profiles §2), binding which class expressions are in scope.
- The existing `OWL 2 RDF-Based Semantics` constraint binds the intersection condition.

## Risks / Trade-offs

- **Rules with eight premises** make the Elpi saturation slower. EL test ontologies are small.
- **Intersections longer than three** are not decomposed; their subsumptions are missed, never wrong.
