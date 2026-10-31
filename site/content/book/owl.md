---
title: OWL 2 RL, sound rule by rule
order: 13
summary: The OWL 2 RDF-Based conditions the OWL 2 RL rules need, 49 rules proven sound, a model that shows the conditions are consistent, oxilite's OWL closure certified, and certified OWL 2 EL classification.
---
# OWL 2 RL, sound rule by rule

RDFS can say that a class is below another class and that a property has a domain. OWL adds identity (`owl:sameAs`), equivalence, inverse, symmetric and transitive properties, and restrictions such as "everything with a child that is a person". OWL 2 RL is the part of OWL that a rule engine can compute: a fixed list of if-then rules over triples. oxilite materializes that closure. The `leanrdf-owl` package proves the rules sound, so a certificate built from them is a theorem, as it is for RDFS.

## The conditions

An OWL interpretation is an RDFS interpretation with extra conditions on the OWL vocabulary, taken from the OWL 2 RDF-Based Semantics §5. `OWLConds` has one field per condition. Three examples:

```lean
structure OWLConds (I : SimpleInterp) : Prop where
  sameAs : ∀ x y, I.IEXT (I.IS sameAs) x y ↔ x = y ∧ I.IR x
  inverse : ∀ p q, I.IEXT (I.IS inverseOf) p q → ∀ x y, I.IEXT p x y ↔ I.IEXT q y x
  transitive : ∀ p, I.InClass p (I.IS TransitiveProperty) →
    ∀ x y z, I.IEXT p x y → I.IEXT p y z → I.IEXT p x z
  -- …
```

The specification states many conditions as "if and only if". `OWLConds` keeps only what the rules use. For domains, ranges and equivalent properties, that is a rule-shaped consequence ("a domain extends to every superclass") instead of the full reverse direction. Every field follows from the full semantics, so more interpretations qualify, and a rule that is sound here is sound for full OWL 2 RDF-Based entailment. Both omissions are recorded as simplifications.

## The rules

`owlRules` is the 80 RDFS rules, the OWL axiomatic triples (`owl:Thing` and `owl:Nothing` are classes, the annotation properties are annotation properties), and 49 OWL 2 RL rules: equality (`eq-ref`, `eq-sym`, `eq-trans`, `eq-rep-s/p/o`), property characteristics (`prp-fp`, `prp-ifp`, `prp-symp`, `prp-trp`, `prp-eqp1/2`, `prp-inv1/2`), restrictions (`cls-svf1/2`, `cls-avf`, `cls-hv1/2`, `cls-maxc2`, `cls-maxqc3/4`), equivalent classes (`cax-eqc1/2`) and the schema rules `scm-*`. Rules whose premises walk an `rdf:List` (intersections, unions, keys) and rules that conclude `false` are left out.

Each rule has its own soundness proof, and together they give the same theorem as for RDFS:

```lean
theorem owlRules_sound : ∀ r ∈ owlRules, r.SoundIn OWLCore

theorem Derives.owl_sound {g : Graph} {t : Triple} (h : Derives owlRules g t) :
    g.OWLEntails (Graph.singleton t)
```

## The conditions are not vacuous

A set of conditions that no interpretation satisfies would make every rule sound. `OwlTests/Model.lean` builds one OWL interpretation, on the small RDFS models of the core: `owl:sameAs` and `owl:equivalentProperty` are identity, `owl:equivalentClass` relates classes with the same members, `owl:inverseOf` relates total properties, and `owl:Nothing` and the property characteristics are empty. The kernel checks that it satisfies every field, that it is a model of a graph with an inverse property, an identity and a someValuesFrom restriction, and that it refutes two entailments:

```lean
theorem inverse_not_equivalent :
    ¬ {p owl:inverseOf q}.OWLEntails {p owl:equivalentProperty q}
theorem type_not_sameAs :
    ¬ {a rdf:type C}.OWLEntails {a owl:sameAs b}
```

(The statements are abbreviated; the files spell out the graphs.)

## Certifying oxilite's OWL closure

`leanrdf-oxilite --profile owl` asks oxilite to materialize its OWL 2 RL closure, answers the query against it, and checks each answer under `owlRules`, from oxilite's `why` tree or from Elpi's search. A `prp-inv` step in oxilite's explanation becomes `prp-inv1` or `prp-inv2`. Under the RDFS profile the same step is untranslated, because no RDFS rule matches it.

`leanrdf-oxilite DATA --materialized` certifies the whole closure one triple at a time. On the recorded family sample, 18 of oxilite's 31 inferences are certified, among them the inverse, transitive, symmetric, subproperty, equivalent-class and sameAs inferences. The other 13 say that a resource is an `owl:Thing`. They are true under the OWL semantics, but OWL 2 RL has no rule for them, and oxilite's own `why` names no template. They are reported `not derived`: "not derived" never means "not entailed". A made-up triple added to the recorded closure is never certified.

## OWL 2 EL: classifying with intersections and existentials

Most large biomedical ontologies are in OWL 2 EL: classes are defined from other classes by intersection and existential restriction ("a parent is a person with a child who is a person"). In RDF an intersection is a node with `owl:intersectionOf` and an `rdf:first`/`rdf:rest` list. The OWL conditions gain one field: an intersection of a sequence of classes contains exactly the resources in all of them.

Ten EL completion rules use it. Elimination takes each conjunct (`C ⊑ A ⊓ B` gives `C ⊑ A`), introduction builds an intersection (`C ⊑ A` and `C ⊑ B` give `C ⊑ A ⊓ B`), and three rules move through existentials: to a larger filler, to a superproperty, and to `owl:Nothing` when the filler is empty. The rules match lists of two or three members in full, down to `rdf:nil`, because only a complete list is a sequence the condition talks about. Each rule is proven sound, so `Derives.el_sound` gives OWL entailment for `owlELRules`.

`lake exe leanrdf-classify ONTOLOGY` saturates an ontology once with Elpi and certifies each derived subsumption between named classes as its own query. Only certified subsumptions are printed. On the example ontology in `elpi/examples/el-ontology.ttl` it prints the 20 subsumptions and two unsatisfiable classes computed by hand, among them `:Mother ⊑ :Parent`. That one needs both an intersection and an existential: a mother is a woman with a child who is a person, a woman is a person, and a parent is defined as a person with such a child.
