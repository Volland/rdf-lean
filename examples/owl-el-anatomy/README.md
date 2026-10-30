# Classifying an EL ontology

`anatomy.ttl` is a small medical ontology in OWL 2 EL, in the style of SNOMED CT. Disorders are defined by what they are (`Inflammation`, `Disorder`) and where they are (`∃hasSite.Heart`), and `locatedIn` is a subproperty of `hasSite`.

```bash
cd elpi
lake exe leanrdf-classify ../examples/owl-el-anatomy/anatomy.ttl
```

It prints 36 certified subsumptions and 2 unsatisfiable classes. Some of them need several EL rules:

- `Endocarditis ⊑ Carditis`: endocarditis is located in the heart, so it has a site in the heart (el-ex-sub), and it is an inflammation (el-int-i2).
- `LobarPneumonia ⊑ Pneumonia`: all three conjuncts of pneumonia's definition hold (el-int-i3).
- `Pneumonia ⊑ OrganDisorder`: the lung is an organ (el-ex), and an inflammation is a disorder.
- `PhantomPain ⊑ owl:Nothing`: its site is an unsatisfiable class (el-ex-bot).

Every printed line is backed by a certificate that the verified checker accepted, and `Derives.el_sound` makes it an OWL entailment.
