---
title: OWL 2 RL and EL
order: 9
summary: The OWL conditions, the OWL 2 RL and EL rule lists, the soundness theorems, certificates under OWL, and classification.
---
# OWL 2 RL and EL

`leanrdf-owl` extends the RDFS machinery to OWL with rules, not with a new engine. It adds conditions on interpretations taken from the OWL 2 RDF-Based Semantics, rules proven sound under them, and nothing else. Certificates, the checker and Elpi work unchanged. Book chapter [13](/book/owl/) has the details.

## The semantics

| Definition | Meaning |
|---|---|
| `Owl.OWLConds I` | the OWL 2 RDF-Based conditions the rules need (§5): `owl:sameAs` is identity, characteristics of properties, inverses, equivalences, restrictions, `owl:intersectionOf`, and the axiomatic triples |
| `Owl.OWLCore I` | `RDFSCore I ∧ OWLConds I`, the class the rule proofs use |
| `DInterp.IsOWL I` | an RDFS interpretation with the OWL conditions |
| `Graph.OWLEntails g h` | every OWL interpretation that satisfies `g` satisfies `h` |
| `Owl.ListOf I l cs` | `l` denotes an RDF list with members `cs` |
| `Owl.sameAs_iff` | `x owl:sameAs y` holds exactly when `x = y` |

The conditions are a recorded subset of the specification, and a few are kept only in the direction the rules use. The rules stay sound for full OWL 2 RDF-Based entailment, because full entailment has more conditions, so it holds in fewer interpretations. `owl/OwlTests/Model.lean` builds an interpretation that satisfies all the conditions, which shows they are consistent and the theorems are not vacuous. It also has two countermodels: inverse properties need not be equivalent, and sharing a class does not make two things the same.

## Rule lists

| List | Size | Contents |
|---|---|---|
| `Owl.owlRLDerivationRules` | 49 | eq-ref, eq-sym, eq-trans, eq-rep-s/p/o; prp-fp, prp-ifp, prp-symp, prp-trp, prp-eqp1/2, prp-inv1/2; cls-svf1/2, cls-avf, cls-hv1/2, cls-maxc2, cls-maxqc3/4; cax-eqc1/2; the scm-* schema rules |
| `Owl.owlRLRules` | 60 | the derivation rules and 11 axiom rules (prp-ap, cls-thing, cls-nothing1) |
| `Owl.owlRules` | 127 | `RDFS.rdfsRules ++ owlRLRules` |
| `Owl.elRules` | 10 | el-int-e1, el-int-e2, el-int-e1-3, el-int-e2-3, el-int-e3, el-int-i2, el-int-i3, el-ex, el-ex-sub, el-ex-bot |
| `Owl.owlELRules` | 137 | `owlRules ++ elRules` |

Left out: the rules whose premises run over an `rdf:List` (prp-key, prp-spo2, cls-int1, cls-int2, cls-uni, cls-oo, scm-int, scm-uni, prp-adp, cax-adc, eq-diff2, eq-diff3) and the rules that conclude `false`. The EL rules cover intersections of two or three classes with fixed-length lists instead.

## Soundness

```lean
theorem owlRules_sound : ∀ r ∈ owlRules, r.SoundIn OWLCore
theorem Derives.owl_sound {g : Graph} {t : Triple} (h : Derives owlRules g t) :
    g.OWLEntails (Graph.singleton t)
theorem Derives.owl_sound_graph {g q : Graph} (μ : BlankNode → Term)
    (h : ∀ t ∈ q, Derives owlRules g (t.instantiate μ)) : g.OWLEntails q
theorem elRules_sound : ∀ r ∈ elRules, r.SoundIn OWLCore
theorem Derives.el_sound {g : Graph} {t : Triple} (h : Derives owlELRules g t) :
    g.OWLEntails (Graph.singleton t)
```

## A certificate under OWL

From `owl/OwlTests/Rules.lean`: `ex:hasChild owl:inverseOf ex:hasParent` and `ex:a ex:hasChild ex:b` give `ex:b ex:hasParent ex:a` by prp-inv1.

```lean
private def invCert : Certificate :=
  { nodes := [ ⟨0, T (ex "hasChild") (.iri inverseOf) (ex "hasParent"), "fact", []⟩,
               ⟨1, T (ex "a") (ex "hasChild") (ex "b"), "fact", []⟩,
               ⟨2, T (ex "b") (ex "hasParent") (ex "a"), "prp-inv1", [0, 1]⟩ ]
    goals := [2] }

#guard (check owlRules family invCert).toOption == some (T (ex "b") (ex "hasParent") (ex "a"))
#guard (check RDFS.rdfsRules family invCert).toOption.isNone

theorem family_entails : family.OWLEntails (Graph.singleton (T (ex "b") (ex "hasParent") (ex "a"))) :=
  Derives.owl_sound (checkB_sound (c := invCert) (by native_decide))
```

To let Elpi find OWL certificates, saturate with `Owl.owlRules` (see [The Elpi search](/docs/elpi/)). `leanrdf-oxilite --profile owl` does exactly that.

## Classification

`leanrdf-classify ONTOLOGY` saturates under `owlELRules` and certifies every derived subsumption between named classes. In Lean, `LeanRDF.Classify.classify g` returns the list of `Edge`s (`sub`, `sup`, `status`), and `render` prints them. The EL patterns it understands:

- `A rdfs:subClassOf B` and `owl:equivalentClass` between named classes;
- existential restrictions: `[ owl:onProperty p ; owl:someValuesFrom C ]` on either side, with `rdfs:subPropertyOf` between properties;
- intersections of two or three classes or restrictions, through `owl:intersectionOf`;
- `owl:Nothing`, for unsatisfiable classes.

Each printed subsumption is backed by a certificate the checker accepted, so `Derives.el_sound` makes it an OWL entailment. A subsumption that is entailed but not derived by these rules is not printed.
