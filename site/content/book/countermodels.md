---
title: Is the semantics empty?
order: 7
summary: Why soundness alone proves nothing if the conditions are contradictory, and the kernel-checked models that rule it out.
---
# Is the semantics empty?

Soundness has a blind spot. If the transcribed RDFS conditions were contradictory — a wrong `↔`, an over-strong axiom — no RDFS interpretation would exist. Then *every* graph would RDFS-entail *every* other graph, and `Derives.sound` would be true for a trivial reason. Nothing in the soundness proof would notice.

LeanRDF rules this out with proofs, not tests: a concrete RDFS interpretation, and countermodels for entailments that must fail. All are kernel-checked, without `native_decide`.

## One family of small models

`Tests/Semantics/SmallModel.lean` builds an RDFS interpretation from a few parameters:

- the carrier is `Term`; every IRI denotes itself and literals denote themselves (tags lowercased);
- every element is a resource and a property;
- every class contains everything, except `xsd:string`, `rdf:langString` and chosen **custom** classes;
- `rdfs:subClassOf` is *inclusion of class extensions*, so reflexivity, transitivity and the extension condition hold by construction;
- `rdfs:subPropertyOf` is the least relation the axioms and `rdfs:member` force.

The file then proves every one of the RDF and RDFS conditions, all 46 finite axioms and the infinite `rdf:_n` axioms, for every choice of parameters:

```lean
theorem isRDFS : (interp P).IsRDFS := ⟨rdf P, rdfs P⟩
```

## A model exists

With no custom classes, the model satisfies a graph using `subClassOf`, `rdf:type`, `rdfs:domain` and a plain property:

```lean
theorem model_exists : ∃ I : DInterp, I.IsRDFS ∧ I.Satisfies (Graph.ofList
    [T (ex "A") rdfs.subClassOf (ex "B"), T (ex "x") rdf.type (ex "A"),
     T (ex "p") rdfs.domain (ex "A"), T (ex "x") (ex "p") (ex "y")])
```

## Three things RDFS must not conclude

Each countermodel makes one class or property empty:

| Non-entailment | Countermodel |
|---|---|
| `A ⊑ B` does not give `B ⊑ A` | `ex:A` is empty, so `B ⊑ A` would need `B` empty too |
| `x a C` does not give `x a D` | `ex:D` is empty |
| `p rdfs:domain C` and `x q y` do not give `x a C` | `ex:p` relates nothing, `ex:C` is empty |

```lean
theorem subClassOf_not_symmetric :
    ¬ (Graph.ofList [T (ex "A") rdfs.subClassOf (ex "B")]).RDFSEntails
      (Graph.ofList [T (ex "B") rdfs.subClassOf (ex "A")])
```

## Independent hand proofs

Finally, one entailment per basic rule is proved directly from the RDFS conditions, without `Rule` or `Derives` — a cross-check that the soundness lemmas prove what they claim:

```lean
theorem subClassOf_inherits : (Graph.ofList [T (ex "A") rdfs.subClassOf (ex "B"),
    T (ex "x") rdf.type (ex "A")]).RDFSEntails (Graph.ofList [T (ex "x") rdf.type (ex "B")]) :=
  entails_of fun _ hI h1 h2 => HoldsIRI.of_IEXT _ ((hI.2.subClass_ext _ _ h1.2).2.2 _ h2.2)
```

Together: the class of RDFS interpretations is non-empty, it does not collapse entailment, and the rules agree with direct reasoning from the definitions.
