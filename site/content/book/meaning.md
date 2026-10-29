---
title: What a graph means
order: 4
summary: Interpretations, satisfaction, existential blank nodes and entailment — the model theory of RDF, in Lean.
---
# What a graph means

A graph is syntax. To say whether a graph is *true* we need something it talks about: an **interpretation**, a little world with things in it and relations between them. RDF 1.1 Semantics §5 defines the simplest kind, and LeanRDF transcribes it.

<figure><img src="{{BASE}}/assets/interpretation.svg" alt="A graph on the left mapped to a world on the right"><figcaption>An interpretation maps names to things. The triple is true if the pair of things is in the extension of the property.</figcaption></figure>

## Simple interpretations

A simple interpretation has

- a non-empty set **IR** of resources,
- a set **IP** of properties, which may overlap IR,
- **IEXT**, the extension of each property: the pairs it relates,
- **IS**, mapping each IRI to a resource or property,
- **IL**, a *partial* map from literals to resources.

In Lean all of these live on one carrier `Dom`, with IR and IP as predicates, so that one thing can be a resource and a property at the same time — RDFS needs that constantly:

```lean
structure SimpleInterp where
  Dom : Type
  IR : Dom → Prop
  IP : Dom → Prop
  IEXT : Dom → Dom → Dom → Prop      -- IEXT p x y : ⟨x, y⟩ ∈ IEXT(p)
  IS : IRI → Dom
  IL : Literal → Option Dom
  IR_nonempty : ∃ x, IR x
  IEXT_wt : ∀ p x y, IEXT p x y → IP p ∧ IR x ∧ IR y
  IS_wt : ∀ i, IR (IS i) ∨ IP (IS i)
  IL_wt : ∀ l x, IL l = some x → IR x
```

## When is a triple true?

A term denotes something under a blank-node mapping `A`: IRIs through `IS`, literals through `IL` (possibly not at all), blank nodes through `A`. A triple holds when all three terms denote, the predicate is a property, and the pair is in its extension:

```lean
def SimpleInterp.Holds (A : BlankNode → I.Dom) (t : Triple) : Prop :=
  ∃ s p o, I.denote A t.s = some s ∧ I.denote A t.p = some p ∧ I.denote A t.o = some o ∧
    I.IP p ∧ I.IEXT p s o
```

A literal with no referent makes its triple false, exactly as §5 says. The definition works for generalized triples too.

## Blank nodes are existential

A graph is true when *some* mapping of its blank nodes into IR makes every triple true:

```lean
def SimpleInterp.Satisfies (g : Graph) : Prop :=
  ∃ A : BlankNode → I.Dom, (∀ b, I.IR (A b)) ∧ ∀ t ∈ g, I.Holds A t
```

So `_:p rdf:type ex:Cat` says "there is a cat". This is why a query like *is there a person with a pet that is a mammal?* is itself a graph with blank nodes.

## Entailment

A graph `g` entails `h` when every interpretation satisfying `g` satisfies `h`:

```lean
def Graph.SimpleEntails (g h : Graph) : Prop :=
  ∀ I : SimpleInterp, I.Satisfies g → I.Satisfies h
```

Two facts follow quickly and are proved in the tests:

- the empty graph is true in every interpretation;
- every graph simply entails its subgraphs.

Simple entailment knows nothing about vocabulary: `rdfs:subClassOf` is just another IRI. To make the RDFS vocabulary mean something we restrict which interpretations count. That is the next chapter.

> The quantifier is over interpretations whose carrier lives in Lean's `Type`. That is a recorded simplification; it does not weaken soundness, because a statement proved for every interpretation in `Type` still holds of each one.
