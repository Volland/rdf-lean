---
title: Why RDF semantics in Lean
order: 1
summary: What "entails" means for RDF, why reasoners disagree, and how LeanRDF makes each answer a theorem.
---
# Why RDF semantics in Lean

RDF is a language for statements about things: *bob has pet tom*, *a cat is a mammal*. Each statement is a **triple** of a subject, a predicate and an object, and a set of triples is a **graph**. RDFS adds a small vocabulary for classes and properties: `rdfs:subClassOf`, `rdfs:domain`, `rdfs:range`, `rdfs:subPropertyOf`.

From the triples

```
ex:Cat    rdfs:subClassOf ex:Mammal .
ex:tom    rdf:type        ex:Cat .
```

every RDFS reasoner concludes `ex:tom rdf:type ex:Mammal`. The reason is not the reasoner's code. It is the **model theory** of RDF 1.1 Semantics, a W3C Recommendation: a graph *entails* another graph when every interpretation that makes the first true also makes the second true. Reasoners implement rules that are supposed to be sound for that definition.

## The gap this library closes

Rules are written by hand, translated into code, optimized, and run on graphs with cycles, blank nodes and literals in odd places. Each step can drift from the definition. Usually nobody notices, because the only check is another reasoner.

LeanRDF writes the definition itself in Lean 4, proves the rules sound against it, and lets any search engine propose answers that a small verified checker accepts or rejects. When the checker accepts, Lean gives you a proposition:

```lean
g.RDFSEntails q
```

which says, in Lean's logic, that every RDFS interpretation satisfying `g` satisfies `q`.

## Elpi finds, Lean checks

Proof search is the expensive part, and the part most likely to change. LeanRDF keeps it out of the trusted base:

<figure><img src="{{BASE}}/assets/pipeline.svg" alt="Pipeline from Turtle to the theorem g entails q"><figcaption>The untrusted search produces a certificate; the trusted checker turns it into a theorem.</figcaption></figure>

- **Untrusted:** the Elpi engine ([lean-elpi](https://github.com/Volland/lean-elpi), λProlog written in Lean), the Elpi clauses generated from the rules, the saturation driver, and anything else that emits certificates.
- **Trusted:** the Lean kernel, the semantics (`LeanRDF.Semantics`), the derivation relation `Derives`, and the checker with its soundness theorem.

A bug in the search shows up as a rejected certificate, never as a wrong "entailed".

## What this book covers

1. How RDF data is represented in Lean ([chapter 2](/book/graphs/)) and read from N-Triples and Turtle ([chapter 3](/book/syntax/)).
2. What a graph *means*: interpretations, satisfaction and entailment ([chapter 4](/book/meaning/)), then the RDF and RDFS conditions ([chapter 5](/book/rdfs/)).
3. Rules as data, derivations and the soundness theorem ([chapter 6](/book/rules/)), and how countermodels show the semantics is not vacuous ([chapter 7](/book/countermodels/)).
4. The search side in Elpi ([chapter 8](/book/elpi/)), certificates and the checker ([chapter 9](/book/certificates/)), and the whole workflow on a rule of your own ([chapter 10](/book/custom-rule/)).
5. Certifying a real triple store, oxilite, from its own explanations ([chapter 11](/book/oxilite/)).
6. Where certificates are not enough and the engine itself is proven: SPARQL ([chapter 12](/book/sparql/)), OWL 2 RL and EL ([chapter 13](/book/owl/)) and SHACL ([chapter 14](/book/shacl/)).
7. An honest account of what is proven and what is trusted ([chapter 15](/book/trust/)).

You need to read Lean 4 a little; you do not need to know RDF or model theory.
