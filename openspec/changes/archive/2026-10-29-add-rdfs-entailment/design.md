## Context

RDF 1.1 Semantics (W3C Recommendation, 25 February 2014) defines simple interpretations (§5), D-interpretations (§7.1), RDF interpretations (§8) and RDFS interpretations (§9), and lists the RDFS entailment patterns informatively (§9.2.1). The interview of 2026-10-29 fixed the shape: one carrier, full condition tables, soundness against a core, and vacuity tests.

## Goals / Non-Goals

**Goals:** a transcription a reader can check against the spec line by line; soundness of six rules with no `sorry` and no new axiom; kernel-checked evidence that the class of RDFS interpretations is neither empty nor trivially entailing.

**Non-Goals:** completeness; datatypes other than the two required ones; value-space reasoning; the remaining RDFS patterns (`add-rdfs-full`); datasets.

## Decisions

### One carrier, conditions as fields

`SimpleInterp` has `Dom : Type` with `IR IP : Dom → Prop`, `IEXT : Dom → Dom → Dom → Prop` with the well-typedness condition, `IS : IRI → Dom` into `IR ∪ IP` and `IL : Literal → Option Dom` into `IR`. `DInterp` adds abstract datatype values (`langVal`, partial `strVal`) with the two §7.1 conditions. The RDF and RDFS conditions are Prop structures over a `DInterp` (`RDFConditions`, `RDFSConditions`), one field per row of the spec's tables, so helper notions such as `InClass` and `SubClass` can be used in their statements. See [[decisions#Single-carrier interpretations]].

### Reading the tables

- "Transitive and reflexive on IP/IC" is read as transitive, and reflexive on IP/IC.
- Container membership properties are `rdf:_n` for `n ≥ 1`, so their axioms are stated as `∀ n, … rdf.member (n + 1) …`.
- The value space of `rdf:langString` is taken as the pairs with lowercased tags. §8 makes `ICEXT(I(rdf:langString))` equal to its value space and §9 makes it the set of values of language-tagged literals, whose tags §7.1 lowercases, so the two only agree that way.
- A blank-node mapping `A` is total on all blank nodes into `IR`, which is equivalent to the spec's mapping on the graph's blank nodes because `IR` is non-empty.

### Generalized satisfaction

`Holds A ⟨s, p, o⟩` requires all three terms to denote, `I(p) ∈ IP` and `⟨I(s), I(o)⟩ ∈ IEXT(I(p))`, for any term in any position. A literal with no referent makes its triple false (§5).

### Rules and derivations

`Rule` is `{name, body : List TPat, head : TPat, guards : List Guard}`. `Guard` is an inductive with no constructors yet, so the six rules have empty guards and the format will not change when `add-rdfs-full` adds constructors. `Derives rules g` has a `fact` case and an `apply` case taking a total substitution `σ : String → Term`. See [[decisions#Horn rules matched by the checker]].

### Soundness through RDFSCore

`Rule.Sound r` quantifies over every `SimpleInterp` satisfying `RDFSCore` and every blank-node mapping; each rule's lemma uses one or two core conditions. `Derives.holds` lifts rule soundness to derivations by induction, and `Derives.sound` and `Derives.sound_graph` lift it to RDFS entailment through `RDFSConditions.toCore`. `sound_graph` maps each query blank node to the denotation of its image under `μ`, which lies in `IR` because RDF interpretations make every property a resource. See [[decisions#Layered interpretations with a core]] and [[decisions#Graph queries with instance mappings]].

### One small-model family for vacuity

`Tests/Semantics/SmallModel.lean` builds one RDFS interpretation from parameters. The carrier is `Term`, IRIs denote themselves and every element is a resource and a property. Every class contains everything except `xsd:string`, `rdf:langString` and chosen custom classes, and every non-vocabulary property relates everything except chosen custom properties. `rdfs:subClassOf` is inclusion of class extensions, so reflexivity, transitivity and the extension condition hold by construction. `rdfs:subPropertyOf` is the least relation the axioms and `rdfs:member` force; domains and ranges are defined from an over-approximation of the extensions. The countermodels choose an empty class or property. Rejected: a canonical-closure model, which amounts to a completeness proof. See [[decisions#Semantics tested against vacuity]].

## Constraints

[[constraints#Simple interpretations]], [[constraints#RDF interpretations recognize two datatypes]], [[constraints#RDFS interpretation conditions]], [[constraints#Entailment rules use generalized RDF]], [[constraints#Entailed blank nodes are existential]], [[constraints#String hash is opaque to the kernel]] (the vacuity proofs avoid hash sets and `native_decide`).

## Risks / Trade-offs

- **Weaker datatype abstraction.** Abstract `strVal` and `langVal` admit more interpretations than the spec (any embedding of the values), which only strengthens soundness; non-entailments shown here are about this class.
- **The universal classes.** The small model needs every class that the axioms, domains or ranges force to be total; a future axiom with a new target class must be added to `universalClasses`.
