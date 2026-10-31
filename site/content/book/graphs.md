---
title: RDF graphs in Lean
order: 2
summary: Terms, literals that cannot be ill-formed, generalized triples, and graphs used through membership.
---
# RDF graphs in Lean

The data model lives in `LeanRDF/Core/` and has no dependencies beyond Lean's standard library.

## Terms

An RDF term (RDF 1.2 Concepts §3) is an IRI, a blank node, a literal or a triple term:

```lean
structure IRI where
  val : String

structure BlankNode where
  label : String

inductive Direction where
  | ltr | rtl

inductive Literal where
  | typed (lex : String) (dt : IRI)
  | lang (lex : String) (tag : String)
  | dirLang (lex : String) (tag : String) (dir : Direction)

inductive Term where
  | iri (i : IRI)
  | bnode (b : BlankNode)
  | lit (l : Literal)
  | triple (s p o : Term)
```

All of them derive `DecidableEq`, `Hashable` and `Ord`. A triple term carries its three components directly, so `Term` stays one recursive type: `<<( ex:a ex:p ex:b )>>` is `.triple (ex "a") (ex "p") (ex "b")`, and two triple terms are equal when their components are. Term equality is character by character: `HTTP://example.org/a` and `http://example.org/a` are different IRIs, and `"1"^^xsd:integer` differs from `"01"^^xsd:integer`, because RDF compares terms, not values.

### Literals that cannot be wrong

RDF says a literal has a language tag exactly when its datatype is `rdf:langString`, or, with a base direction (`ltr` or `rtl`), `rdf:dirLangString`. LeanRDF makes the first half impossible to violate: a language-tagged literal is the constructor `lang` or `dirLang`, and its datatype is computed.

```lean
def Literal.datatype : Literal → IRI
  | .typed _ dt => dt
  | .lang _ _ => rdf.langString
  | .dirLang _ _ _ => rdf.dirLangString
```

The other half, a `typed` literal claiming `rdf:langString` or `rdf:dirLangString`, is rejected by the smart constructor that every parser uses:

```lean
#guard Literal.mk? "x" rdf.langString none = none
#guard Literal.lang' "a" "EN" == Literal.lang' "a" "en"   -- tags are lowercased
#guard (Literal.dirLang' "مرحبا" "ar" .rtl).datatype == rdf.dirLangString
#guard Literal.str "x" == .typed "x" xsd.string
```

## Generalized triples

```lean
structure Triple where
  s : Term
  p : Term
  o : Term
```

Any term may stand in any position. That is deliberate: the RDFS rules are stated over **generalized RDF**, and the range rule happily derives `"5" rdf:type ex:Number` with a literal subject. Strict RDF 1.2 triples are those satisfying a decidable predicate: the subject is an IRI or a blank node, the predicate an IRI, and the object any term, where a triple term must itself be strict. A triple term may therefore be an object, nested to any depth, but never a subject:

```lean
#guard decide (Triple.mk (ex "r") (.iri rdf.reifies) (.triple (ex "a") (ex "p") (ex "b"))).WellFormed
#guard !decide (Triple.mk (.triple (ex "a") (ex "p") (ex "b")) (ex "q") (ex "c")).WellFormed
```

`Triple.mk?` builds only well-formed ones. `Graph.Basic` decides whether a graph has no triple term at all, which is RDF 1.2 *Basic* conformance and everything an RDF 1.1 document parses to.

A triple term is not asserted by appearing: `ex:r rdf:reifies <<( ex:a ex:p ex:b )>>` says something about the proposition `ex:a ex:p ex:b` without claiming it. In the semantics, a triple term denotes `IT` of its components, an injective map every interpretation carries (RDF 1.2 Semantics §5).

## Graphs, through membership only

A `Graph` wraps a `Std.HashSet Triple`, but the representation is private. You use it through `∈` and a handful of lemmas:

```lean
theorem Graph.mem_insert : u ∈ g.insert t ↔ u = t ∨ u ∈ g
theorem Graph.mem_union  : t ∈ g ∪ h ↔ t ∈ g ∨ t ∈ h
theorem Graph.mem_singleton : u ∈ Graph.singleton t ↔ u = t
theorem Graph.mem_ofList : t ∈ Graph.ofList l ↔ t ∈ l
theorem Graph.mem_toList : t ∈ g.toList ↔ t ∈ g
```

Every proof in the library is stated with these, never with the hash set, so the representation could change in one file. `toList` sorts, which makes output deterministic.

<figure><img src="{{BASE}}/assets/pets-graph.svg" alt="The pet ontology drawn as a graph"><figcaption>A graph is a set of triples: nodes are terms, arrows are triples. Dashed arrows are what RDFS adds.</figcaption></figure>

## Blank nodes and isomorphism

Blank nodes are local names: two graphs that differ only in blank-node labels say the same thing. LeanRDF defines this as a proposition (RDF 1.1 Concepts §3.6):

```lean
def Graph.Iso (g h : Graph) : Prop :=
  ∃ f : BlankNode → BlankNode, Bijective f ∧ ∀ t : Triple, t ∈ g ↔ t.renameBNodes f ∈ h
```

The tests prove, for example, that `{_:a ex:p ex:o}` and `{_:b ex:p ex:o}` are isomorphic by exhibiting the swap of `a` and `b`.
