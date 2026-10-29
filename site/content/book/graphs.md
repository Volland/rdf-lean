---
title: RDF graphs in Lean
order: 2
summary: Terms, literals that cannot be ill-formed, generalized triples, and graphs used through membership.
---
# RDF graphs in Lean

The data model lives in `LeanRDF/Core/` and has no dependencies beyond Lean's standard library.

## Terms

An RDF term (RDF 1.1 Concepts §3) is an IRI, a blank node or a literal:

```lean
structure IRI where
  val : String

structure BlankNode where
  label : String

inductive Literal where
  | typed (lex : String) (dt : IRI)
  | lang (lex : String) (tag : String)

inductive Term where
  | iri (i : IRI)
  | bnode (b : BlankNode)
  | lit (l : Literal)
```

All of them derive `DecidableEq`, `Hashable` and `Ord`. Term equality is character by character: `HTTP://example.org/a` and `http://example.org/a` are different IRIs, and `"1"^^xsd:integer` differs from `"01"^^xsd:integer`, because RDF compares terms, not values.

### Literals that cannot be wrong

RDF says a literal has a language tag exactly when its datatype is `rdf:langString`. LeanRDF makes the first half impossible to violate: a language-tagged literal is the constructor `lang`, and its datatype is computed.

```lean
def Literal.datatype : Literal → IRI
  | .typed _ dt => dt
  | .lang _ _ => rdf.langString
```

The other half, a `typed` literal claiming `rdf:langString`, is rejected by the smart constructor that every parser uses:

```lean
#guard Literal.mk? "x" rdf.langString none = none
#guard Literal.lang' "a" "EN" == Literal.lang' "a" "en"   -- tags are lowercased
#guard Literal.str "x" == .typed "x" xsd.string
```

## Generalized triples

```lean
structure Triple where
  s : Term
  p : Term
  o : Term
```

Any term may stand in any position. That is deliberate: the RDFS rules are stated over **generalized RDF**, and the range rule happily derives `"5" rdf:type ex:Number` with a literal subject. Strict RDF 1.1 triples are those satisfying a decidable predicate:

```lean
def Triple.WellFormed (t : Triple) : Prop :=
  (match t.s with | .lit _ => False | _ => True) ∧
  (match t.p with | .iri _ => True | _ => False)
```

and `Triple.mk?` builds only well-formed ones.

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
