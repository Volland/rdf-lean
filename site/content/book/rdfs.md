---
title: RDF and RDFS interpretations
order: 5
summary: Datatypes, the RDF and RDFS condition tables transcribed one field per row, and the core the proofs use.
---
# RDF and RDFS interpretations

Stronger entailment comes from fewer interpretations. RDF 1.1 Semantics adds conditions in three layers, and LeanRDF transcribes each row of each table as one field, with the section it comes from.

## D-interpretations (§7.1)

Every RDF interpretation recognizes two datatypes, `xsd:string` and `rdf:langString`. LeanRDF's `DInterp` adds their values as abstract fields:

```lean
structure DInterp extends SimpleInterp where
  langVal : String → String → Dom
  IL_lang : ∀ s t, IL (.lang s t) = some (langVal s t.toLower)
  strVal : String → Option Dom
  IL_str : ∀ s, IL (.typed s xsd.string) = strVal s
  -- plus injectivity of both
```

`strVal` is partial: an ill-typed string has no value, and a graph containing it is unsatisfiable.

## RDF conditions (§8)

```lean
structure RDFConditions (I : DInterp) : Prop where
  IP_iff : ∀ x, I.IP x ↔ I.InClass x (I.IS rdf.Property)
  string_class : ∀ x, I.InClass x (I.IS xsd.string) ↔ ∃ s, I.strVal s = some x
  langString_class : ∀ x, I.InClass x (I.IS rdf.langString) ↔ ∃ s t, x = I.langVal s t.toLower
  axioms : ∀ a ∈ rdfAxioms, I.HoldsIRI a
  axioms_member : ∀ n, I.HoldsIRI (rdf.member (n + 1), rdf.type, rdf.Property)
```

`InClass x c` is `⟨x, c⟩ ∈ IEXT(I(rdf:type))`. A consequence used often: in an RDF interpretation every property is a resource.

## RDFS conditions (§9)

The RDFS table has a row for each piece of vocabulary. A few of the sixteen fields:

```lean
structure RDFSConditions (I : DInterp) : Prop where
  resource : ∀ x, I.InClass x (I.IS rdfs.Resource) ↔ I.IR x
  domain : ∀ x y u v, I.IEXT (I.IS rdfs.domain) x y → I.IEXT x u v → I.InClass u y
  range  : ∀ x y u v, I.IEXT (I.IS rdfs.range) x y → I.IEXT x u v → I.InClass v y
  subClass_ext : ∀ x y, I.SubClass x y → I.IC x ∧ I.IC y ∧ ∀ u, I.InClass u x → I.InClass u y
  subClass_trans : ∀ x y z, I.SubClass x y → I.SubClass y z → I.SubClass x z
  axioms : ∀ a ∈ rdfsAxioms, I.HoldsIRI a
  -- … subproperties, classes, container membership, datatypes
```

An **RDFS interpretation** is a `DInterp` with both condition sets, and RDFS entailment quantifies over those:

```lean
def DInterp.IsRDFS (I : DInterp) : Prop := RDFConditions I ∧ RDFSConditions I

def Graph.RDFSEntails (g h : Graph) : Prop :=
  ∀ I : DInterp, I.IsRDFS → I.Satisfies g → I.Satisfies h
```

Simple ⇒ D ⇒ RDF ⇒ RDFS entailment, each a one-line theorem.

## Reading the tables

Where the tables are terse, LeanRDF fixes one reading and writes it down: "transitive and reflexive on IP" is transitive and reflexive on IP; container membership properties start at `rdf:_1`; the value space of `rdf:langString` uses lowercased tags (the only reading under which §8 and §9 agree).

## The core

Proofs do not need all sixteen conditions. `RDFSCore` collects exactly those the rules use, stated on a plain `SimpleInterp`, and one theorem derives it from the full conditions:

```lean
theorem DInterp.IsRDFS.toCore {I : DInterp} (h : I.IsRDFS) : RDFSCore I.toSimpleInterp
```

Soundness is proved against the core, which is the stronger statement: the larger the class of interpretations, the stronger a soundness theorem about all of them.
