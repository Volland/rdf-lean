---
title: Rules, derivations and soundness
order: 6
summary: RDFS entailment patterns as data, the Derives relation, and the proof that every derivation is an entailment.
---
# Rules, derivations and soundness

Entailment quantifies over all interpretations, which no program can enumerate. Reasoners instead apply **rules**: if these triples are present, add that one. LeanRDF writes rules as data and proves each one sound.

## Rules as data

```lean
inductive Pat where
  | var (n : String)
  | const (t : Term)

structure TPat where
  s : Pat
  p : Pat
  o : Pat

structure Rule where
  name : String
  body : List TPat
  head : TPat
  guards : List Guard := []
```

Rule rdfs9, transcribed from RDF 1.1 Semantics §9.2.1 with the specification's variable names:

```lean
def rdfs9 : Rule :=
  { name := "rdfs9"
    body := [⟨v "xxx", c rdfs.subClassOf, v "yyy"⟩, ⟨v "zzz", c rdf.type, v "xxx"⟩]
    head := ⟨v "zzz", c rdf.type, v "yyy"⟩ }
```

Variables may stand in any position: rdfs7 has a variable predicate. Every rule is **range-restricted** (head variables occur in the body) and names are unique; both are decidable and checked by `decide` in the tests.

Some patterns need a side condition. A `Guard` is a decidable test with a meaning and a proof that the test implies the meaning:

```lean
inductive Guard where
  | containerMembership (v : String)   -- the value is rdf:_n, n ≥ 1
  | stringLiteral (v : String)         -- an xsd:string literal
  | langLiteral (v : String)           -- a language-tagged literal

theorem Guard.check_sound (h : g.check σ = true) : g.Holds σ
```

`rdfsRules` has 67 rules: rdfs2–rdfs13, rdfD2, GrdfD1 for both datatypes, three container-membership axioms, and the 48 finite axiomatic triples as rules without premises.

## Derivations

```lean
inductive Derives (rules : List Rule) (g : Graph) : Triple → Prop where
  | fact {t : Triple} : t ∈ g → Derives rules g t
  | apply (r : Rule) (σ : Subst) : r ∈ rules → (∀ gd ∈ r.guards, gd.Holds σ) →
      (∀ b ∈ r.body, Derives rules g (b.apply σ)) → Derives rules g (r.head.apply σ)
```

A triple is derivable if it is in the graph, or the head of a rule instance whose guards hold and whose body instances are derivable.

## Soundness, one rule at a time

A rule is sound when, in every interpretation with the core conditions and under every blank-node mapping, true premises make the conclusion true:

```lean
def Rule.Sound (r : Rule) : Prop :=
  ∀ (I : SimpleInterp), RDFSCore I → ∀ (A : BlankNode → I.Dom) (σ : Subst),
    (∀ gd ∈ r.guards, gd.Holds σ) → (∀ b ∈ r.body, I.Holds A (b.apply σ)) →
    I.Holds A (r.head.apply σ)
```

The proof for rdfs9 reads like the textbook argument: unpack the two premises, observe that both mention the same class, and apply the subclass condition.

```lean
theorem rdfs9_sound : rdfs9.Sound := by
  intro I hI A σ _ hb
  obtain ⟨x, y, hx, hy, h1⟩ := holds_iri (hb _ (.head _))
  obtain ⟨z, x', hz, hx', h2⟩ := holds_iri (hb _ (.tail _ (.head _)))
  cases same hx hx'
  exact Holds.intro I hz rfl hy (hI.subClass_ext _ _ h1 _ h2)
```

All 67 are collected in `rdfsRules_sound`. Induction on `Derives` then gives the key theorem:

```lean
theorem Derives.sound {g : Graph} {t : Triple} (h : Derives rdfsRules g t) :
    g.RDFSEntails (Graph.singleton t)
```

## Queries with blank nodes

A query is a graph, and its blank nodes are existential. If replacing them by terms (an instance mapping `μ`) makes every query triple derivable, the query is entailed:

```lean
theorem Derives.sound_graph {g q : Graph} (μ : BlankNode → Term)
    (h : ∀ t ∈ q, Derives rdfsRules g (t.instantiate μ)) : g.RDFSEntails q
```

The proof builds a blank-node assignment from the denotations of `μ`'s values; it needs the RDF fact that every property is a resource.

These theorems use only `propext`, `Quot.sound` and `Classical.choice`, and a test pins that with `#print axioms`.
