---
title: Semantics and entailment
order: 5
summary: Interpretations and the four entailment relations, rules as data, the Derives relation and the soundness theorems you call.
---
# Semantics and entailment

This page is the API side of book chapters [4](/book/meaning/) to [7](/book/countermodels/). The semantics is in `LeanRDF.Semantics`, and the rules and their proofs are in `LeanRDF.Entailment`.

## Interpretations

| Definition | Meaning (RDF 1.1 Semantics) |
|---|---|
| `SimpleInterp` | a simple interpretation: `IR`, `IP`, `IEXT`, `IS`, `IL` (§4) |
| `I.denote A t` | the value of a term, with `A` assigning blank nodes (§5.2) |
| `I.Holds A t`, `I.Satisfies g` | a triple is true; some assignment makes every triple of `g` true (§5.1, §5.2) |
| `I.InClass x c`, `I.SubClass`, `I.SubProp` | `x ∈ ICEXT(c)` and the extensions of `rdfs:subClassOf` and `rdfs:subPropertyOf` |
| `DInterp`, `RDFConditions`, `RDFSConditions` | D-interpretations and the condition tables of §7, §8 and §9, one field per row |
| `DInterp.IsRDF`, `IsRDFS` | RDF and RDFS interpretations recognizing `xsd:string` and `rdf:langString` |
| `RDFSCore I` | the conditions the rule proofs use; `IsRDFS.toCore` derives them |

## Entailment

```lean
Graph.SimpleEntails g h   -- every simple interpretation satisfying g satisfies h
Graph.DEntails g h        -- D-interpretations, D = {xsd:string, rdf:langString}
Graph.RDFEntails g h      -- RDF interpretations
Graph.RDFSEntails g h     -- RDFS interpretations
```

Blank nodes of `h` are existential: `g.RDFSEntails h` holds when every RDFS interpretation that satisfies `g` makes `h` true under *some* assignment of its blank nodes. That is why a query graph with blank nodes asks for an instance.

## Rules as data

```lean
inductive Pat | var (n : String) | const (t : Term)
structure TPat where s : Pat; p : Pat; o : Pat
structure Rule where
  name : String
  body : List TPat
  head : TPat
  guards : List Guard := []
```

A `Subst` is `String → Term`. `TPat.apply σ` instantiates a pattern. Guards are decidable side conditions with a semantic meaning (`Guard.Holds`) and a checker (`Guard.check`) proven to agree: `containerMembership v` (the variable is `rdf:_n`), `stringLiteral v` and `langLiteral v`. `Rule.RangeRestricted` (every head variable occurs in the body) and `Rule.UniqueNames` (a rule list has distinct names) are decidable and checked for the shipped lists.

The rule lists are in `LeanRDF.RDFS`:

| List | Rules |
|---|---|
| `rdfsBasicRules` | rdfs2, rdfs3, rdfs5, rdfs7, rdfs9, rdfs11 |
| `rdfsExtraRules` | rdfD2, rdfs4a, rdfs4b, rdfs6, rdfs8, rdfs10, rdfs12, rdfs13, GrdfD1 for strings and language-tagged literals, the container membership rules |
| `axiomRules` | the RDF and RDFS axiomatic triples, as rules with empty bodies |
| `rdfsRules` | all 67 |

## Derivations and soundness

```lean
inductive Derives (rules : List Rule) (g : Graph) : Triple → Prop
  | fact : t ∈ g → Derives rules g t
  | apply (r : Rule) (σ : Subst) : r ∈ rules → (∀ gd ∈ r.guards, gd.Holds σ) →
      (∀ b ∈ r.body, Derives rules g (b.apply σ)) → Derives rules g (r.head.apply σ)
```

The theorems you call:

| Theorem | Statement |
|---|---|
| `Derives.sound` | `Derives rdfsRules g t → g.RDFSEntails (Graph.singleton t)` |
| `Derives.sound_graph μ` | if every triple of `q`, with its blank nodes replaced by `μ`, is derivable, then `g.RDFSEntails q` |
| `rdfsRules_sound` | `∀ r ∈ rdfsRules, r.Sound` |
| `Rule.SoundIn C r` | `r` is sound in every interpretation satisfying `C`; `Rule.Sound` is `SoundIn RDFSCore` |
| `Derives.holdsIn` | a derivation by rules sound in `C` is true in every interpretation of `C` that makes the graph true |
| `Derives.satisfies_graph` | the same for a query graph, for any class `C` |

`holdsIn` and `satisfies_graph` are the generic forms. The OWL package and your own rule lists use them, as [Adding a rule of your own](/book/custom-rule/) shows step by step.

## Non-entailment

A soundness theorem cannot show that something is *not* entailed. `Tests.Semantics.SmallModel` builds a family of finite RDFS interpretations from a few parameters, with their conditions proven by `decide`. To prove `¬ g.RDFSEntails h`, pick parameters under which `g` holds and `h` fails. `Tests/Semantics/Vacuity.lean` does this for `subClassOf` symmetry, and `owl/OwlTests/Model.lean` extends the family to OWL.
