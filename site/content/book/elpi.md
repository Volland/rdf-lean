---
title: Elpi finds
order: 8
summary: Rules compiled to λProlog clauses, semi-naive forward chaining that terminates on cycles, and the closure read back into Lean.
---
# Elpi finds

The search side lives in a separate package, `leanrdf-elpi` (directory `elpi/`), so users of the model and the checker never build it. It uses [lean-elpi](https://github.com/Volland/lean-elpi), an implementation of the ELPI dialect of λProlog written in Lean that runs in-process.

## Why forward chaining

The natural λProlog encoding is backward: *to show `z rdf:type y`, find `x` with `x ⊑ y` and show `z rdf:type x`*. With a subclass cycle (`A ⊑ B`, `B ⊑ A`, which is legal RDFS) that loops forever, and lean-elpi has no tabling.

So LeanRDF saturates instead: apply every rule to the known triples, add what is new, repeat until nothing is new. The rules invent no terms, so this always stops.

## Clauses generated from the proven rules

There is one source of rules: the Lean list `rdfsRules`. `stepClauses` turns each into Elpi clauses — one per premise position, with that premise read from the triples new in the last round (semi-naive evaluation) and guards as Elpi goals. For rdfs9 one of the two clauses is:

```
rdf.step "rdfs9" [(rdf.t Vxxx (rdf.iri "…#subClassOf") Vyyy), (rdf.t Vzzz (rdf.iri "…#type") Vxxx)]
                 (rdf.t Vzzz (rdf.iri "…#type") Vyyy) :-
  rdf.delta (rdf.iri "…#subClassOf") Vxxx Vyyy, rdf.known (rdf.iri "…#type") Vzzz Vxxx.
```

Known triples are hypothetical clauses `rdf.known P S O`, added with λProlog's `=>` and indexed on the predicate. Rules without premises become `rdf.axiom` facts.

## The closure, read back

```lean
structure Entry where
  conclusion : Triple
  rule : String          -- "fact" for triples of the input graph
  premises : List Triple -- in the rule's body order

def saturate (rules : List Rule) (g : Graph) : Except String Closure
```

Every triple appears once, premises before conclusions. On the pet ontology, eleven triples close to 201 under all 67 rules; a subclass cycle adds exactly the reflexive triples and the inherited type.

```lean
#guard closesTo [T (ex "A") sc (ex "B"), T (ex "B") sc (ex "A"), T (ex "x") ty (ex "A")]
  [T (ex "A") sc (ex "A"), T (ex "B") sc (ex "B"), T (ex "x") ty (ex "B")]
```

Nothing here is trusted. If the clause generator or the Elpi engine had a bug, the next chapter's checker would reject the result.

## Other engines can be the searcher

Elpi is one searcher among many. oxilite, an Oxigraph-compatible SPARQL store on SQLite, answers RDFS queries by rewriting them, and its `why` tool returns the proof tree behind an inferred triple. `leanrdf-oxilite` translates each step of such a tree into a rule application, trying the 67 rules with the checker's own node check, and hands the result to the same checker. When oxilite's explanation is incomplete, Elpi's certificate is the fallback. Either way, nothing oxilite says is trusted until the checker accepts it.

