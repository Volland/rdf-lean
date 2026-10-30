---
title: SHACL, proven in both directions
order: 12
summary: The SHACL Core semantics in Lean, and a validator proven to report a violation exactly when the data does not conform.
---
# SHACL, proven in both directions

SHACL checks data against shapes: every person has exactly one name, every price is positive, a product has only the listed properties. A validator answers with a report: either the data conforms, or a list of results, each naming a focus node, a path, a value and the constraint that failed. Each result is a positive claim that can be checked on its own. "Conforms" is a claim that *no* result exists, and no certificate can show that. So, as for SPARQL, LeanRDF proves the validator itself, in the `leanrdf-shacl` package.

## Shapes, paths and value nodes

A shape has targets (which nodes to check), a path for a property shape, and constraint components. In Lean a shape is a finite tree: `sh:node`, `sh:property`, `sh:and` and the other references hold the shapes themselves. SHACL leaves recursive shapes undefined (§3.4), and LeanRDF rejects them when it reads the shapes graph.

A property path says which nodes are reached from a focus node. The semantics is an inductive relation: `ValueNode G p x y` holds when `y` is reached from `x` by `p`, for predicate, inverse, sequence, alternative and the `*`, `+` and `?` paths. The validator computes value nodes, with a fixpoint for `*` and `+`, and a theorem says it computes exactly the relation:

```lean
theorem valueNodes_iff : y ∈ valueNodes G p x ↔ ValueNode G p x y
```

The fixpoint stops because every value node is a term of the graph or the start node, and each round adds a new one or ends.

## The semantics

`Conforms G s x` says when focus node `x` conforms to shape `s`: the shape is deactivated, or every component holds. Each component is the condition of the SHACL text. `sh:class C` holds when every value node has a type that is `C` or below it by `rdfs:subClassOf`. `sh:minCount n` holds when there are `n` different value nodes, stated with a list without duplicates. `sh:xone` holds when exactly one of the shapes conforms. A qualified shape with `sh:qualifiedValueShapesDisjoint` counts only the value nodes that conform to no sibling shape. Checks of one term (datatypes, ranges, lengths, patterns, language tags, `sh:in`) are functions shared by the semantics and the validator.

## The theorems

The validator computes results. One mutual induction over shapes and components proves that a focus node has no results exactly when it conforms. Two theorems follow:

```lean
theorem validate_conforms (G : Graph) (S : List Shape) :
    (validate G S).conforms = true ↔ DataConforms G S

theorem validate_sound (G : Graph) (S : List Shape) {r : Result}
    (h : r ∈ (validate G S).results) : Violation G r
```

The first says the report is right in both directions: "conforms" is never wrong, and neither is "does not conform". The second says every result names a shape and a component that really fails at that focus node.

## Tested against the W3C suite and oxilite

All 98 W3C SHACL Core tests pass, with an empty skip list, comparing each report result by result up to blank-node renaming. One test is a lesson in reading the specification: `sh:uniqueLang "1"^^xsd:boolean` does not turn the constraint on, because only `true` does. oxilite validates with rudof. On the recorded samples, the two agree on every result's focus node, path and component. Run `lake exe leanrdf-shacl validate --data DATA --shapes SHAPES` to get a report in Turtle.
