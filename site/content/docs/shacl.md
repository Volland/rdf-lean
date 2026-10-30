---
title: SHACL
order: 10
summary: Reading shapes, validating, the report, the theorems that turn a report into a fact about the data, and the supported constraint components.
---
# SHACL

`leanrdf-shacl` implements SHACL Core: a shapes reader, the semantics as Lean propositions, a validator, and proofs that the validator computes the semantics in both directions. Book chapter [14](/book/shacl/) explains the proofs. The snippets are compiled from `shacl/ShaclTests/Examples.lean`.

## Validate from Lean

```lean
private def shapes : List Shape := (readShapes (ttl "
  :PersonShape a sh:NodeShape ; sh:targetClass :Person ;
    sh:property [ sh:path :name ; sh:minCount 1 ; sh:maxCount 1 ; sh:datatype xsd:string ] ;
    sh:property [ sh:path :knows ; sh:class :Person ] .")).toOption.getD []

private def good : Graph := ttl ":ada a :Person ; :name \"Ada\" ; :knows :alan .
  :alan a :Person ; :name \"Alan\" ."

private def bad : Graph := ttl ":ada a :Person ; :name \"Ada\", \"A. Lovelace\" ; :knows :rex .
  :rex a :Dog ."

#guard (validate good shapes).conforms
#guard (validate bad shapes).results.map (·.component.val) ==
  ["http://www.w3.org/ns/shacl#MaxCountConstraintComponent",
   "http://www.w3.org/ns/shacl#ClassConstraintComponent"]

theorem good_conforms : DataConforms good shapes :=
  (validate_conforms good shapes).1 (by native_decide)

theorem bad_does_not_conform : ¬ DataConforms bad shapes := fun h =>
  absurd ((validate_conforms bad shapes).2 h) (by native_decide)

example : ∀ r ∈ (validate bad shapes).results, Violation bad r := fun _ h => validate_sound _ _ h
```

## The API

| Definition | Meaning |
|---|---|
| `readShapes sg : Except String (List Shape)` | the shapes of a shapes graph that have targets, with the shapes they refer to |
| `validate G S : Report` | `conforms : Bool` and `results : List Result` |
| `Result` | `focus`, `path`, `value`, `source` (the shape), `component`, `severity`, `messages` |
| `Report.toTurtle`, `readReport` | write a report in Turtle (§3.6); read one back, as the W3C tests do |
| `Conforms G s x` | focus node `x` conforms to shape `s` (the semantics) |
| `DataConforms G S` | every focus node of every shape conforms |
| `Violation G r` | the result names a shape and a component that fail at its focus node |
| `ValueNode G p x y`, `valueNodes` | the value nodes of a path, as a relation and computed |

| Theorem | Statement |
|---|---|
| `valueNodes_iff` | `y ∈ valueNodes G p x ↔ ValueNode G p x y` |
| `results_nil` | a focus node has no results exactly when it conforms |
| `validate_conforms` | `(validate G S).conforms = true ↔ DataConforms G S` |
| `validate_sound` | every result of the report is a `Violation` |

When the shapes and the data come from different files, rename the shapes graph's blank nodes apart first (`renameShapes`, as the command line does), so that the two graphs' blank nodes do not collide.

## Supported

- **Targets:** `sh:targetNode`, `sh:targetClass`, implicit class targets (a shape that is also an `rdfs:Class`), `sh:targetSubjectsOf`, `sh:targetObjectsOf`.
- **Paths:** predicate, sequence, `sh:alternativePath`, `sh:inversePath`, `sh:zeroOrMorePath`, `sh:oneOrMorePath`, `sh:zeroOrOnePath`.
- **Value type:** `sh:class`, `sh:datatype`, `sh:nodeKind`.
- **Cardinality:** `sh:minCount`, `sh:maxCount`.
- **Value range:** `sh:minExclusive`, `sh:minInclusive`, `sh:maxExclusive`, `sh:maxInclusive`, compared as XSD values.
- **String:** `sh:minLength`, `sh:maxLength`, `sh:pattern` with `sh:flags`, `sh:languageIn`, `sh:uniqueLang`.
- **Property pairs:** `sh:equals`, `sh:disjoint`, `sh:lessThan`, `sh:lessThanOrEquals`.
- **Logic:** `sh:not`, `sh:and`, `sh:or`, `sh:xone`.
- **Shapes:** `sh:node`, `sh:property`, `sh:qualifiedValueShape` with `sh:qualifiedMinCount`, `sh:qualifiedMaxCount` and `sh:qualifiedValueShapesDisjoint`.
- **Other:** `sh:closed` with `sh:ignoredProperties`, `sh:hasValue`, `sh:in`, `sh:deactivated`, `sh:severity`, `sh:message`.

All 98 W3C SHACL Core tests pass, and the skip list is empty.

## Not supported

- **Recursive shapes**, which refer to themselves directly or through other shapes. They are rejected when read, because §3.4 leaves their validation undefined.
- **SHACL-SPARQL** (`sh:sparql`, SPARQL-based constraint components) and SHACL Advanced Features.
- **Boolean parameters** are on only for the literal `"true"^^xsd:boolean`, as the W3C test `uniqueLang-002` requires. `"1"^^xsd:boolean` does not count.

## Comparing with oxilite

oxilite validates with rudof. `scripts/shacl-oxilite-fixtures.sh` records oxilite's reports on the samples in `shacl/ShaclTests/data/oxilite/`, and `ShaclTests/Oxilite.lean` checks that both engines report the same results: focus node, path and component, result by result.
