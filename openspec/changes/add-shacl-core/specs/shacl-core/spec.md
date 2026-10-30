## ADDED Requirements

### Requirement: Shapes
`Shacl.readShapes` SHALL read a shapes graph into node and property shapes with their targets (`sh:targetNode`, `sh:targetClass`, implicit class targets, `sh:targetSubjectsOf`, `sh:targetObjectsOf`), paths, Core constraint components, `sh:deactivated`, severities and messages, and SHALL report an error for a recursive shape or an ill-formed shape.

#### Scenario: Property shape with a path
- **WHEN** a node shape targeting `ex:Person` with a property shape on `ex:knows/ex:name` and `sh:minCount 1` is read
- **THEN** the shape has the class target, a sequence path and the `minCount` component

#### Scenario: Recursion is rejected
- **WHEN** a shape refers to itself through `sh:node`
- **THEN** reading returns an error

### Requirement: SHACL Core semantics
`Shacl.Conforms` SHALL define, for every SHACL Core component (`class`, `datatype`, `nodeKind`, `minCount`, `maxCount`, `minExclusive`, `minInclusive`, `maxExclusive`, `maxInclusive`, `minLength`, `maxLength`, `pattern`, `languageIn`, `uniqueLang`, `equals`, `disjoint`, `lessThan`, `lessThanOrEquals`, `not`, `and`, `or`, `xone`, `node`, `property`, `qualifiedValueShape` with its min, max and disjointness, `closed` with `ignoredProperties`, `hasValue` and `in`), when a focus node conforms, following SHACL §4, with value nodes given by the inductive path relation `ValueNode`.

#### Scenario: Class membership follows subClassOf
- **WHEN** `ex:a a ex:Student`, `ex:Student rdfs:subClassOf ex:Person` and `sh:class ex:Person` is checked on `ex:a`
- **THEN** `ex:a` conforms

#### Scenario: Qualified shapes disjointness
- **WHEN** a hand with `sh:qualifiedValueShapesDisjoint true` has a finger that conforms to both the thumb and the finger sibling shapes
- **THEN** that finger counts for neither, and the hand does not conform

### Requirement: Proven validator
`Shacl.validate` SHALL compute a validation report, and it SHALL be proven that the report conforms exactly when every target focus node conforms to its shape (`validate_conforms`), that every reported result is a real violation (`validate_sound`), and that computed value nodes are exactly those of `ValueNode` (`valueNodes_iff`), with no `sorry` and only Lean's standard axioms.

#### Scenario: Correctness theorems
- **WHEN** the package is built
- **THEN** the three theorems hold, and `#print axioms` shows only `propext`, `Quot.sound` and `Classical.choice`

#### Scenario: A minCount violation
- **WHEN** a person without `ex:name` is validated against `sh:minCount 1` on `ex:name`
- **THEN** the report does not conform and holds one result with that focus node, path and `sh:MinCountConstraintComponent`

### Requirement: SHACL W3C conformance
`lake test` in `shacl/` SHALL run the W3C SHACL Core tests and compare each report with the expected one up to blank-node renaming. Every test SHALL pass unless the skip list names it with a reason from `recursive`, `sparql` or `rdfs-entailment`, and a listed test that passes SHALL fail the run.

#### Scenario: Core tests
- **WHEN** the core manifests run
- **THEN** every test not on the skip list passes, and the skip list has no passing test

### Requirement: SHACL command line and oxilite comparison
`lake exe leanrdf-shacl validate --data DATA --shapes SHAPES` SHALL print the validation report in Turtle and exit with 0 when the data conforms, 1 when it does not and 3 on an input error. Recorded oxilite results for the sample shape sets SHALL agree with LeanRDF's focus nodes and components, or each difference SHALL be recorded in `tg.md`.

#### Scenario: Validate from the command line
- **WHEN** the sample data with one missing name is validated
- **THEN** the report has one result and the exit code is 1

#### Scenario: Agreement with oxilite
- **WHEN** the recorded oxilite results are compared with LeanRDF's reports
- **THEN** they agree on every sample, or the test names a documented difference
