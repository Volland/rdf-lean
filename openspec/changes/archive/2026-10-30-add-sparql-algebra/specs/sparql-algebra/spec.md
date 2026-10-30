## ADDED Requirements

### Requirement: Algebra
`leanrdf-sparql` SHALL define the SPARQL 1.1 algebra of §18.2 for BGP, Join, LeftJoin, Filter, Union, Graph, Extend, Minus, Table, ToList, OrderBy, Project, Distinct, Reduced and Slice, over the `Dataset` of the core package, with solution mappings as sorted association lists.

#### Scenario: Mapping operations
- **WHEN** `{x ↦ a}` and `{x ↦ a, y ↦ b}` are tested for compatibility and merged
- **THEN** they are compatible and the merge is `{x ↦ a, y ↦ b}`, and `{x ↦ a}` is incompatible with `{x ↦ c}`

### Requirement: Algebra semantics
`Spec.eval` SHALL transcribe the evaluation semantics of §18.5 operator by operator, on solution multisets represented as lists up to permutation, with the BGP semantics given declaratively over the active graph's terms and blank nodes treated as hidden variables.

#### Scenario: OPTIONAL keeps unmatched mappings
- **WHEN** `LeftJoin(BGP(?x a :P), BGP(?x :name ?n), true)` is evaluated on a graph where `:a` and `:b` are persons and only `:a` has a name
- **THEN** the result is `{x ↦ a, n ↦ "A"}` and `{x ↦ b}`

#### Scenario: MINUS without shared variables removes nothing
- **WHEN** `Minus(BGP(?x a :P), BGP(?y a :Q))` is evaluated
- **THEN** the result equals the left side

#### Scenario: Blank nodes in a BGP are hidden variables
- **WHEN** `BGP(?x :knows _:b)` is evaluated on a graph where `:a` knows two people
- **THEN** the result holds `{x ↦ a}` twice

### Requirement: Proven evaluator
`Eval.evalN` SHALL evaluate BGPs by matching triple patterns one at a time, and `Eval.runQuery` SHALL order solutions by a stable sort. It SHALL be proven that `Eval.evalN n D G P` is a permutation of `Spec.evalN n D G P` for every fuel, dataset, active graph and pattern (`EXISTS` included), that ORDER BY returns a sorted list, and that every answer of `Eval.runQuery` satisfies `Spec.Answer`, with no `sorry` and no axiom beyond Lean's standard three.

#### Scenario: Correctness theorem
- **WHEN** the package is built
- **THEN** `eval_perm_spec`, `orderBy_sorted` and `runQuery_answer` are theorems, and `#print axioms` shows only `propext`, `Quot.sound` and `Classical.choice`

#### Scenario: Evaluator and specification agree on small graphs
- **WHEN** both are run on every pattern of the scenario tests
- **THEN** their results are permutations of each other

### Requirement: Expressions
`Expr.eval` SHALL implement SPARQL 1.1 §17 expressions with errors: the logical connectives by the §17.2 tables, `=`, `!=`, `<`, `<=`, `>`, `>=` by RDF term equality and `XsdValue.compare?`, `+`, `-`, `*`, `/` with numeric promotion, `BOUND`, `IF`, `COALESCE`, `IN`, `NOT IN`, `sameTerm`, `isIRI`, `isBlank`, `isLiteral`, `isNumeric`, `STR`, `LANG`, `DATATYPE`, `IRI`, `BNODE`, `STRDT`, `STRLANG`, `langMatches`, `STRLEN`, `SUBSTR`, `UCASE`, `LCASE`, `STRSTARTS`, `STRENDS`, `CONTAINS`, `STRBEFORE`, `STRAFTER`, `CONCAT`, `ENCODE_FOR_URI`, `REGEX`, `REPLACE`, `ABS`, `ROUND`, `CEIL`, `FLOOR`, the XSD casts, and `EXISTS`/`NOT EXISTS`.

#### Scenario: Errors in OR
- **WHEN** `(?unbound = 1) || true` is evaluated
- **THEN** the result is `true`

#### Scenario: Numeric promotion in FILTER
- **WHEN** `FILTER(?v > 1.5)` is applied to `"2"^^xsd:integer` and `"1"^^xsd:integer`
- **THEN** only the first passes

### Requirement: Regular expressions
`LeanRDF.Text.Regex` SHALL match the XPath regular expressions used by `REGEX`, `REPLACE` and `sh:pattern`: character classes and escapes, quantifiers with bounds, groups, alternation, anchors, and the flags `i`, `s`, `m` and `x`.

#### Scenario: Case-insensitive match
- **WHEN** `REGEX("Alice", "^ali", "i")` is evaluated
- **THEN** the result is `true`

#### Scenario: Bounded quantifiers
- **WHEN** `[0-9]{3}-[0-9]{2}` is matched against `123-45` and `12-345`
- **THEN** the first matches and the second does not
