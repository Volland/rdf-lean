## Context

SHACL (W3C Recommendation, 2017) §2 to §4 define shapes, targets, focus nodes, property paths and the Core constraint components. §3.4 leaves validation with recursive shapes undefined. The W3C test suite (`w3c/data-shapes`, `data-shapes-test-suite/tests/core/`) gives each test as a Turtle manifest entry with a data graph, a shapes graph and an expected validation report.

## Goals / Non-Goals

**Goals:** all Core constraint components; a validator with a correctness theorem; the Core tests passing for everything supported.

**Non-Goals:** SHACL-SPARQL; SHACL Advanced Features; recursive shapes; validating with an RDFS or OWL closure (oxilite's default) unless the closure is given as data.

## Decisions

### Shapes are a non-recursive inductive

`Shape` holds its targets, its path (for property shapes), its constraint components, `sh:deactivated`, severity and messages. Shape references (`sh:node`, `sh:property`, `sh:and`, `sh:or`, `sh:not`, `sh:xone`, `sh:qualifiedValueShape`) are resolved while reading. A cycle is a read error, as §3.4 allows. The shape graph is therefore a well-founded tree, and both the semantics and the validator recurse on it structurally.

### Paths by reachability

`Path` covers predicate, inverse, sequence, alternative, zero-or-more, one-or-more and zero-or-one paths. The semantics defines `ValueNode G p x y` as an inductive relation. The validator computes value nodes by breadth-first search to a fixpoint. A theorem proves that the computed list holds exactly the `y` with `ValueNode G p x y`.

### Semantics and validator

`Conforms G s x` is a `Prop`: per component, the condition of the SHACL text, for instance `sh:minCount n` means at least `n` value nodes. `validate G shapes : Report` computes results. Two theorems:

- `validate_conforms`: `(validate G S).conforms = true` iff every target focus node of every shape satisfies `Conforms`.
- `validate_sound`: every result in the report names a focus node, a shape and a component whose condition fails.

Value comparisons use `XsdValue.compare?`; `sh:pattern` uses `LeanRDF.Text.Regex`.

### Tests as reports up to blank nodes

Each W3C test's expected report is compared with LeanRDF's, as sets of results over (focus node, path, value, source shape, constraint component, severity), up to blank-node renaming. `skip.txt` names each skipped test with a reason from a fixed set (`recursive`, `sparql`, `rdfs-entailment`). As for SPARQL, a skipped test that passes fails the run.

### oxilite comparison

`oxilite check` on a project with shapes reports SHACL results. Fixtures record its results for a few sample shape sets. A test compares the focus nodes and components with LeanRDF's report. A mismatch is recorded as a known difference in `tg.md`, not hidden.

## Constraints

- New: `SHACL Core` (SHACL §2 to §4), binding the semantics and the components.
- [[constraints#Turtle grammar]]: shapes and test manifests are Turtle.

## Risks / Trade-offs

- **`sh:qualifiedValueShapesDisjoint`** compares sibling shapes and is the hardest component to state; it is in scope and gets its own scenario.
- **oxilite validates over its reasoning closure by default**, so differences can come from entailment, not validation. Fixtures are recorded with reasoning off.
