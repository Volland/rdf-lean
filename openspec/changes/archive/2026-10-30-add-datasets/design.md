## Context

RDF 1.1 Concepts §4 defines a dataset as one default graph and zero or more named graphs, each named by an IRI or a blank node. N-Quads (W3C Recommendation, 2014) extends N-Triples with an optional graph label. TriG (W3C Recommendation, 2014) extends Turtle with graph blocks. The W3C suites live next to the Turtle and N-Triples suites at commit `d01b141`.

## Goals / Non-Goals

**Goals:** a dataset type as small and opaque as `Graph`; exact W3C conformance for both syntaxes; one parser for Turtle statements shared by Turtle and TriG.

**Non-Goals:** dataset semantics or entailment; a TriG serializer; RDF-star.

## Decisions

### A dataset is a set of quads

`Quad` is a `Triple` with `g : Option Term` (`none` is the default graph). `Dataset` wraps `Std.HashSet Quad` the way `Graph` wraps triples, and is used only through `mem_*` lemmas: `mem_defaultGraph : t ∈ d.defaultGraph ↔ ⟨t, none⟩ ∈ d`, `mem_namedGraph : t ∈ d.namedGraph n ↔ ⟨t, some n⟩ ∈ d`. An empty named graph cannot be represented; RDF 1.1 allows it, but no syntax here can produce one.

Rejected: a map from names to graphs. It keeps empty graphs, but every operation would need two lemma sets, and N-Quads is quads anyway.

### N-Quads reuses N-Triples terms

The N-Quads parser calls the N-Triples term parsers and adds an optional `graphLabel` (IRI or blank node) before the `.`. The serializer writes canonical N-Triples terms and sorts like `Graph.toList`.

### TriG on the Turtle statement parser

The Turtle parser's state gains a current graph name. `triples` statements emit quads in that graph. TriG adds `GRAPH`, `{ … }` blocks and bare labelled blocks, and forbids directives inside blocks. `Turtle.parse` keeps its signature and returns the default graph of the same machinery.

### Evaluation tests up to isomorphism

Datasets are compared by a bijection on blank nodes that maps quads to quads, extending the test-only graph isomorphism.

## Constraints

- [[constraints#N-Triples grammar]] binds N-Quads terms.
- [[constraints#Turtle grammar]] binds TriG statements.
- New: `N-Quads grammar` (N-Quads §5) and `TriG grammar` (TriG §5).

## Risks / Trade-offs

- **Refactoring the Turtle parser** risks regressions; the 313 Turtle tests run unchanged.
- **No empty named graphs.** Acceptable until a syntax or SPARQL Update needs one.
