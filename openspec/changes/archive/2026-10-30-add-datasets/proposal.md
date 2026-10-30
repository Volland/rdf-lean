## Why

SPARQL queries datasets, not graphs: `GRAPH`, `FROM` and `FROM NAMED` need named graphs, and oxilite stores quads and scopes reasoning per ontology graph. Phase P1 lifts [[decisions#No datasets in v0.x]] and adds RDF 1.1 datasets with their two standard syntaxes.

## What Changes

- Add `Quad` and an opaque `Dataset` (a finite set of quads), used through membership lemmas, with `defaultGraph`, `namedGraph`, `graphNames`, `ofGraph` and sorted `toList`.
- Add a native N-Quads parser and canonical serializer, sharing the N-Triples term rules.
- Add a native TriG parser built on the Turtle parser: `GRAPH`, labelled and unlabelled graph blocks, and blank-node-labelled graphs.
- Vendor the W3C `rdf-n-quads` and `rdf-trig` suites (commit `d01b141`) and run them on every `lake test`, comparing TriG evaluation results with the expected N-Quads up to blank-node renaming.

## Capabilities

### New Capabilities

- `datasets`: quads, datasets, N-Quads and TriG.

### Modified Capabilities

None. Graph entailment is unchanged: RDF 1.1 gives datasets no model theory, and none is added.

## Impact

**Roadmap:** P1, first half. Depends on `release-v0-1`.

**Code:** `LeanRDF/Core/Dataset.lean`, `LeanRDF/Parse/NQuads/*.lean`, `LeanRDF/Parse/TriG/Parser.lean`, `LeanRDF/Parse/Turtle/Parser.lean` (shared statement parsing), `Tests/Datasets/*.lean`, `Tests/data/rdf-n-quads/`, `Tests/data/rdf-trig/`, `scripts/w3c-index.py`.

**Motivating decisions** (tg.md): [[decisions#No datasets in v0.x]] (superseded), [[decisions#Recursive-descent N-Triples parser]], [[decisions#N-Triples first, native Turtle later]].

**Constraints honoured:** [[constraints#N-Triples grammar]], [[constraints#Turtle grammar]].
