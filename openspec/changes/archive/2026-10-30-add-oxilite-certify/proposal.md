## Why

oxilite answers SPARQL queries with RDFS reasoning by query rewriting, and its `why` tool explains an inferred triple as a proof tree. Neither is checked. Phase P2 makes LeanRDF the proof layer for oxilite: every answer oxilite gives under RDFS reasoning can be checked by the verified checker, either from oxilite's own explanation or from a certificate Elpi finds.

## What Changes

- Read SPARQL 1.1 Query Results JSON into solution mappings.
- Turn a query pattern written in Turtle, with blank nodes as variables, into a `SELECT` query for oxilite, and each solution into a ground query graph.
- **Mode `elpi`:** certify each answer graph with the existing Elpi saturation and checker.
- **Mode `why`:** call oxilite's `why` tool over MCP for each answer triple and translate the proof tree into a LeanRDF certificate, matching each step against the 67 rules, then check it.
- Add `lake exe leanrdf-oxilite DATA PATTERN [--oxilite PATH] [--mode elpi|why|both] [--results FILE] [--why-dir DIR]`, which runs oxilite or reads recorded outputs and prints a verdict per answer.
- Record oxilite outputs for the pet ontology and oxilite's own reasoning scenarios as fixtures, so `lake test` needs no oxilite binary; `scripts/oxilite-fixtures.sh` regenerates them.

## Capabilities

### New Capabilities

- `oxilite-bridge`: reading oxilite's answers and explanations, and certifying them.

### Modified Capabilities

None.

## Impact

**Roadmap:** P2. Depends on `release-v0-1`. No change to oxilite is needed.

**Code:** `elpi/LeanRDFElpi/Oxilite/{Results,Pattern,Why,Translate,Run}.lean`, `elpi/OxiliteMain.lean`, `elpi/lakefile.lean`, `elpi/BridgeTests/Oxilite*.lean`, `elpi/BridgeTests/data/oxilite/`, `scripts/oxilite-fixtures.sh`.

**Motivating decisions** (tg.md): [[decisions#LeanRDF is the proof layer for oxilite]], [[decisions#Demo never claims non-entailment]], [[decisions#Graph queries with instance mappings]], [[decisions#Own certificate format with a Datalog export]].
