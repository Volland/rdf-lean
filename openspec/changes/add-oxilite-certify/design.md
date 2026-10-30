## Context

oxilite (github.com/Volland/oxilite, v0.9) is an Oxigraph-compatible SPARQL store on SQLite. `oxilite query --location DB --reasoning rdfs --query Q` answers with SPARQL JSON results. `oxilite mcp --root PROJECT` serves tools over MCP (JSON-RPC 2.0 on standard input and output). Its `why` tool takes a subject, predicate and object and returns a JSON tree. Each node has a `triple` (`s`, `p`, `o` in RDF/JS term JSON) and a `status` (`asserted`, `inferred` or `absent`). An `inferred` node also has a `rule` (an OWL 2 RL template name such as `cax-sco (subclass)` or `prp-rng (range)`), a `producer` and `premises`, or a `note` when no template matched or the depth limit (8) was reached.

## Goals / Non-Goals

**Goals:** check oxilite's RDFS answers without trusting oxilite; use its explanations when they translate; never report an unchecked answer as certified.

**Non-Goals:** OWL templates (`cax-eqc`, `prp-inv`, `prp-trp`, `eq-*`), which wait for `add-owl-rl`; changing oxilite; arbitrary SPARQL (the pattern is a BGP).

## Decisions

### The query is a pattern, not SPARQL

The user writes the query as a Turtle graph whose blank nodes are the variables, as the demo already does. LeanRDF renders it as `SELECT * WHERE { … }`, with each blank node `_:x` written as `?x`. Each JSON solution μ gives the ground graph μ(q). No SPARQL parser is needed until `add-sparql-syntax`. A solution that binds a blank node keeps it as a blank node, which stays existential in μ(q).

### Two modes, one checker

- `elpi`: saturate the data once, then certify each μ(q) with `Certify` and `checkQueryB`. Verdicts are those of the demo: `certified`, `not derived`, `rejected`.
- `why`: for each triple of μ(q), translate oxilite's tree into certificate nodes. An `asserted` node becomes `fact`. An `inferred` node becomes one rule application. The translator tries every rule in `rdfsRules` whose head matches the conclusion and whose body, in some order, matches the premises, preferring the rule that the name map suggests (`cax-sco` → `rdfs9`, `prp-dom` → `rdfs2`, `prp-rng` → `rdfs3`, `prp-spo1` → `rdfs7`, `scm-sco` → `rdfs11`). Nodes are shared by conclusion. A node with a `note`, an `absent` node or an untranslatable step makes that answer `untranslated`, never `certified`. The whole certificate then goes through `check`.

`both` runs the two modes and reports each. The overall verdict for an answer is `certified` if either mode's certificate is accepted.

### Running oxilite is untrusted plumbing

`Run.lean` writes a temporary store and project (`oxilite.toml` with `reasoning = "rdfs"` and one graph holding the data file), runs `oxilite load`, `oxilite query` and `oxilite mcp` with `IO.Process`, and parses their output. Every failure is an input error (exit code 3). With `--results` and `--why-dir`, recorded outputs replace the process calls; the tests use only these.

### Exit codes

`0`: every answer certified. `1`: some answer not derived or untranslated, none rejected. `2`: a certificate was rejected by the checker (a bug on the untrusted side, oxilite's or LeanRDF's). `3`: input, process or parse error.

## Constraints

- [[constraints#Lean toolchain 4.35]].
- New: `oxilite why trees` (oxilite `crates/oxilite-cli/src/studio/why.rs`, v0.9), binding the JSON shape and the template names.
- New: `SPARQL results JSON` (SPARQL 1.1 Query Results JSON Format), binding the results reader.

## Risks / Trade-offs

- **Template names may change in oxilite.** The name map is only a preference: matching by structure still finds the rule.
- **The `why` depth limit** cuts long chains. Those answers fall back to mode `elpi` in `both`.
- **oxilite's RDFS regime is narrower than RDFS 1.1** (no axiomatic triples, for instance). That can only make it return fewer answers, which a certificate cannot detect: certification proves soundness, not completeness.
