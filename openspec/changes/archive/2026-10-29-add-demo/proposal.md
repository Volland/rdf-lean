## Why

Every piece of the pipeline exists, but only tests drive it. Milestone M6 adds a runnable program that loads an ontology in N-Triples, answers an entailment query and prints a checked certificate, so the "Elpi finds, Lean checks" loop can be seen and used.

## What Changes

- Add `lake exe leanrdf-demo DATA.nt QUERY.nt [--cert OUT.json] [--datalog OUT.json]` in the `leanrdf-elpi` package, with its logic in `LeanRDF.Demo.run` so tests can drive it.
- Report the closure size, the query instance, the pruned certificate and the verdict; write the certificate JSON and the CertifyingDatalog problem on request.
- Exit `0` (entailed, checked), `1` (not derived), `2` (certificate rejected or search failed), `3` (usage, input or parse error). "Not derived" is never worded as "not entailed".
- Add an example pet ontology with three queries.

## Capabilities

### New Capabilities

- `demo`: the demo command, its exit codes and verdicts, and the example ontology.

### Modified Capabilities

None.

## Impact

**Milestone:** M6. Depends on `add-certificates` and `add-rdfs-full` (archived).

**Code:** `elpi/LeanRDFElpi/Demo.lean`, `elpi/DemoMain.lean`, `elpi/examples/*.nt`, `elpi/BridgeTests/Demo.lean`, a `lean_exe` in `elpi/lakefile.lean`, `README.md`.

**Motivating decisions** (tg.md): [[decisions#Demo never claims non-entailment]], [[decisions#Axiom-clean library]], [[decisions#Graph queries with instance mappings]].
