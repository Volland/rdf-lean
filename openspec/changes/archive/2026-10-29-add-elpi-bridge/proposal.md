## Why

The rules are proven sound but nothing searches with them yet. Milestone M4 adds the untrusted search: graphs encoded for Elpi, Elpi clauses generated from the proven `Rule` list, a forward-chaining saturation driver that terminates on cyclic schemas, and a readout of each derived triple's justification into Lean, which the certificate checker of M5 consumes.

## What Changes

- Add a hand-written encoding of RDF terms and triples as Elpi terms (`rdf.iri`, `rdf.bnode`, `rdf.typed`, `rdf.lang`, `rdf.t`) and its decoder.
- Add `stepClauses : Rule → Except String (List String)`, one semi-naive clause per premise position, and `program : List Rule → Except String CompiledProgram`.
- Add the driver `elpi/saturate.elpi` and `saturate : List Rule → Graph → Except String Closure`, where a closure lists each triple once with its rule and premises, premises first.
- Add golden closure tests (subclass, domain and range, subproperty, a cycle, a 12-link chain).

## Capabilities

### New Capabilities

- `elpi-bridge`: term encoding, generated rule clauses, saturation, golden closures and reflection of derivations.

### Modified Capabilities

None.

## Impact

**Milestone:** M4, in the `leanrdf-elpi` package. Depends on `add-rdfs-entailment` (archived) for `Rule`. `add-certificates` (M5) turns closures into certificates.

**Code:** `elpi/LeanRDFElpi/{Encode,Codegen,Saturate}.lean`, `elpi/LeanRDFElpi/elpi/saturate.elpi`, `elpi/BridgeTests/*.lean`, an `input_dir` for the driver in `elpi/lakefile.lean`.

**Motivating decisions** (tg.md): [[decisions#Elpi finds, Lean checks]], [[decisions#Forward-chaining saturation in Elpi]], [[decisions#Rules generated from Lean]], [[decisions#Hand-written Elpi term encoding]].

**Constraints honoured:** [[constraints#lean-elpi has no tabling]], [[constraints#cmp_term orders only numbers and strings]], [[constraints#Derived Elpi names follow the Lean names]].
