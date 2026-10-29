## Why

Elpi now finds derivations, but nothing yet turns them into Lean propositions. Milestone M5 adds the certificate: a proof DAG that Elpi's closure is pruned into, a format to store and exchange it, and a verified checker whose acceptance yields `Derives` and RDFS entailment. Together these close the loop "Elpi finds, Lean checks".

## What Changes

- Add `Cert.Node`, `Cert.Certificate` (nodes, goal ids, instance mapping for query blank nodes) and their JSON form, with terms in N-Triples syntax; add `NTriples.parseTerm` for single terms.
- Add left-to-right pattern matching with `matchBody_spec`, and the checker `checkCert`, `check`, `checkQuery` with `check_sound` (`Derives`) and `checkQuery_sound` (RDFS entailment), plus Boolean forms for `native_decide` in tests.
- Add an exporter to the CertifyingDatalog `GraphProblemInput` schema.
- In the bridge, add `certify` (instance mapping by backtracking join, pruning, renumbering) and `entailmentCertificate`.
- Add tampering tests and an end-to-end test from N-Triples to `g.RDFSEntails q`.

## Capabilities

### New Capabilities

- `certificates`: certificate format, checker, checker soundness, CertifyingDatalog export, certificates from Elpi and the end-to-end path.

### Modified Capabilities

None. `ntriples` gains `parseTerm` without changing its requirements.

## Impact

**Milestone:** M5. Depends on `add-rdfs-entailment` and `add-elpi-bridge` (archived). `add-demo` (M6) prints these certificates.

**Code:** `LeanRDF/Cert/{Match,Check,Json,Datalog}.lean`, `LeanRDF/Parse/NTriples/Parser.lean` (`parseTerm`), `elpi/LeanRDFElpi/Certify.lean`, `Tests/Cert/*.lean`, `elpi/BridgeTests/EndToEnd.lean`.

**Motivating decisions** (tg.md): [[decisions#Own certificate format with a Datalog export]], [[decisions#Horn rules matched by the checker]], [[decisions#Graph queries with instance mappings]], [[decisions#Axiom-clean library]], [[decisions#Elpi finds, Lean checks]].

**Constraints honoured:** [[constraints#CertifyingDatalog needs Mathlib]], [[constraints#String hash is opaque to the kernel]], [[constraints#Entailed blank nodes are existential]].
