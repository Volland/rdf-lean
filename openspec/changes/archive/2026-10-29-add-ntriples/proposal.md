## Why

LeanRDF can represent graphs but cannot read or write them. The end-to-end path (parse, saturate, check) and the demo start from N-Triples files, and certificates reuse the N-Triples term syntax, so milestone M2 adds a native N-Triples parser and serializer, tested against the W3C suite.

## What Changes

- Add a native N-Triples parser `NTriples.parse : String → Except ParseError Graph` following the RDF 1.1 N-Triples grammar, with line and column in every error.
- Add a canonical serializer `Graph.toNTriples : Graph → Except String String` (sorted, one triple per line, canonical escapes) and a public `Term.toNTriples` for reuse by certificates.
- Vendor the W3C `rdf-n-triples` test suite (41 positive, 29 negative syntax tests) under `Tests/data/` with a generated index, and run it on every `lake test`.
- Check round-trip stability on every positive test.

## Capabilities

### New Capabilities

- `ntriples`: N-Triples parsing, term syntax, canonical serialization, W3C conformance and round-trip stability.

### Modified Capabilities

None.

## Impact

**Milestone:** M2. Depends on `add-rdf-core` ([[changes#add-rdf-core]], archived). `add-certificates` reuses `Term.toNTriples` and the term parser.

**Code:** `LeanRDF/Parse/NTriples/{Chars,Parser,Serializer}.lean`, `Tests/NTriples/*.lean`, `Tests/data/rdf-n-triples/`, `scripts/w3c-ntriples-index.py`, and an `input_dir` in `lakefile.lean` so test data changes rebuild the tests.

**Motivating decisions** (tg.md): [[decisions#N-Triples first, native Turtle later]], [[decisions#Literals are typed or language-tagged]], [[decisions#Opaque hash-set graph]], [[decisions#Generalized triples inside]], [[decisions#Dependency-free core package]].

**Constraints honoured:** [[constraints#Language tag iff langString]], [[constraints#IRIs are RFC 3987 IRIs]], [[constraints#N-Triples grammar]], [[constraints#W3C tests reject colons in blank-node labels]].

**Simplifications:** [[simplifications#IRIs checked only by the N-Triples grammar]].
