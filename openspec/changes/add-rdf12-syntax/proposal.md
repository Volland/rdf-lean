## Why

After `add-rdf12-core`, N-Triples and N-Quads read triple terms and directional literals, but Turtle and TriG still reject them. RDF 1.2 Turtle (W3C Working Draft, 23 October 2026) is where reification is written in practice: `<< s p o ~ r >>`, annotations `{| … |}` and version announcements. Statement graphs (`add-statement-graphs`) and their examples are read and written in that syntax.

## What Changes

- The Turtle statement parser accepts the RDF 1.2 Turtle grammar (§6.5): `@version`/`VERSION` directives, `LANG_DIR` literals (`"x"@ar--rtl`), triple terms `<<( s p o )>>` in object position, reified triples `<< s p o ~ r >>` as subject or object, nested reified triples, and annotations `~ r` and `{| … |}` after any object.
- Reified triples and annotations are desugared while parsing, by the rules of §7.3: one `r rdf:reifies <<( s p o )>>` per reifier, a fresh blank node when no reifier is given, the base triple asserted only by an annotation.
- Generated reifiers are named like every other generated blank node (`genidN`, avoiding document labels), including blank nodes inside triple terms.
- TriG gets all of it through the shared statement parser; reifying and annotation triples go to the graph of their statement.
- Vendor the W3C RDF 1.2 `rdf-turtle` and `rdf-trig` suites (syntax and evaluation) beside the RDF 1.1 ones and run them on every `lake test`.
- Every RDF 1.1 Turtle and TriG document parses to the same graph or dataset as before.

## Capabilities

### New Capabilities

None.

### Modified Capabilities

- `turtle`: `Turtle parsing` and `Blank nodes` cover the RDF 1.2 grammar; new requirements `Triple terms in Turtle`, `Reified triples`, `Annotations`, `Version directives` and `RDF 1.2 Turtle conformance`.
- `datasets`: `TriG` covers RDF 1.2 TriG; new requirement `RDF 1.2 TriG conformance`.

## Impact

**Roadmap:** second of four changes (RDF 1.2 → v0.2.0, then statement graphs → v0.3.0). Depends on `add-rdf12-core` being archived: it supplies `Term.triple`, `Literal.dirLang`, strict `WellFormed` over triple terms, the RDF 1.2 vocabulary and the N-Triples/N-Quads 1.2 parsers that read the suites' expected results.

**Code:** `LeanRDF/Parse/Turtle/Parser.lean` (state, `object`, `objectList`, `triples`, `directive`, `rdfLiteral`, `renameFresh`), `LeanRDF/Parse/TriG/Parser.lean` (doc comment only), `Tests/Turtle/*.lean`, `Tests/Datasets/{TriG,W3C}.lean`, `Tests/data/rdf12-turtle/`, `Tests/data/rdf12-trig/`, `scripts/w3c-index.py`, `lakefile.lean` (`testData` already covers `Tests/data`).

**lat.md sections touched:** [[decisions#TriG on the Turtle statement parser]], [[decisions#N-Triples first, native Turtle later]], [[constraints#Turtle grammar]], [[constraints#TriG grammar]], [[constraints#RFC 3986 reference resolution]], [[changes#add-turtle]], [[changes#add-datasets]].

**Binding constraints:** [[constraints#Turtle grammar]] and [[constraints#TriG grammar]] (RDF 1.1, kept: 1.1 documents must parse as before); new `Turtle 1.2 grammar`, `Turtle 1.2 reification mapping` and `TriG 1.2 grammar`.

**Requirements:** modifies [[openspec:turtle#Turtle parsing]], [[openspec:turtle#Blank nodes]], [[openspec:datasets#TriG]]; adds [[openspec:turtle#Triple terms in Turtle]], [[openspec:turtle#Reified triples]], [[openspec:turtle#Annotations]], [[openspec:turtle#Version directives]], [[openspec:turtle#RDF 1.2 Turtle conformance]], [[openspec:datasets#RDF 1.2 TriG conformance]].
