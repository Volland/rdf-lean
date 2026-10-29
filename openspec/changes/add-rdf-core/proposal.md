## Why

LeanRDF has no data model yet. Everything later (the N-Triples parser, the semantics, the derivation relation, the Elpi encoding and the certificate checker) is stated over terms, triples and graphs, so milestone M1 fixes those types first and keeps them free of dependencies.

## What Changes

- Add `IRI`, `BlankNode`, `Literal` (`typed lex dt | lang lex tag`) and `Term`, with `DecidableEq`, `Hashable`, `Ord` and `Repr`.
- Add smart constructors that enforce RDF 1.1 literal rules: `Literal.mk?` rejects `.typed _ rdf:langString`, and language tags are lowercased.
- Add generalized `Triple` (any term in any position) with a decidable `Triple.WellFormed` and a smart constructor for strict RDF 1.1 triples.
- Add an opaque `Graph` over `Std.HashSet Triple` with `empty`, `insert`, `union`, `singleton`, `ofList`, `toList` (sorted), `size` and membership lemmas.
- Add `Graph.Iso`, graph isomorphism up to blank-node renaming, as a definition.
- Add the `rdf:`, `rdfs:` and `xsd:` vocabulary constants used by the semantics and rules.

## Capabilities

### New Capabilities

- `rdf-core`: terms, literals, generalized triples, graphs and their membership API, blank-node isomorphism, and vocabulary.

### Modified Capabilities

None. This is the first change.

## Impact

**Milestone:** M1. Depends on the M0 skeleton ([[changes#M0 skeleton]]). `add-ntriples` (M2) and `add-rdfs-entailment` (M3) build on it.

**Code:** `LeanRDF/Core/{Term,Literal,Triple,Graph,Iso,Vocab}.lean`, `Tests/Core/*.lean`, in the dependency-free `leanrdf` package.

**Motivating decisions** (tg.md): [[decisions#Generalized triples inside]], [[decisions#Literals are typed or language-tagged]], [[decisions#Opaque hash-set graph]], [[decisions#Dependency-free core package]], [[decisions#No datasets in v0.x]].

**Constraints honoured:** [[constraints#Language tag iff langString]], [[constraints#IRIs are RFC 3987 IRIs]], [[constraints#Entailment rules use generalized RDF]], [[constraints#Lean toolchain 4.35]].

**Simplifications:** [[simplifications#IRIs checked only by the N-Triples grammar]].
