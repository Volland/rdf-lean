## Why

RDF 1.2 makes a triple usable as a term and adds base direction to language-tagged strings. tiramemsu and oxilite already speak RDF 1.2 reification (`~ ?r`, `rdf:reifies`), and the planned statement graphs ([[changes#add-statement-graphs]]) export to it. LeanRDF's `Term` is RDF 1.1 only, so nothing above it can state, check or certify RDF 1.2 data. This change brings the data model, the line-based syntaxes every package exchanges terms in, and the simple-interpretation layer to RDF 1.2. Every package keeps working on the new terms.

## What Changes

- **BREAKING (Lean API)** `Term` gains `triple (s p o : Term)`; `Literal` gains `dirLang (lex tag : String) (dir : Direction)` with `Direction := ltr | rtl` and datatype `rdf:dirLangString`. Every exhaustive match in core, elpi, sparql, shacl and owl gets the new cases.
- `Triple.WellFormed` follows RDF 1.2 Concepts §3.1: a triple term is allowed only as an object, and its components are well formed in turn. Decidable `Term.Basic`, `Triple.Basic`, `Graph.Basic` and `Dataset.Basic` say "no triple terms" (RDF 1.2 Basic conformance).
- Blank-node renaming and `Graph.Iso` reach inside triple terms (Concepts §3.7).
- Vocabulary: `rdf:reifies`, `rdf:dirLangString`, `rdfs:Proposition`.
- `SimpleInterp` gains the injective triple denotation `IT` (Semantics §5), and `denote` gives a triple term the value `IT(I s, I p, I o)`. Existing soundness theorems keep their statements. The small vacuity models become free triple-term extensions.
- N-Triples and N-Quads 1.2: `<<( s p o )>>` objects, `LANG_DIR` (`@en--rtl`), the `VERSION` directive, the canonical 1.2 serializer, and the W3C RDF 1.2 `rdf-n-triples` (with `c14n`) and `rdf-n-quads` suites.
- Opaque pass-through downstream:
  - Elpi encodes `rdf.tt` and `rdf.dirlang`.
  - Certificates write triple terms in N-Triples 1.2.
  - SPARQL binds and returns triple terms; `isIRI`, `isBlank` and `isLiteral` are false on them; results write and read them in the RDF 1.2 result forms.
  - SHACL never matches them by `sh:nodeKind`.
  - The oxilite bridge reads `triple` bindings.

## Capabilities

### New Capabilities

None.

### Modified Capabilities

- `rdf-core`: terms, literals, well-formedness, isomorphism and vocabulary become RDF 1.2; new requirement `RDF 1.2 Basic`.
- `ntriples`: document grammar, term syntax, canonical serialization and conformance move to RDF 1.2 N-Triples.
- `datasets`: N-Quads 1.2 and its W3C suite.
- `rdf-semantics`: simple interpretations gain `IT`.
- `elpi-bridge`: the term encoding covers triple terms and directional literals.
- `certificates`: the JSON term syntax is N-Triples 1.2.
- `sparql-algebra`: new requirement `Triple terms in evaluation`.
- `sparql-syntax`: result formats carry triple terms.
- `shacl-core`: new requirement `Triple terms in validation`.
- `oxilite-bridge`: results reading accepts triple-term bindings.

## Impact

**Roadmap:** first of four changes: add-rdf12-core → [[changes#add-rdf12-syntax]] → [[changes#add-rdf12-semantics]] (v0.2.0) → [[changes#add-statement-graphs]] (v0.3.0). Depends on `release-v0-1` and the archived P-phase changes.

**Code:**
- core: `LeanRDF/Core/{Term,Literal,Triple,Graph,Dataset,Iso,Vocab}.lean`, `LeanRDF/Semantics/{Interpretation,Entails}.lean`, `LeanRDF/Entailment/Soundness.lean`, `LeanRDF/Parse/NTriples/*`, `LeanRDF/Parse/NQuads/*`, `LeanRDF/Cert/Json.lean`
- other packages: `elpi/LeanRDFElpi/*` (encoding, `saturate.elpi`), `sparql/LeanRDFSparql/*` (expressions, result formats), `shacl/LeanRDFShacl/*` (node kinds), `elpi/OxiliteMain.lean` and the results reader
- tests: `Tests/{Core,NTriples,Datasets,Semantics,Cert}`, `Tests/data/rdf12-n-triples/`, `Tests/data/rdf12-n-quads/`

**tg.md sections touched:**
- decisions superseded: [[decisions#Generalized triples inside]], [[decisions#Literals are typed or language-tagged]]
- decisions amended: [[decisions#Single-carrier interpretations]], [[decisions#Small-model family for vacuity]], [[decisions#Hand-written Elpi term encoding]], [[decisions#Canonical N-Triples output]], [[decisions#Recursive-descent N-Triples parser]]

**Constraints binding the area:**
- unchanged: [[constraints#Simple interpretations]], [[constraints#Entailment rules use generalized RDF]]
- replaced by their RDF 1.2 versions: [[constraints#Language tag iff langString]], [[constraints#N-Triples grammar]], [[constraints#N-Quads grammar]]
- new: `RDF 1.2 triples and triple terms`, `Directional language-tagged strings`, `Triple-term denotation`, `RDF 1.2 N-Triples grammar`, `RDF 1.2 N-Quads grammar`, `RDF 1.2 conformance levels`

**Requirements:**
- modified: [[openspec:rdf-core#RDF terms]], [[openspec:rdf-core#Literal forms]], [[openspec:rdf-core#Generalized triples]], [[openspec:rdf-core#Blank node isomorphism]], [[openspec:rdf-core#Vocabulary constants]], [[openspec:ntriples#Document parsing]], [[openspec:ntriples#Term syntax]], [[openspec:ntriples#Canonical serialization]], [[openspec:ntriples#W3C conformance]], [[openspec:datasets#N-Quads]], [[openspec:datasets#Dataset W3C conformance]], [[openspec:rdf-semantics#Simple interpretations]], [[openspec:elpi-bridge#Term encoding]], [[openspec:certificates#Certificate format]], [[openspec:sparql-syntax#Result formats]], [[openspec:oxilite-bridge#Results reading]]
- added: `rdf-core#RDF 1.2 Basic`, `sparql-algebra#Triple terms in evaluation`, `shacl-core#Triple terms in validation`
