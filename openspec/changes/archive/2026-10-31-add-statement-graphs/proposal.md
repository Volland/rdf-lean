## Why

tiramemsu stores every statement as a bitemporal record with its own id, and other records can point at that id. Its paper (*When Is a Temporal Statement Store a Statement Graph?*, Zenodo 10.5281/zenodo.23335652) proves, in abstract Lean, when such a store is a Gelling–Fletcher–Schmidt Statement Graph. LeanRDF can make this concrete over real RDF terms and connect it to RDF 1.2: a proven, exact export of statement graphs to RDF 1.2 reification, the paper's export criterion and kernel over LeanRDF types, and a checker tiramemsu's own export can later be certified against. This change depends on RDF 1.2 being complete ([[changes#add-rdf12-semantics]]).

## What Changes

- New Lake package `statements/` (`leanrdf-statements`), requiring only the core.
- Bitemporal statement records: `(eid, s, p, o, txAdded, txRetracted?, validFrom?, validTo?)`. Subject and object are a term or an eid reference. Transaction time is a `Nat`, and valid time is `Int` epoch milliseconds.
- A decidable `WellFormed`:
  - strict RDF 1.2 positions;
  - no self-reference;
  - sane intervals;
  - reserved names (`urn:tiramemsu:stmt:N`, `rdf:reifies`, the four `tm:` time predicates) kept out of user content.
- Views (`now`, `asOf t`, `history`, plus an optional valid-time point) decide which records are asserted.
- Reifier export to strict RDF 1.2. Each record becomes:
  - `stmt:e rdf:reifies <<( s' p o' )>>`;
  - its `tm:` time triples;
  - its base triple `s' p o'`, when it is live in the view.
- An exact decoder, with `decode v (export v sg) = .ok sg` and `decode v g = .ok sg → export v sg = g`.
- The paper's abstract development, vendored and ported to Lean 4.35, then instantiated with LeanRDF types:
  - the export criterion (closed ∧ acyclic ⇔ a Statement Graph export exists);
  - the export kernel;
  - history closure;
  - the quoting view into generalized RDF 1.2 with its BGP theorem.
- An executable kernel, proven equal to the greatest closed acyclic subset, with `isClosed` and `isAcyclic` deciders and an executable quoting view.
- `leanrdf-sg check|export|decode|kernel|quote` over JSON-lines records, writing RDF 1.2 N-Triples.

## Capabilities

### New Capabilities

- `statement-graphs`: bitemporal statement records, well-formedness, views, the reifier export and its exact decoder, the export kernel and criterion, history closure, the quoting view, the command line and the test corpus.

### Modified Capabilities

- `release`: every package, now six, declares `0.3.0`, and `v0.3.0` is published as the statement graphs release.

The core is not modified: all four clocks are exported as `xsd:integer` literals, so no date conversion is added (design.md, *Clocks are integer literals*).

## Impact

**Roadmap:** fourth of four changes, after [[changes#add-rdf12-core]], [[changes#add-rdf12-syntax]] and [[changes#add-rdf12-semantics]]. Ships as v0.3.0.

**Code:**
- new package: `statements/` (`lakefile.lean`, `LeanRDFStatements/{Abstract,Model,View,Export,Decode,Kernel,Quote,History,Json}.lean`, `SgMain.lean`, `StatementsTests/`)
- CI: `.github/workflows/*`
- docs: `site/` (book chapter, example), `examples/`

**External:**
- tiramemsu's paper Lean at commit `55735c3` (`paper/statement-as-one-record/lean`, core Lean only, v4.34.1) is vendored, not required.
- tiramemsu's `tm export` writes only live, flat statements today. A matching `--format sg-nt12` export is a later tiramemsu change; until it exists, the goldens are marked "pending tm cross-check".

**tg.md sections touched:**
- new: `statement-graphs.md` (decisions), `concepts.md` (statement graph concepts), constraints `Statement Graph definition` and `tiramemsu record model`
- the package follows [[decisions#Layers as packages in one repository]] and [[decisions#Dependency-free core package]]

**Requirements:**
- added: `statement-graphs#Statement records`, `#Statement graph well-formedness`, `#Views`, `#Reifier export`, `#Exact decoding`, `#Export kernel`, `#Statement Graph criterion`, `#History closure`, `#Quoting view`, `#Statement graph command line`, `#Statement graph test corpus`
- depends on: [[openspec:rdf-core#Generalized triples]], [[openspec:ntriples#Canonical serialization]]
