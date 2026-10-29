## Why

LeanRDF has a data model and a parser but no meaning: nothing yet says when a graph entails a triple. Milestone M3 adds the model theory of RDF 1.1 Semantics, the derivation relation over Horn rules, and the key theorem that derivations by the RDFS rules are RDFS entailments, together with evidence that the semantics is not vacuous.

## What Changes

- Add simple interpretations (one carrier, `IR` and `IP` as predicates), D-interpretations for `{rdf:langString, xsd:string}`, and the RDF and RDFS semantic conditions and axiomatic triples, one field per condition, each citing its section.
- Add simple, D-, RDF and RDFS entailment, and `RDFSCore`, the conditions the proven rules use, with `RDFSConditions.toCore`.
- Add `Pat`, `TPat`, `Guard` (no constructors yet), `Rule` with guards, range restriction and unique names, and the rules rdfs2, rdfs3, rdfs5, rdfs7, rdfs9 and rdfs11.
- Add `Derives` and the theorems `Derives.sound` and `Derives.sound_graph` (graph queries with an instance mapping for their blank nodes).
- Add the vacuity tests: a parametric small RDFS model, a model of a nontrivial graph, three non-entailments with countermodels, and one semantic hand proof per rule.

## Capabilities

### New Capabilities

- `rdf-semantics`: interpretations, satisfaction, the RDF and RDFS conditions, entailment relations, and non-vacuity.
- `rdfs-entailment`: the rule format, the RDFS rule set, the derivation relation and soundness.

### Modified Capabilities

None.

## Impact

**Milestone:** M3. Depends on `add-rdf-core` and `add-ntriples` (archived). `add-elpi-bridge` (M4) generates Elpi clauses from `Rule`; `add-certificates` (M5) checks derivations against `Derives`.

**Code:** `LeanRDF/Semantics/{Interpretation,Axioms,RDFS,Entails}.lean`, `LeanRDF/Entailment/{Rule,Rules,Derivation,Soundness}.lean`, `Tests/Semantics/*.lean`, `Tests/Entailment/*.lean`.

**Motivating decisions** (tg.md): [[decisions#Single-carrier interpretations]], [[decisions#Layered interpretations with a core]], [[decisions#Horn rules matched by the checker]], [[decisions#Graph queries with instance mappings]], [[decisions#Semantics tested against vacuity]], [[decisions#Axiom-clean library]], [[decisions#Generalized triples inside]].

**Constraints honoured:** [[constraints#Simple interpretations]], [[constraints#Entailed blank nodes are existential]], [[constraints#RDF interpretations recognize two datatypes]], [[constraints#RDFS interpretation conditions]], [[constraints#Entailment rules use generalized RDF]].

**Simplifications:** [[simplifications#Interpretations in universe zero]], [[simplifications#Two recognized datatypes with abstract values]].
