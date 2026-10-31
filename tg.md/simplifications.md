---
type: Simplification
source: "per section: see each simplification's source:: line"
---
# Simplifications

Knowing departures of the formalization from the W3C texts. Code that implements one carries a `-- SIMPLIFICATION:` comment naming its section here.

List them with `tg cypher "MATCH (s:Simplification)-[:deviates_from]->(c) RETURN s.title, c.title"`; the `impact::` lines are for readers (tg reads typed properties from frontmatter only).

## Interpretations in universe zero

`Entails` quantifies over interpretations whose carrier lives in `Type`, not over every universe.

Soundness is unaffected, since a statement over all interpretations in `Type` is still proved for each. A future completeness proof must build its countermodels in `Type`, which the canonical small model does.

- source:: RDF 1.1 Semantics §5
- impact:: soundness-neutral
- deviates_from:: [[constraints#Simple interpretations]]

## Three recognized datatypes with abstract values

D is exactly `{xsd:string, rdf:langString, rdf:dirLangString}`, and their value spaces are abstract fields `strVal`, `langVal` and `dirLangVal` of the interpretation, not an XSD implementation.

Other datatypes are unrecognized, so their literals are interpreted only through `IL`. Value-space reasoning (`"01"^^xsd:integer` equals `"1"^^xsd:integer`) is out of scope, and so are the RDF 1.2 tests that need it or `rdf:JSON` (the expected-not-run list of the W3C semantics suite). Because the values are fields, every embedding of them is allowed, a larger class than the spec's, which only strengthens soundness. "I(aaa) is the datatype identified by aaa" (§7.1) is not expressed. The value spaces of `rdf:langString` and `rdf:dirLangString` are the tuples with lowercased tags, the only reading under which §8 and §9 agree.

Since `add-xsd-values`, `LeanRDF.Xsd` computes XSD values for queries and validation (`Literal.value?`, `XsdValue.compare?`), but entailment still does not use them: `"01"^^xsd:integer` and `"1"^^xsd:integer` are different terms to every rule and interpretation.

- source:: RDF 1.2 Semantics §7 and §8
- impact:: scope
- deviates_from:: [[constraints#RDF 1.2 RDF interpretations]]

## IRIs checked only by the N-Triples grammar

Core stores IRIs as unvalidated strings; the parser enforces the N-Triples `IRIREF` production but not full RFC 3987 conformance.

- source:: RDF 1.1 Concepts §3.2
- impact:: scope
- deviates_from:: [[constraints#IRIs are RFC 3987 IRIs]]

## Container axioms only for occurring rdf:_n

The closure adds the axiomatic triples for `rdf:_n` only for `rdf:_n` IRIs that occur as a predicate in the input graph (rules `rdfs-axiom-cmp-*`, guard `containerMembership`).

The semantics keeps the infinite `∀ n` conditions; only the derivation side is finite, which loses completeness and not soundness. IRIs `rdf:_n` occurring only as subject or object get no axioms.

- source:: RDF 1.1 Semantics §8 and §9 (axiomatic triples)
- impact:: incompleteness
- deviates_from:: [[constraints#RDF interpretations recognize two datatypes]]

## A subset of the OWL 2 RDF-Based conditions

`OWLConds` transcribes only the conditions the included rules need, and for some "iff" conditions only rule-shaped consequences of their reverse direction.

Omitted are the conditions on vocabulary no included rule uses (lists, intersections, unions, keys, negative assertions, datatypes) and, for `rdfs:domain`, `rdfs:range`, `rdfs:subPropertyOf` and `owl:equivalentProperty`, the extensional reverse directions. Every field is a consequence of the full semantics, so more interpretations qualify and every soundness theorem holds for full OWL 2 RDF-Based entailment.

- source:: OWL 2 RDF-Based Semantics §5
- impact:: soundness-neutral
- deviates_from:: [[constraints#OWL 2 RDF-Based Semantics]]

## OWL 2 RL without list rules and inconsistency rules

`owlRLRules` leaves out the OWL 2 RL rules whose premises run over an `rdf:List` (`prp-key`, `prp-spo2`, `cls-int1`, `cls-int2`, `cls-uni`, `cls-oo`, `scm-int`, `scm-uni`, `prp-adp`, `cax-adc`, `eq-diff2`, `eq-diff3`) and those that conclude `false`.

A rule with a list premise has no fixed number of body patterns, which `Rule` needs. An inconsistency rule derives no triple. The datatype rules (`dt-*`) depend on value spaces the semantics does not interpret. Fewer rules lose completeness, never soundness.

- source:: OWL 2 Profiles §4.3
- impact:: incompleteness
- deviates_from:: [[constraints#OWL 2 RL rules]]

## Recursive shapes are rejected

A shapes graph in which a shape refers to itself, directly or through other shapes, is a read error instead of being validated.

SHACL §3.4 leaves validation with recursive shapes to implementations, so rejecting them is allowed; it means some shapes graphs that other validators accept get no report. Term checks compare values only for the XSD datatypes of `LeanRDF.Xsd`, and `sh:pattern` uses LeanRDF's regex engine.

- source:: SHACL §3.4
- impact:: scope
- deviates_from:: [[constraints#SHACL Core]]

## EL rules for intersections of two or three classes

The EL rules decompose and build intersections whose `rdf:first`/`rdf:rest` list has two or three members; longer intersections, role chains, nominals and datatypes are not reasoned about.

Subsumptions that need them are missed, never wrong. The semantic condition itself holds for sequences of every length.

- source:: OWL 2 Profiles §2
- impact:: incompleteness
- deviates_from:: [[constraints#OWL 2 EL profile]]

## Language tags checked only for subtag length

A language tag is accepted when it matches the `LANG_DIR` production and every subtag has at most eight characters; it is not checked against the full BCP 47 grammar or the subtag registry.

RDF 1.2 Concepts §3.4 requires tags well-formed by BCP 47 §2.2.9. The length bound is the part the W3C RDF 1.2 N-Triples suite tests (`ntriples-langdir-bad-4`); a tag such as `en-a-b` with a lone singleton is still accepted. Soundness is unaffected: a tag only names a literal.

- source:: RDF 1.2 Concepts §3.4; BCP 47 §2.2.9
- impact:: scope
- deviates_from:: [[constraints#Directional language-tagged strings]]

## Datatype rules see asserted positions only

The GrdfD1 rules type a literal that is the object of a triple; a literal inside a triple term, or in subject or predicate position, is not typed.

RDF 1.2 Semantics §8.1.1 states rdfD1 for a literal that *appears* in a triple, triple terms included. Soundness is unaffected, since every typing the rules derive is entailed; the rule set is only less complete.

- source:: RDF 1.2 Semantics §8.1.1
- impact:: incompleteness
- deviates_from:: [[constraints#RDF 1.2 entailment patterns]]

## Proposition rules are not exported to Datalog

The CertifyingDatalog export writes ground triple-term patterns as constants and leaves out rules whose triple-term patterns have variables, since Datalog has no function terms.

The six Grdfs14 rules are such rules, so a certificate that uses them does not re-check in CertifyingDatalog. The export is a cross-check, not part of LeanRDF's trusted base; LeanRDF's own checker accepts these certificates.

- source:: CertifyingDatalog `GraphProblemInput` format; RDF 1.2 Semantics §9.2.1
- impact:: scope
- deviates_from:: [[constraints#RDF 1.2 entailment patterns]]
