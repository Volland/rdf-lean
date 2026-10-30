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

## Two recognized datatypes with abstract values

D is exactly `{xsd:string, rdf:langString}`, and their value spaces are abstract fields `strVal` and `langVal` of the interpretation, not an XSD implementation.

Other datatypes are unrecognized, so their literals are interpreted only through `IL`. Value-space reasoning (`"01"^^xsd:integer` equals `"1"^^xsd:integer`) is out of scope. Because the values are fields, every embedding of them is allowed, a larger class than the spec's, which only strengthens soundness. "I(aaa) is the datatype identified by aaa" (§7.1) is not expressed. The value space of `rdf:langString` is the pairs with lowercased tags, the only reading under which §8 and §9 agree.

Since `add-xsd-values`, `LeanRDF.Xsd` computes XSD values for queries and validation (`Literal.value?`, `XsdValue.compare?`), but entailment still does not use them: `"01"^^xsd:integer` and `"1"^^xsd:integer` are different terms to every rule and interpretation.

- source:: RDF 1.1 Semantics §7 and §8
- impact:: scope
- deviates_from:: [[constraints#RDF interpretations recognize two datatypes]]

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
