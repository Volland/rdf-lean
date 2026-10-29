import LeanRDF.Core.Vocab

/-!
# Axiomatic triples

The RDF axiomatic triples (RDF 1.1 Semantics §8) and RDFS axiomatic triples (§9) without the
container membership properties `rdf:_n`, whose triples are stated for every `n` where they are
used.
-/

namespace LeanRDF.Semantics

open Vocab

/-- The RDF axiomatic triples of RDF 1.1 Semantics §8, except those for `rdf:_1`, `rdf:_2`, …
(`(subject, predicate, object)`). -/
def rdfAxioms : List (IRI × IRI × IRI) :=
  [ (rdf.type, rdf.type, rdf.Property), (rdf.subject, rdf.type, rdf.Property),
    (rdf.predicate, rdf.type, rdf.Property), (rdf.object, rdf.type, rdf.Property),
    (rdf.first, rdf.type, rdf.Property), (rdf.rest, rdf.type, rdf.Property),
    (rdf.value, rdf.type, rdf.Property), (rdf.nil, rdf.type, rdf.List) ]

/-- The RDFS axiomatic triples of RDF 1.1 Semantics §9, except those for `rdf:_1`, `rdf:_2`, …
(`(subject, predicate, object)`). -/
def rdfsAxioms : List (IRI × IRI × IRI) :=
  [ (rdf.type, rdfs.domain, rdfs.Resource), (rdfs.domain, rdfs.domain, rdf.Property),
    (rdfs.range, rdfs.domain, rdf.Property), (rdfs.subPropertyOf, rdfs.domain, rdf.Property),
    (rdfs.subClassOf, rdfs.domain, rdfs.Class), (rdf.subject, rdfs.domain, rdf.Statement),
    (rdf.predicate, rdfs.domain, rdf.Statement), (rdf.object, rdfs.domain, rdf.Statement),
    (rdfs.member, rdfs.domain, rdfs.Resource), (rdf.first, rdfs.domain, rdf.List),
    (rdf.rest, rdfs.domain, rdf.List), (rdfs.seeAlso, rdfs.domain, rdfs.Resource),
    (rdfs.isDefinedBy, rdfs.domain, rdfs.Resource), (rdfs.comment, rdfs.domain, rdfs.Resource),
    (rdfs.label, rdfs.domain, rdfs.Resource), (rdf.value, rdfs.domain, rdfs.Resource),
    (rdf.type, rdfs.range, rdfs.Class), (rdfs.domain, rdfs.range, rdfs.Class),
    (rdfs.range, rdfs.range, rdfs.Class), (rdfs.subPropertyOf, rdfs.range, rdf.Property),
    (rdfs.subClassOf, rdfs.range, rdfs.Class), (rdf.subject, rdfs.range, rdfs.Resource),
    (rdf.predicate, rdfs.range, rdfs.Resource), (rdf.object, rdfs.range, rdfs.Resource),
    (rdfs.member, rdfs.range, rdfs.Resource), (rdf.first, rdfs.range, rdfs.Resource),
    (rdf.rest, rdfs.range, rdf.List), (rdfs.seeAlso, rdfs.range, rdfs.Resource),
    (rdfs.isDefinedBy, rdfs.range, rdfs.Resource), (rdfs.comment, rdfs.range, rdfs.Literal),
    (rdfs.label, rdfs.range, rdfs.Literal), (rdf.value, rdfs.range, rdfs.Resource),
    (rdf.Alt, rdfs.subClassOf, rdfs.Container), (rdf.Bag, rdfs.subClassOf, rdfs.Container),
    (rdf.Seq, rdfs.subClassOf, rdfs.Container),
    (rdfs.ContainerMembershipProperty, rdfs.subClassOf, rdf.Property),
    (rdfs.isDefinedBy, rdfs.subPropertyOf, rdfs.seeAlso),
    (rdfs.Datatype, rdfs.subClassOf, rdfs.Class) ]

/-- The rdfs1 triples for `D = {xsd:string, rdf:langString}` (RDF 1.1 Semantics §9.2.1): every
recognized datatype IRI is an `rdfs:Datatype`. -/
def datatypeAxioms : List (IRI × IRI × IRI) :=
  [(xsd.string, rdf.type, rdfs.Datatype), (rdf.langString, rdf.type, rdfs.Datatype)]

end LeanRDF.Semantics
