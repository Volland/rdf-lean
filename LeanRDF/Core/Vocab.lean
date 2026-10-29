import LeanRDF.Core.Term

/-!
# Vocabulary

The `rdf:`, `rdfs:` and `xsd:` IRIs that the semantics and the entailment rules mention: the
RDF vocabulary of RDF 1.1 Semantics §8 (with the classes the RDFS axiomatic triples use) and
the RDFS vocabulary of §9.
-/

namespace LeanRDF.Vocab

-- @tg: implements:: [[openspec:rdf-core#Vocabulary constants]]
/-- The `rdf:` namespace (RDF 1.1 Concepts §1.4). -/
def rdfNS : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#"

/-- The `rdfs:` namespace (RDF 1.1 Concepts §1.4). -/
def rdfsNS : String := "http://www.w3.org/2000/01/rdf-schema#"

/-- The `xsd:` namespace (RDF 1.1 Concepts §1.4). -/
def xsdNS : String := "http://www.w3.org/2001/XMLSchema#"

/-! ## RDF vocabulary (RDF 1.1 Semantics §8) -/

namespace rdf

private def mk (local_ : String) : IRI := ⟨rdfNS ++ local_⟩

/-- `rdf:type` (RDF 1.1 Semantics §8). -/
def type : IRI := mk "type"
/-- `rdf:subject` (RDF 1.1 Semantics §8). -/
def subject : IRI := mk "subject"
/-- `rdf:predicate` (RDF 1.1 Semantics §8). -/
def predicate : IRI := mk "predicate"
/-- `rdf:object` (RDF 1.1 Semantics §8). -/
def object : IRI := mk "object"
/-- `rdf:first` (RDF 1.1 Semantics §8). -/
def first : IRI := mk "first"
/-- `rdf:rest` (RDF 1.1 Semantics §8). -/
def rest : IRI := mk "rest"
/-- `rdf:value` (RDF 1.1 Semantics §8). -/
def value : IRI := mk "value"
/-- `rdf:nil` (RDF 1.1 Semantics §8). -/
def nil : IRI := mk "nil"
/-- `rdf:List` (RDF 1.1 Semantics §8). -/
def List : IRI := mk "List"
/-- `rdf:langString`, the datatype of language-tagged literals (RDF 1.1 Semantics §8). -/
def langString : IRI := mk "langString"
/-- `rdf:Property` (RDF 1.1 Semantics §8). -/
def Property : IRI := mk "Property"
/-- `rdf:Statement` (RDFS axiomatic triples, RDF 1.1 Semantics §9.1). -/
def Statement : IRI := mk "Statement"
/-- `rdf:Seq` (RDFS axiomatic triples, RDF 1.1 Semantics §9.1). -/
def Seq : IRI := mk "Seq"
/-- `rdf:Bag` (RDFS axiomatic triples, RDF 1.1 Semantics §9.1). -/
def Bag : IRI := mk "Bag"
/-- `rdf:Alt` (RDFS axiomatic triples, RDF 1.1 Semantics §9.1). -/
def Alt : IRI := mk "Alt"
/-- The container membership property `rdf:_n` (RDF 1.1 Semantics §8). -/
def member (n : Nat) : IRI := mk ("_" ++ toString n)

end rdf

/-! ## RDFS vocabulary (RDF 1.1 Semantics §9) -/

namespace rdfs

private def mk (local_ : String) : IRI := ⟨rdfsNS ++ local_⟩

/-- `rdfs:domain` (RDF 1.1 Semantics §9). -/
def domain : IRI := mk "domain"
/-- `rdfs:range` (RDF 1.1 Semantics §9). -/
def range : IRI := mk "range"
/-- `rdfs:Resource` (RDF 1.1 Semantics §9). -/
def Resource : IRI := mk "Resource"
/-- `rdfs:Literal` (RDF 1.1 Semantics §9). -/
def Literal : IRI := mk "Literal"
/-- `rdfs:Datatype` (RDF 1.1 Semantics §9). -/
def Datatype : IRI := mk "Datatype"
/-- `rdfs:Class` (RDF 1.1 Semantics §9). -/
def Class : IRI := mk "Class"
/-- `rdfs:subClassOf` (RDF 1.1 Semantics §9). -/
def subClassOf : IRI := mk "subClassOf"
/-- `rdfs:subPropertyOf` (RDF 1.1 Semantics §9). -/
def subPropertyOf : IRI := mk "subPropertyOf"
/-- `rdfs:member` (RDF 1.1 Semantics §9). -/
def member : IRI := mk "member"
/-- `rdfs:Container` (RDF 1.1 Semantics §9). -/
def Container : IRI := mk "Container"
/-- `rdfs:ContainerMembershipProperty` (RDF 1.1 Semantics §9). -/
def ContainerMembershipProperty : IRI := mk "ContainerMembershipProperty"
/-- `rdfs:comment` (RDF 1.1 Semantics §9). -/
def comment : IRI := mk "comment"
/-- `rdfs:seeAlso` (RDF 1.1 Semantics §9). -/
def seeAlso : IRI := mk "seeAlso"
/-- `rdfs:isDefinedBy` (RDF 1.1 Semantics §9). -/
def isDefinedBy : IRI := mk "isDefinedBy"
/-- `rdfs:label` (RDF 1.1 Semantics §9). -/
def label : IRI := mk "label"

end rdfs

/-! ## XSD -/

namespace xsd

/-- `xsd:string`, the datatype of simple literals, recognized by every RDF interpretation
(RDF 1.1 Semantics §7 and §8). -/
def string : IRI := ⟨xsdNS ++ "string"⟩

end xsd

end LeanRDF.Vocab
