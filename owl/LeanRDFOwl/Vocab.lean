import LeanRDF

/-!
# The OWL vocabulary

The IRIs of the OWL 2 vocabulary that the OWL 2 RL rules use (OWL 2 RDF-Based Semantics §3).
-/

namespace LeanRDF.Owl

/-- The OWL namespace. -/
def ns : String := "http://www.w3.org/2002/07/owl#"

private def o (n : String) : IRI := ⟨ns ++ n⟩

def Thing := o "Thing"
def Nothing := o "Nothing"
def «Class» := o "Class"
def Restriction := o "Restriction"
def sameAs := o "sameAs"
def equivalentClass := o "equivalentClass"
def equivalentProperty := o "equivalentProperty"
def inverseOf := o "inverseOf"
def intersectionOf := o "intersectionOf"
def FunctionalProperty := o "FunctionalProperty"
def InverseFunctionalProperty := o "InverseFunctionalProperty"
def SymmetricProperty := o "SymmetricProperty"
def TransitiveProperty := o "TransitiveProperty"
def ObjectProperty := o "ObjectProperty"
def DatatypeProperty := o "DatatypeProperty"
def AnnotationProperty := o "AnnotationProperty"
def onProperty := o "onProperty"
def onClass := o "onClass"
def someValuesFrom := o "someValuesFrom"
def allValuesFrom := o "allValuesFrom"
def hasValue := o "hasValue"
def maxCardinality := o "maxCardinality"
def maxQualifiedCardinality := o "maxQualifiedCardinality"
def deprecated := o "deprecated"
def versionInfo := o "versionInfo"
def priorVersion := o "priorVersion"
def backwardCompatibleWith := o "backwardCompatibleWith"
def incompatibleWith := o "incompatibleWith"

/-- The literal `"1"^^xsd:nonNegativeInteger` of cardinality restrictions. -/
def one : Literal := .typed "1" ⟨"http://www.w3.org/2001/XMLSchema#nonNegativeInteger"⟩

open Vocab in
/-- The axiomatic triples that `prp-ap`, `cls-thing` and `cls-nothing1` state (OWL 2 Profiles §4.3,
OWL 2 RDF-Based Semantics §5.2 and §5.5). -/
def owlAxioms : List (IRI × IRI × IRI) :=
  [(Thing, rdf.type, «Class»), (Nothing, rdf.type, «Class»)] ++
  [rdfs.label, rdfs.comment, rdfs.seeAlso, rdfs.isDefinedBy, deprecated, versionInfo, priorVersion,
   backwardCompatibleWith, incompatibleWith].map fun p => (p, rdf.type, AnnotationProperty)

end LeanRDF.Owl
