import LeanRDF

/-!
# The SHACL vocabulary

The IRIs of the SHACL Core vocabulary (SHACL, W3C Recommendation, 20 July 2017).
-/

namespace LeanRDF.Shacl.sh

/-- The SHACL namespace. -/
def ns : String := "http://www.w3.org/ns/shacl#"

/-- An IRI in the SHACL namespace. -/
def iri (n : String) : IRI := ⟨ns ++ n⟩

def NodeShape := iri "NodeShape"
def PropertyShape := iri "PropertyShape"
def targetNode := iri "targetNode"
def targetClass := iri "targetClass"
def targetSubjectsOf := iri "targetSubjectsOf"
def targetObjectsOf := iri "targetObjectsOf"
def path := iri "path"
def inversePath := iri "inversePath"
def alternativePath := iri "alternativePath"
def zeroOrMorePath := iri "zeroOrMorePath"
def oneOrMorePath := iri "oneOrMorePath"
def zeroOrOnePath := iri "zeroOrOnePath"
def deactivated := iri "deactivated"
def severity := iri "severity"
def message := iri "message"
def Violation := iri "Violation"
def Warning := iri "Warning"
def Info := iri "Info"
def IRI := iri "IRI"
def BlankNode := iri "BlankNode"
def Literal := iri "Literal"
def BlankNodeOrIRI := iri "BlankNodeOrIRI"
def BlankNodeOrLiteral := iri "BlankNodeOrLiteral"
def IRIOrLiteral := iri "IRIOrLiteral"
def ValidationReport := iri "ValidationReport"
def ValidationResult := iri "ValidationResult"
def conforms := iri "conforms"
def result := iri "result"
def focusNode := iri "focusNode"
def resultPath := iri "resultPath"
def value := iri "value"
def sourceShape := iri "sourceShape"
def sourceConstraintComponent := iri "sourceConstraintComponent"
def resultSeverity := iri "resultSeverity"
def resultMessage := iri "resultMessage"
-- parameters of the constraint components
def «class» := iri "class"
def datatype := iri "datatype"
def nodeKind := iri "nodeKind"
def minCount := iri "minCount"
def maxCount := iri "maxCount"
def minExclusive := iri "minExclusive"
def minInclusive := iri "minInclusive"
def maxExclusive := iri "maxExclusive"
def maxInclusive := iri "maxInclusive"
def minLength := iri "minLength"
def maxLength := iri "maxLength"
def pattern := iri "pattern"
def flags := iri "flags"
def languageIn := iri "languageIn"
def uniqueLang := iri "uniqueLang"
def equals := iri "equals"
def disjoint := iri "disjoint"
def lessThan := iri "lessThan"
def lessThanOrEquals := iri "lessThanOrEquals"
def «not» := iri "not"
def «and» := iri "and"
def «or» := iri "or"
def xone := iri "xone"
def node := iri "node"
def property := iri "property"
def qualifiedValueShape := iri "qualifiedValueShape"
def qualifiedMinCount := iri "qualifiedMinCount"
def qualifiedMaxCount := iri "qualifiedMaxCount"
def qualifiedValueShapesDisjoint := iri "qualifiedValueShapesDisjoint"
def closed := iri "closed"
def ignoredProperties := iri "ignoredProperties"
def hasValue := iri "hasValue"
def «in» := iri "in"

end LeanRDF.Shacl.sh
