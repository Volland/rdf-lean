import LeanRDFElpi

/-! Saturation with the full rule set: the new patterns, the guards in Elpi and the axioms.
Scenarios of `elpi-bridge › Rule clauses` added by `add-rdfs-full`. -/

namespace LeanRDF.BridgeTests.FullRules

open LeanRDF Bridge Vocab Cert

private def ex (n : String) : Term := .iri ⟨"http://example.org/" ++ n⟩
private def T (s p o : Term) : Triple := ⟨s, p, o⟩
private def ty : Term := .iri rdf.type

private def g : Graph := Graph.ofList
  [T (ex "s") (ex "p") (.lit (Literal.str "v")), T (ex "seq") (.iri (rdf.member 2)) (ex "a"),
   T (ex "s") (ex "q") (.lit (.lang "chat" "fr"))]

private def closure : Closure := (saturate RDFS.rdfsRules g).toOption.getD #[]

private def has (t : Triple) : Bool := (closure.find? t).isSome

-- @tg: verifies:: [[openspec:elpi-bridge#Rule clauses#Guards and axioms run in Elpi]] {level: integration}
#guard has (T (ex "p") ty (.iri rdf.Property)) && has (T (ex "s") ty (.iri rdfs.Resource)) &&
  has (T (.lit (Literal.str "v")) ty (.iri xsd.string)) &&
  has (T (.lit (.lang "chat" "fr")) ty (.iri rdf.langString)) &&
  has (T (.iri rdf.type) ty (.iri rdf.Property)) &&
  has (T (.iri xsd.string) ty (.iri rdfs.Datatype)) &&
  has (T (.iri (rdf.member 2)) ty (.iri rdfs.ContainerMembershipProperty)) &&
  has (T (ex "seq") (.iri rdfs.member) (ex "a"))

/- Guards keep the patterns precise: a language-tagged literal is not an `xsd:string`, and a
plain property is not a container membership property. -/
#guard !has (T (.lit (.lang "chat" "fr")) ty (.iri xsd.string)) &&
  !has (T (ex "p") ty (.iri rdfs.ContainerMembershipProperty))

/- Every entry of the full closure is accepted by the checker. -/
#guard
  let nodes := closure.toList.zipIdx.map fun (e, i) =>
    { id := i, conclusion := e.conclusion, rule := e.rule,
      premises := e.premises.filterMap fun p => closure.findIdx? (·.conclusion == p) : Node }
  closure.wellOrdered &&
    (checkCert RDFS.rdfsRules g { nodes, goals := [] }).toOption.map (·.size) == some closure.size

end LeanRDF.BridgeTests.FullRules
