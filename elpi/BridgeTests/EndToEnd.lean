import LeanRDFElpi

/-! The whole pipeline: N-Triples, Elpi saturation, certificate, checker, and the resulting
propositions. Scenarios of `certificates › Certificates from Elpi` and `End-to-end`. -/

namespace LeanRDF.BridgeTests.EndToEnd

open LeanRDF Bridge Cert

private def data : String := "
<http://example.org/Dog> <http://www.w3.org/2000/01/rdf-schema#subClassOf> <http://example.org/Mammal> .
<http://example.org/Mammal> <http://www.w3.org/2000/01/rdf-schema#subClassOf> <http://example.org/Animal> .
<http://example.org/hasPet> <http://www.w3.org/2000/01/rdf-schema#range> <http://example.org/Dog> .
<http://example.org/alice> <http://example.org/hasPet> <http://example.org/rex> .
<http://example.org/Dog> <http://www.w3.org/2000/01/rdf-schema#label> \"dog\"@en .
"

private def query : String :=
  "_:pet <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://example.org/Animal> .\n"

private def g : Graph := (NTriples.parse data).toOption.getD ∅
private def q : Graph := (NTriples.parse query).toOption.getD ∅

/-- The certificate Elpi produces, or an empty one. -/
private def cert : Certificate := (entailmentCertificate g q).toOption.getD default

-- @tg: verifies:: [[openspec:certificates#Certificates from Elpi#Elpi certificates are accepted]] {level: e2e}
#guard g.size == 5 && (checkQuery RDFS.rdfsRules g q cert).toOption.isSome

-- @tg: verifies:: [[openspec:certificates#Certificates from Elpi#Certificates are pruned]] {level: e2e}
#guard cert.nodes.length == 7 && cert.mapping == [(⟨"pet"⟩, .iri ⟨"http://example.org/rex"⟩)]

-- @tg: verifies:: [[openspec:certificates#End-to-end#Parse, derive, check, obtain entailment]] {level: e2e}
theorem g_entails_q : g.RDFSEntails q := checkQueryB_sound (c := cert) (by native_decide)

-- @tg: verifies:: [[openspec:certificates#Certificates from Elpi#Non-derived queries have no certificate]] {level: e2e}
#guard (entailmentCertificate g ((NTriples.parse
  "<http://example.org/alice> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://example.org/Dog> .").toOption.getD ∅)).toOption.isNone

private def exT (n : String) : Term := .iri ⟨"http://example.org/" ++ n⟩
private def tt : Term := .triple (exT "b") (exT "q") (exT "c")
private def g12 : Graph := Graph.ofList
  [⟨exT "p", .iri Vocab.rdfs.range, exT "C"⟩, ⟨exT "a", exT "p", tt⟩]
private def q12 : Graph := Graph.ofList [⟨tt, .iri Vocab.rdf.type, exT "C"⟩]

-- @tg: verifies:: [[openspec:elpi-bridge#Term encoding#Rules match triple terms as opaque terms]] {level: integration}
#guard
  match entailmentCertificate g12 q12 with
  | .ok c => (checkQuery RDFS.rdfsRules g12 q12 c).toOption.isSome
  | .error _ => false

/- A certificate from Elpi that is tampered with after the fact is rejected. -/
#guard
  let bad := { cert with nodes := cert.nodes.map fun n => if n.rule == "rdfs9" then { n with rule := "rdfs11" } else n }
  (checkQuery RDFS.rdfsRules g q bad).toOption.isNone

/- The Elpi certificate survives JSON and exports to CertifyingDatalog. -/
#guard (Certificate.parse cert.render).toOption == some cert
#guard match (toDatalog RDFS.rdfsRules g cert).getObjValD "graph" |>.getObjValD "edges" with
  | .arr es => es.size == cert.nodes.length
  | _ => false

end LeanRDF.BridgeTests.EndToEnd
