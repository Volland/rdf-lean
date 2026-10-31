import LeanRDF

/-! Scenarios of `certificates`: a hand-written certificate, its JSON form, the propositions the
checker yields, rejection of tampered certificates, and the CertifyingDatalog export. -/

namespace LeanRDF.Tests.CertChecks

open Vocab LeanRDF.Cert RDFS

private def ex (n : String) : Term := .iri ⟨"http://example.org/" ++ n⟩
private def T (s p o : Term) : Triple := ⟨s, p, o⟩
private def sc : Term := .iri rdfs.subClassOf
private def ty : Term := .iri rdf.type

private def g : Graph :=
  Graph.ofList [T (ex "A") sc (ex "B"), T (ex "B") sc (ex "C"), T (ex "x") ty (ex "A")]

/-- `ex:x rdf:type ex:C` by rdfs11 then rdfs9. -/
private def cert : Certificate :=
  { nodes := [ ⟨0, T (ex "A") sc (ex "B"), "fact", []⟩, ⟨1, T (ex "B") sc (ex "C"), "fact", []⟩,
               ⟨2, T (ex "x") ty (ex "A"), "fact", []⟩,
               ⟨3, T (ex "A") sc (ex "C"), "rdfs11", [0, 1]⟩,
               ⟨4, T (ex "x") ty (ex "C"), "rdfs9", [3, 2]⟩ ]
    goals := [4] }

-- @tg: verifies:: [[openspec:certificates#Checker#A valid certificate is accepted]] {level: unit}
#guard (check rdfsRules g cert).toOption == some (T (ex "x") ty (ex "C"))

-- @tg: verifies:: [[openspec:certificates#Checker soundness#An accepted certificate gives Derives]] {level: unit}
theorem x_type_C : Derives rdfsRules g (T (ex "x") ty (ex "C")) :=
  checkB_sound (c := cert) (by native_decide)

/-- The query `_:who rdf:type ex:C`, answered with `_:who ↦ ex:x`. -/
private def q : Graph := Graph.ofList [T (.bnode ⟨"who"⟩) ty (ex "C")]
private def qcert : Certificate := { cert with mapping := [(⟨"who"⟩, ex "x")] }

-- @tg: verifies:: [[openspec:certificates#Checker soundness#An accepted query certificate gives RDFS entailment]] {level: unit}
theorem g_entails_q : g.RDFSEntails q := checkQueryB_sound (c := qcert) (by native_decide)

-- @tg: verifies:: [[openspec:certificates#Certificate format#JSON round-trips]] {level: unit}
#guard (Certificate.parse qcert.render).toOption == some qcert

/-- A nested triple term with a directional literal, typed by rdfs3 through a range. -/
private def tt : Term :=
  .triple (ex "b") (ex "q") (.triple (ex "c") (ex "r") (.lit (.dirLang "x" "en" .rtl)))
private def g12 : Graph := Graph.ofList [T (ex "p") (.iri rdfs.range) (ex "C"), T (ex "a") (ex "p") tt]
private def cert12 : Certificate :=
  { nodes := [ ⟨0, T (ex "p") (.iri rdfs.range) (ex "C"), "fact", []⟩, ⟨1, T (ex "a") (ex "p") tt, "fact", []⟩,
               ⟨2, T tt ty (ex "C"), "rdfs3", [0, 1]⟩ ]
    goals := [2]
    mapping := [(⟨"t"⟩, tt)] }

-- @tg: verifies:: [[openspec:certificates#Certificate format#RDF 1.2 terms in certificates]] {level: unit}
#guard
  match Certificate.parse cert12.render with
  | .ok c => c == cert12 && (check rdfsRules g12 c).toOption == (check rdfsRules g12 cert12).toOption &&
      (check rdfsRules g12 c).toOption == some (T tt ty (ex "C"))
  | .error _ => false

/- Literal subjects (generalized triples) survive the JSON form. -/
#guard
  let c : Certificate := { nodes := [⟨0, T (.lit (.lang "v" "en")) ty (ex "R"), "fact", []⟩], goals := [0] }
  (Certificate.parse c.render).toOption == some c

private def tamper (f : List Node → List Node) : Certificate := { cert with nodes := f cert.nodes }
private def rejects (c : Certificate) : Bool := (check rdfsRules g c).toOption.isNone

-- @tg: verifies:: [[openspec:certificates#Checker#Tampered certificates are rejected]] {level: unit}
#guard rejects (tamper (·.map fun n => if n.id == 4 then { n with rule := "rdfs99" } else n))
#guard rejects (tamper (·.map fun n => if n.id == 3 then { n with premises := [0, 4] } else n))
#guard rejects (tamper (·.map fun n => if n.id == 4 then { n with conclusion := T (ex "x") ty (ex "B") } else n))
#guard rejects (tamper (·.map fun n => if n.id == 2 then { n with conclusion := T (ex "y") ty (ex "A") } else n))
#guard rejects (tamper (·.map fun n => if n.id == 4 then { n with premises := [2, 3] } else n))
#guard rejects (tamper (·.map fun n => if n.id == 1 then { n with id := 7 } else n))
#guard rejects (tamper (·.map fun n => if n.id == 3 then { n with premises := [0] } else n))
#guard (checkQuery rdfsRules g (Graph.ofList [T (ex "x") ty (ex "D")]) cert).toOption.isNone

-- @tg: verifies:: [[openspec:certificates#CertifyingDatalog export#Export has the GraphProblemInput shape]] {level: unit}
#guard
  let j := toDatalog rdfsRules g cert
  match (j.getObjValD "graph").getObjValD "edges", j.getObjValD "program" with
  -- the six Grdfs14 rules have triple-term patterns over variables, which Datalog cannot write
  | .arr edges, .arr prog => edges.size == 5 && prog.size == rdfsRules.length - 6 + 3 &&
      ((edges[4]!.getObjValD "predecessors").getArr?.toOption.map (·.size)) == some 2 &&
      ((prog[0]!.getObjValD "head").getObjValD "symbol") == .str "triple"
  | _, _ => false

end LeanRDF.Tests.CertChecks
