import LeanRDF

/-! Scenarios of the RDF 1.2 additions to `rdfs-entailment` and `certificates`: triple-term
patterns, the proposition rules (generalized rdfs14 and rdfs14a), and the simple and RDF regimes
with their checker theorems. -/

namespace LeanRDF.Tests.Propositions

open Vocab RDFS LeanRDF.Cert

private def ex (n : String) : Term := .iri ⟨"http://example.org/" ++ n⟩
private def T (s p o : Term) : Triple := ⟨s, p, o⟩
private def ty : Term := .iri rdf.type
private def prop : Term := .iri rdfs.Proposition
private def reifies : Term := .iri rdf.reifies
private def tt (s p o : Term) : Term := .triple s p o

/-! ## Triple-term patterns -/

private def pat : TPat := ⟨.var "x", .var "a", .triple (.var "s") (.var "p") (.var "o")⟩

-- @tg: verifies:: [[openspec:rdfs-entailment#Rule format#Triple-term patterns match inside triple terms]] {level: unit}
#guard
  let t := T (ex "r") reifies (tt (ex "a") (ex "p") (ex "b"))
  match matchTPat [] pat t with
  | some σ => σ.find? "s" == some (ex "a") && σ.find? "p" == some (ex "p") &&
      σ.find? "o" == some (ex "b") && pat.apply σ.toSubst == t
  | none => false

-- @tg: verifies:: [[openspec:rdfs-entailment#Rule format#Triple-term patterns do not match other terms]] {level: unit}
#guard (matchTPat [] pat (T (ex "r") (ex "q") (ex "b"))).isNone

/-! ## Proposition rules -/

private def g1 : Graph := Graph.ofList [T (ex "r") reifies (tt (ex "a") (ex "p") (ex "b"))]

private def cert1 : Certificate :=
  { nodes := [⟨0, T (ex "r") reifies (tt (ex "a") (ex "p") (ex "b")), "fact", []⟩,
              ⟨1, T (tt (ex "a") (ex "p") (ex "b")) ty prop, "Grdfs14-o", [0]⟩]
    goals := [1] }

-- @tg: verifies:: [[openspec:rdfs-entailment#Proposition rules#A reified triple term is a proposition]] {level: unit}
theorem reified_is_proposition : Derives rdfsRules g1 (T (tt (ex "a") (ex "p") (ex "b")) ty prop) :=
  checkB_sound (c := cert1) (by native_decide)

private def g2 : Graph :=
  Graph.ofList [T (ex "r") reifies (tt (ex "a") (ex "p") (tt (ex "c") (ex "q") (ex "d")))]

private def cert2 : Certificate :=
  { nodes := [⟨0, T (ex "r") reifies (tt (ex "a") (ex "p") (tt (ex "c") (ex "q") (ex "d"))), "fact", []⟩,
              ⟨1, T (tt (ex "a") (ex "p") (tt (ex "c") (ex "q") (ex "d"))) ty prop, "Grdfs14-o", [0]⟩,
              ⟨2, T (tt (ex "c") (ex "q") (ex "d")) ty prop, "Grdfs14-in-o", [1]⟩]
    goals := [2] }

-- @tg: verifies:: [[openspec:rdfs-entailment#Proposition rules#Nested triple terms are propositions]] {level: unit}
theorem nested_is_proposition : Derives rdfsRules g2 (T (tt (ex "c") (ex "q") (ex "d")) ty prop) :=
  checkB_sound (c := cert2) (by native_decide)

/-- The rdfs14 query `_:n rdf:type rdfs:Proposition . ex:r rdf:reifies _:n .` -/
private def q1 : Graph := Graph.ofList [T (.bnode ⟨"n"⟩) ty prop, T (ex "r") reifies (.bnode ⟨"n"⟩)]

private def qcert1 : Certificate := { cert1 with goals := [1, 0], mapping := [(⟨"n"⟩, tt (ex "a") (ex "p") (ex "b"))] }

-- @tg: verifies:: [[openspec:rdfs-entailment#Proposition rules#rdfs14 as a graph query]] {level: unit}
theorem rdfs14_query : g1.RDFSEntails q1 := checkQueryB_sound (c := qcert1) (by native_decide)

-- @tg: verifies:: [[openspec:certificates#Checker soundness#A proposition certificate gives RDFS entailment]] {level: unit}
example : g1.RDFSEntails q1 := checkQuery_sound (c := qcert1) (checkQueryB_ok (by native_decide))

private def witness : Term := tt (.iri rdf.type) (.iri rdf.type) (.iri rdf.Property)

private def cert14a : Certificate :=
  { nodes := [⟨0, T witness ty prop, "rdfs14a", []⟩], goals := [0], mapping := [(⟨"n"⟩, witness)] }

-- @tg: verifies:: [[openspec:rdfs-entailment#Proposition rules#rdfs14a holds for the empty graph]] {level: unit}
theorem rdfs14a_empty : (∅ : Graph).RDFSEntails (Graph.ofList [T (.bnode ⟨"n"⟩) ty prop]) :=
  checkQueryB_sound (c := cert14a) (by native_decide)

/-! ## Regimes -/

private def g3 : Graph := Graph.ofList [T (ex "a") (ex "p") (ex "b")]

/-- Well-formedness of a concrete query, from a Boolean check. -/
private theorem wf_of_all {q : Graph} (h : (q.toList.all fun t => decide t.WellFormed) = true) :
    ∀ t ∈ q, t.WellFormed := fun t ht =>
  of_decide_eq_true (List.all_eq_true.1 h t (Graph.mem_toList.2 ht))

private def q3 : Graph := Graph.ofList [T (.bnode ⟨"x"⟩) (ex "p") (ex "b")]

-- @tg: verifies:: [[openspec:rdfs-entailment#Regime rule sets#Simple entailment of an instance]] {level: unit}
theorem simple_instance : g3.SimpleEntails q3 :=
  Derives.sound_graph_simple (fun _ => ex "a") (wf_of_all (by native_decide)) fun t ht => by
    rw [q3, Graph.mem_ofList, List.mem_singleton] at ht
    subst ht
    rw [g3, Graph.mem_ofList]; decide

private def certD2 : Certificate :=
  { nodes := [⟨0, T (ex "a") (ex "p") (ex "b"), "fact", []⟩, ⟨1, T (ex "p") ty (.iri rdf.Property), "rdfD2", [0]⟩]
    goals := [1] }

-- @tg: verifies:: [[openspec:rdfs-entailment#Regime rule sets#RDF entailment by rdfD2]] {level: unit}
theorem rdf_rdfD2 : g3.RDFEntails (Graph.ofList [T (ex "p") ty (.iri rdf.Property)]) :=
  checkQuery_sound_rdf (c := certD2) (checkQueryB_ok (by native_decide))

-- @tg: verifies:: [[openspec:rdfs-entailment#Regime rule sets#RDF rules do not use RDFS conditions]] {level: unit}
#guard
  let iris (p : Pat) : List IRI := match p with | .const (.iri i) => [i] | _ => []
  rdfRules.all fun r => (r.head :: r.body).all fun b =>
    ([b.s, b.p, b.o].flatMap iris).all fun i => !i.val.startsWith rdfsNS

private def certSimple : Certificate :=
  { nodes := [⟨0, T (ex "a") (ex "p") (ex "b"), "fact", []⟩], goals := [0], mapping := [(⟨"x"⟩, ex "a")] }

-- @tg: verifies:: [[openspec:certificates#Checker soundness#Regime certificates give their entailment]] {level: unit}
example : g3.SimpleEntails q3 ∧ g3.RDFEntails (Graph.ofList [T (ex "p") ty (.iri rdf.Property)]) :=
  ⟨checkQuery_sound_simple (wf_of_all (by native_decide)) (c := certSimple) (checkQueryB_ok (by native_decide)),
   rdf_rdfD2⟩

end LeanRDF.Tests.Propositions
