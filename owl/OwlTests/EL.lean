import LeanRDFOwl

/-! Scenarios of `owl-el`: the intersection condition for two classes, and a certificate using
`el-ex` checked under `owlELRules`. -/

namespace LeanRDF.Owl.Tests.EL

open Vocab LeanRDF.Cert

-- @tg: verifies:: [[openspec:owl-el#Intersection condition#Two-element intersection]] {level: unit}
/-- `ICEXT(x) = ICEXT(a) ∩ ICEXT(b)` when `x owl:intersectionOf (a b)`. -/
example {I : SimpleInterp} (hI : OWLConds I) {x l a b : I.Dom}
    (h : I.IEXT (I.IS intersectionOf) x l) (hl : ListOf I l [a, b]) (y : I.Dom) (hy : I.IR y) :
    I.InClass y x ↔ I.InClass y a ∧ I.InClass y b :=
  (intersection_two hI h hl).2.2.2 y hy

private def ex (n : String) : Term := .iri ⟨"http://example.org/el#" ++ n⟩
private def T (s p o : Term) : Triple := ⟨s, p, o⟩
private def sc : Term := .iri rdfs.subClassOf

/-- `:Hand ⊑ ∃:hasPart.:Thumb`, `:Thumb ⊑ :Finger`, and `:R2 = ∃:hasPart.:Finger`. -/
private def hands : Graph := Graph.ofList
  [T (ex "Hand") sc (ex "R1"), T (ex "R1") (.iri someValuesFrom) (ex "Thumb"),
   T (ex "R1") (.iri onProperty) (ex "hasPart"), T (ex "Thumb") sc (ex "Finger"),
   T (ex "R2") (.iri someValuesFrom) (ex "Finger"), T (ex "R2") (.iri onProperty) (ex "hasPart")]

/-- `:Hand ⊑ :R2` by `el-ex`, its premises in the rule's order. -/
private def exCert : Certificate :=
  { nodes := [ ⟨0, T (ex "Hand") sc (ex "R1"), "fact", []⟩,
               ⟨1, T (ex "R1") (.iri someValuesFrom) (ex "Thumb"), "fact", []⟩,
               ⟨2, T (ex "R1") (.iri onProperty) (ex "hasPart"), "fact", []⟩,
               ⟨3, T (ex "Thumb") sc (ex "Finger"), "fact", []⟩,
               ⟨4, T (ex "R2") (.iri someValuesFrom) (ex "Finger"), "fact", []⟩,
               ⟨5, T (ex "R2") (.iri onProperty) (ex "hasPart"), "fact", []⟩,
               ⟨6, T (ex "Hand") sc (ex "R2"), "el-ex", [0, 1, 2, 3, 4, 5]⟩ ]
    goals := [6] }

-- @tg: verifies:: [[openspec:owl-el#EL completion rules#Existential monotonicity]] {level: unit}
#guard (check owlELRules hands exCert).toOption == some (T (ex "Hand") sc (ex "R2"))
#guard (check owlRules hands exCert).toOption.isNone

/-- The subsumption is OWL-entailed. -/
theorem hand_r2 : hands.OWLEntails (Graph.singleton (T (ex "Hand") sc (ex "R2"))) :=
  Derives.el_sound (checkB_sound (c := exCert) (by native_decide))

/- 10 EL rules on top of the 127 RDFS and OWL 2 RL rules. -/
#guard elRules.length == 10 && owlELRules.length == 150

end LeanRDF.Owl.Tests.EL
