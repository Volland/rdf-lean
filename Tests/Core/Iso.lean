import LeanRDF

/-! Scenarios of `rdf-core › Blank node isomorphism`. -/

namespace LeanRDF.Tests.Iso

private def a : BlankNode := ⟨"a"⟩
private def b : BlankNode := ⟨"b"⟩
private def p : Term := .iri ⟨"http://example.org/p"⟩
private def o : Term := .iri ⟨"http://example.org/o"⟩
private def ta : Triple := ⟨.bnode a, p, o⟩
private def tb : Triple := ⟨.bnode b, p, o⟩

/-- Swap the blank nodes `a` and `b`. -/
private def swap (x : BlankNode) : BlankNode := if x = a then b else if x = b then a else x

private theorem swap_swap (x : BlankNode) : swap (swap x) = x := by
  unfold swap
  by_cases h1 : x = a <;> by_cases h2 : x = b <;> simp_all [a, b]

private theorem rename_rename (t : Triple) : (t.renameBNodes swap).renameBNodes swap = t := by
  rw [Triple.renameBNodes_comp]
  have : swap ∘ swap = id := funext swap_swap
  rw [this, Triple.renameBNodes_id]

-- @tg: verifies:: [[openspec:rdf-core#Blank node isomorphism#Relabelled graph is isomorphic]] {level: unit}
example : Graph.Iso (Graph.singleton ta) (Graph.singleton tb) := by
  refine ⟨swap, ⟨fun x y h => ?_, fun y => ⟨swap y, swap_swap y⟩⟩, fun t => ?_⟩
  · rw [← swap_swap x, h, swap_swap]
  · simp only [Graph.mem_singleton]
    constructor
    · rintro rfl; decide
    · intro h; rw [← rename_rename t, h]; decide

-- @tg: verifies:: [[openspec:rdf-core#Blank node isomorphism#Isomorphism is reflexive]] {level: unit}
example (g : Graph) : Graph.Iso g g := Graph.Iso.refl g

private def reifies : Term := .iri LeanRDF.Vocab.rdf.reifies
private def r : Term := .iri ⟨"http://example.org/r"⟩
private def qa : Triple := ⟨r, reifies, .triple (.bnode a) p o⟩
private def qb : Triple := ⟨r, reifies, .triple (.bnode b) p o⟩

-- @tg: verifies:: [[openspec:rdf-core#Blank node isomorphism#Renaming reaches into triple terms]] {level: unit}
example : qa.renameBNodes swap = qb ∧ Graph.Iso (Graph.singleton qa) (Graph.singleton qb) := by
  refine ⟨by decide, swap, ⟨fun x y h => ?_, fun y => ⟨swap y, swap_swap y⟩⟩, fun t => ?_⟩
  · rw [← swap_swap x, h, swap_swap]
  · simp only [Graph.mem_singleton]
    constructor
    · rintro rfl; decide
    · intro h; rw [← rename_rename t, h]; decide

end LeanRDF.Tests.Iso
