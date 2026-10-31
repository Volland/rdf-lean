import LeanRDF.Core.Graph

/-!
# Graph isomorphism

Two graphs are isomorphic when a bijection on blank nodes maps one onto the other, inside
triple terms too (RDF 1.2 Concepts §3.7). Stated as a definition; deciding it is not needed in
v0.x.
-/

namespace LeanRDF

/-- A bijective function. Core Lean has no `Function.Bijective` without Mathlib. -/
def Bijective {α β : Type} (f : α → β) : Prop :=
  (∀ a b, f a = f b → a = b) ∧ ∀ b, ∃ a, f a = b

theorem bijective_id {α : Type} : Bijective (id : α → α) :=
  ⟨fun _ _ h => h, fun b => ⟨b, rfl⟩⟩

namespace Graph

-- @tg: implements:: [[openspec:rdf-core#Blank node isomorphism]]
/-- Graph isomorphism up to blank-node renaming (RDF 1.2 Concepts §3.7): a bijection `f` on
blank nodes such that `t ∈ g` iff `t` renamed by `f`, at any depth of its triple terms, is in
`h`. -/
def Iso (g h : Graph) : Prop :=
  ∃ f : BlankNode → BlankNode, Bijective f ∧ ∀ t : Triple, t ∈ g ↔ t.renameBNodes f ∈ h

/-- Every graph is isomorphic to itself, by the identity on blank nodes. -/
theorem Iso.refl (g : Graph) : Iso g g :=
  ⟨id, bijective_id, fun t => by simp⟩

end Graph

end LeanRDF
