import LeanRDFShacl.Shapes

/-!
# The SHACL Core semantics

When a focus node conforms to a shape (SHACL §3.4, §4), as propositions over the data graph:
value nodes come from the path relation `ValueNode`, counts are stated with lists without
duplicates, and SHACL instances follow `rdfs:subClassOf` in the data graph (§3.2).
-/

namespace LeanRDF.Shacl

open Vocab

variable (G : Graph)

/-- The value nodes of a focus node (§3.3): the focus node itself for a node shape, the path's
value nodes for a property shape. -/
def VN : Option Path → Term → Term → Prop
  | none, x, y => y = x
  | some p, x, y => ValueNode G p x y

/-- `v` is a SHACL instance of `c` (§3.2): it has a type that is `c` or a subclass of `c` in
the data graph. -/
def InstanceOf (v c : Term) : Prop :=
  ∃ t, ⟨v, .iri rdf.type, t⟩ ∈ G ∧ ValueNode G (.zeroOrMore (.pred rdfs.subClassOf)) t c

-- @tg: implements:: [[openspec:shacl-core#SHACL Core semantics]]
mutual
/-- A focus node conforms to a shape (§3.4): the shape is deactivated, or every component holds. -/
def Conforms : Shape → Term → Prop
  | .mk _ path _ comps deact _ _, x => deact = true ∨ CompsHold path comps x
/-- Every component of a list holds. -/
def CompsHold (path : Option Path) : List Component → Term → Prop
  | [], _ => True
  | c :: cs, x => CompHolds path c x ∧ CompsHold path cs x
/-- A component holds at a focus node (§4), given the shape's path. -/
def CompHolds (path : Option Path) : Component → Term → Prop
  | .test t, x => ∀ v, VN G path x v → t.ok v = true
  | .class_ c, x => ∀ v, VN G path x v → InstanceOf G v c
  | .minCount n, x => ∃ l : List Term, l.Nodup ∧ (∀ y ∈ l, VN G path x y) ∧ n ≤ l.length
  | .maxCount n, x => ∀ l : List Term, l.Nodup → (∀ y ∈ l, VN G path x y) → l.length ≤ n
  | .uniqueLang, x => ∀ y z, VN G path x y → VN G path x z → y ≠ z →
      langOf y = none ∨ langOf y ≠ langOf z
  | .equals p, x => ∀ v, VN G path x v ↔ ⟨x, .iri p, v⟩ ∈ G
  | .disjoint p, x => ∀ v, VN G path x v → ⟨x, .iri p, v⟩ ∉ G
  | .lessThan p, x => ∀ v w, VN G path x v → ⟨x, .iri p, w⟩ ∈ G → lessB false v w = true
  | .lessThanOrEquals p, x => ∀ v w, VN G path x v → ⟨x, .iri p, w⟩ ∈ G → lessB true v w = true
  | .not s, x => ∀ v, VN G path x v → ¬ Conforms s v
  | .and ss, x => ∀ v, VN G path x v → AllConform ss v
  | .or ss, x => ∀ v, VN G path x v → SomeConforms ss v
  | .xone ss, x => ∀ v, VN G path x v → OneConforms ss v
  | .node s, x => ∀ v, VN G path x v → Conforms s v
  | .property s, x => ∀ v, VN G path x v → Conforms s v
  | .qualifiedMin s n sibs, x => ∃ l : List Term, l.Nodup ∧
      (∀ y ∈ l, VN G path x y ∧ Conforms s y ∧ NoneConform sibs y) ∧ n ≤ l.length
  | .qualifiedMax s n sibs, x => ∀ l : List Term, l.Nodup →
      (∀ y ∈ l, VN G path x y ∧ Conforms s y ∧ NoneConform sibs y) → l.length ≤ n
  | .closed allowed, x => ∀ v, VN G path x v → ∀ p o, ⟨v, p, o⟩ ∈ G → ∃ q ∈ allowed, p = .iri q
  | .hasValue t, x => VN G path x t
/-- The node conforms to every shape (`sh:and`). -/
def AllConform : List Shape → Term → Prop
  | [], _ => True
  | s :: ss, v => Conforms s v ∧ AllConform ss v
/-- The node conforms to some shape (`sh:or`). -/
def SomeConforms : List Shape → Term → Prop
  | [], _ => False
  | s :: ss, v => Conforms s v ∨ SomeConforms ss v
/-- The node conforms to none of the shapes (disjoint qualified shapes). -/
def NoneConform : List Shape → Term → Prop
  | [], _ => True
  | s :: ss, v => ¬ Conforms s v ∧ NoneConform ss v
/-- The node conforms to exactly one shape (`sh:xone`). -/
def OneConforms : List Shape → Term → Prop
  | [], _ => False
  | s :: ss, v => (Conforms s v ∧ NoneConform ss v) ∨ (¬ Conforms s v ∧ OneConforms ss v)
end

/-- A target selects a focus node (§2.1.3). -/
def TargetHolds : Target → Term → Prop
  | .node t, x => x = t
  | .class_ c, x => InstanceOf G x c
  | .subjectsOf p, x => ∃ o, ⟨x, .iri p, o⟩ ∈ G
  | .objectsOf p, x => ∃ s, ⟨s, .iri p, x⟩ ∈ G

/-- `x` is a focus node of the shape. -/
def IsFocus (s : Shape) (x : Term) : Prop := ∃ tg ∈ s.targets, TargetHolds G tg x

/-- The data graph conforms to the shapes (§3.4): every focus node of every shape conforms. -/
def DataConforms (S : List Shape) : Prop := ∀ s ∈ S, ∀ x, IsFocus G s x → Conforms G s x

end LeanRDF.Shacl
