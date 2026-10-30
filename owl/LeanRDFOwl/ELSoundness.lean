import LeanRDFOwl.EL
import LeanRDFOwl.Soundness

/-!
# Soundness of the EL rules

Each EL completion rule is sound in every interpretation satisfying `OWLCore`; with
`owlRules_sound`, every derivation under `owlELRules` is an OWL entailment.
-/

namespace LeanRDF.Owl

open Vocab RDFS Semantics SimpleInterp

variable {I : SimpleInterp}

/-! ## Intersections of two and three classes -/

theorem listOf_two {l a l2 b : I.Dom} (h1 : I.IEXT (I.IS rdf.first) l a)
    (h2 : I.IEXT (I.IS rdf.rest) l l2) (h3 : I.IEXT (I.IS rdf.first) l2 b)
    (h4 : I.IEXT (I.IS rdf.rest) l2 (I.IS rdf.nil)) : ListOf I l [a, b] :=
  ⟨h1, l2, h2, h3, _, h4, rfl⟩

theorem listOf_three {l a l2 b l3 d : I.Dom} (h1 : I.IEXT (I.IS rdf.first) l a)
    (h2 : I.IEXT (I.IS rdf.rest) l l2) (h3 : I.IEXT (I.IS rdf.first) l2 b)
    (h4 : I.IEXT (I.IS rdf.rest) l2 l3) (h5 : I.IEXT (I.IS rdf.first) l3 d)
    (h6 : I.IEXT (I.IS rdf.rest) l3 (I.IS rdf.nil)) : ListOf I l [a, b, d] :=
  ⟨h1, l2, h2, h3, l3, h4, h5, _, h6, rfl⟩

-- @tg: implements:: [[openspec:owl-el#Intersection condition]] {note: "two and three classes"}
/-- `ICEXT(x) = ICEXT(a) ∩ ICEXT(b)` for `x owl:intersectionOf (a b)`. -/
theorem intersection_two (hI : OWLConds I) {x l a b : I.Dom}
    (h : I.IEXT (I.IS intersectionOf) x l) (hl : ListOf I l [a, b]) :
    I.IC x ∧ I.IC a ∧ I.IC b ∧ ∀ y, I.IR y → (I.InClass y x ↔ I.InClass y a ∧ I.InClass y b) := by
  obtain ⟨hx, hcs, hy⟩ := hI.intersection x l [a, b] h hl
  refine ⟨hx, hcs a (by simp), hcs b (by simp), fun y hr => (hy y hr).trans ?_⟩
  simp

/-- `ICEXT(x) = ICEXT(a) ∩ ICEXT(b) ∩ ICEXT(d)` for `x owl:intersectionOf (a b d)`. -/
theorem intersection_three (hI : OWLConds I) {x l a b d : I.Dom}
    (h : I.IEXT (I.IS intersectionOf) x l) (hl : ListOf I l [a, b, d]) :
    I.IC x ∧ I.IC a ∧ I.IC b ∧ I.IC d ∧
      ∀ y, I.IR y → (I.InClass y x ↔ I.InClass y a ∧ I.InClass y b ∧ I.InClass y d) := by
  obtain ⟨hx, hcs, hy⟩ := hI.intersection x l [a, b, d] h hl
  refine ⟨hx, hcs a (by simp), hcs b (by simp), hcs d (by simp), fun y hr => (hy y hr).trans ?_⟩
  simp

/-! ## Premises -/

private theorem b0 {α : Type} {x : α} {l : List α} : x ∈ x :: l := .head _
private theorem b1 {α : Type} {x y : α} {l : List α} : y ∈ x :: y :: l := .tail _ b0
private theorem b2 {α : Type} {x y z : α} {l : List α} : z ∈ x :: y :: z :: l := .tail _ b1
private theorem b3 {α : Type} {x y z w : α} {l : List α} : w ∈ x :: y :: z :: w :: l := .tail _ b2
private theorem b4 {α : Type} {x y z w a : α} {l : List α} : a ∈ x :: y :: z :: w :: a :: l := .tail _ b3
private theorem b5 {α : Type} {x y z w a b : α} {l : List α} : b ∈ x :: y :: z :: w :: a :: b :: l :=
  .tail _ b4
private theorem b6 {α : Type} {x y z w a b c : α} {l : List α} :
    c ∈ x :: y :: z :: w :: a :: b :: c :: l := .tail _ b5
private theorem b7 {α : Type} {x y z w a b c d : α} {l : List α} :
    d ∈ x :: y :: z :: w :: a :: b :: c :: d :: l := .tail _ b6
private theorem b8 {α : Type} {x y z w a b c d e : α} {l : List α} :
    e ∈ x :: y :: z :: w :: a :: b :: c :: d :: e :: l := .tail _ b7
private theorem b9 {α : Type} {x y z w a b c d e f : α} {l : List α} :
    f ∈ x :: y :: z :: w :: a :: b :: c :: d :: e :: f :: l := .tail _ b8

private theorem ir_of {y c : I.Dom} (h : I.InClass y c) : I.IR y := (I.IEXT_wt _ _ _ h).2.1

/-! ## Intersections -/

theorem elIntE1_sound : elIntE1.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨c, x, hc, hx, hcx⟩ := holds_iri (hb _ b0)
  obtain ⟨x', l, hx', hl, hint⟩ := holds_iri (hb _ b1)
  obtain ⟨l', a, hl', ha, hf⟩ := holds_iri (hb _ b2)
  obtain ⟨l'', l2, hl'', hl2, hr⟩ := holds_iri (hb _ b3)
  obtain ⟨l2', d, hl2', hd, hf2⟩ := holds_iri (hb _ b4)
  obtain ⟨l2'', hl2'', hnil⟩ := holds_const (hb _ b5)
  cases same hx hx'; cases same hl hl'; cases same hl hl''; cases same hl2 hl2'; cases same hl2 hl2''
  obtain ⟨-, hca, -, hy⟩ := intersection_two hI.2 hint (listOf_two hf hr hf2 hnil)
  exact Holds.intro I hc rfl ha (hI.2.subClass_of _ _ (sub_ic hI hcx).1 hca fun y h =>
    ((hy y (ir_of h)).1 (hI.1.subClass_ext _ _ hcx y h)).1)

theorem elIntE2_sound : elIntE2.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨c, x, hc, hx, hcx⟩ := holds_iri (hb _ b0)
  obtain ⟨x', l, hx', hl, hint⟩ := holds_iri (hb _ b1)
  obtain ⟨l', a, hl', ha, hf⟩ := holds_iri (hb _ b2)
  obtain ⟨l'', l2, hl'', hl2, hr⟩ := holds_iri (hb _ b3)
  obtain ⟨l2', d, hl2', hd, hf2⟩ := holds_iri (hb _ b4)
  obtain ⟨l2'', hl2'', hnil⟩ := holds_const (hb _ b5)
  cases same hx hx'; cases same hl hl'; cases same hl hl''; cases same hl2 hl2'; cases same hl2 hl2''
  obtain ⟨-, -, hcd, hy⟩ := intersection_two hI.2 hint (listOf_two hf hr hf2 hnil)
  exact Holds.intro I hc rfl hd (hI.2.subClass_of _ _ (sub_ic hI hcx).1 hcd fun y h =>
    ((hy y (ir_of h)).1 (hI.1.subClass_ext _ _ hcx y h)).2)

theorem elIntE13_sound : elIntE13.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨c, x, hc, hx, hcx⟩ := holds_iri (hb _ b0)
  obtain ⟨x', l, hx', hl, hint⟩ := holds_iri (hb _ b1)
  obtain ⟨l', a, hl', ha, hf⟩ := holds_iri (hb _ b2)
  obtain ⟨l'', l2, hl'', hl2, hr⟩ := holds_iri (hb _ b3)
  obtain ⟨l2', d, hl2', hd, hf2⟩ := holds_iri (hb _ b4)
  obtain ⟨l2'', l3, hl2'', hl3, hr2⟩ := holds_iri (hb _ b5)
  obtain ⟨l3', e, hl3', he, hf3⟩ := holds_iri (hb _ b6)
  obtain ⟨l3'', hl3'', hnil⟩ := holds_const (hb _ b7)
  cases same hx hx'; cases same hl hl'; cases same hl hl''; cases same hl2 hl2'; cases same hl2 hl2''
  cases same hl3 hl3'; cases same hl3 hl3''
  obtain ⟨-, hca, -, -, hy⟩ := intersection_three hI.2 hint (listOf_three hf hr hf2 hr2 hf3 hnil)
  exact Holds.intro I hc rfl ha (hI.2.subClass_of _ _ (sub_ic hI hcx).1 hca fun y h =>
    ((hy y (ir_of h)).1 (hI.1.subClass_ext _ _ hcx y h)).1)

theorem elIntE23_sound : elIntE23.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨c, x, hc, hx, hcx⟩ := holds_iri (hb _ b0)
  obtain ⟨x', l, hx', hl, hint⟩ := holds_iri (hb _ b1)
  obtain ⟨l', a, hl', ha, hf⟩ := holds_iri (hb _ b2)
  obtain ⟨l'', l2, hl'', hl2, hr⟩ := holds_iri (hb _ b3)
  obtain ⟨l2', d, hl2', hd, hf2⟩ := holds_iri (hb _ b4)
  obtain ⟨l2'', l3, hl2'', hl3, hr2⟩ := holds_iri (hb _ b5)
  obtain ⟨l3', e, hl3', he, hf3⟩ := holds_iri (hb _ b6)
  obtain ⟨l3'', hl3'', hnil⟩ := holds_const (hb _ b7)
  cases same hx hx'; cases same hl hl'; cases same hl hl''; cases same hl2 hl2'; cases same hl2 hl2''
  cases same hl3 hl3'; cases same hl3 hl3''
  obtain ⟨-, -, hcd, -, hy⟩ := intersection_three hI.2 hint (listOf_three hf hr hf2 hr2 hf3 hnil)
  exact Holds.intro I hc rfl hd (hI.2.subClass_of _ _ (sub_ic hI hcx).1 hcd fun y h =>
    ((hy y (ir_of h)).1 (hI.1.subClass_ext _ _ hcx y h)).2.1)

theorem elIntE3_sound : elIntE3.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨c, x, hc, hx, hcx⟩ := holds_iri (hb _ b0)
  obtain ⟨x', l, hx', hl, hint⟩ := holds_iri (hb _ b1)
  obtain ⟨l', a, hl', ha, hf⟩ := holds_iri (hb _ b2)
  obtain ⟨l'', l2, hl'', hl2, hr⟩ := holds_iri (hb _ b3)
  obtain ⟨l2', d, hl2', hd, hf2⟩ := holds_iri (hb _ b4)
  obtain ⟨l2'', l3, hl2'', hl3, hr2⟩ := holds_iri (hb _ b5)
  obtain ⟨l3', e, hl3', he, hf3⟩ := holds_iri (hb _ b6)
  obtain ⟨l3'', hl3'', hnil⟩ := holds_const (hb _ b7)
  cases same hx hx'; cases same hl hl'; cases same hl hl''; cases same hl2 hl2'; cases same hl2 hl2''
  cases same hl3 hl3'; cases same hl3 hl3''
  obtain ⟨-, -, -, hce, hy⟩ := intersection_three hI.2 hint (listOf_three hf hr hf2 hr2 hf3 hnil)
  exact Holds.intro I hc rfl he (hI.2.subClass_of _ _ (sub_ic hI hcx).1 hce fun y h =>
    ((hy y (ir_of h)).1 (hI.1.subClass_ext _ _ hcx y h)).2.2)

theorem elIntI2_sound : elIntI2.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨c, a, hc, ha, hca⟩ := holds_iri (hb _ b0)
  obtain ⟨c', d, hc', hd, hcd⟩ := holds_iri (hb _ b1)
  obtain ⟨x, l, hx, hl, hint⟩ := holds_iri (hb _ b2)
  obtain ⟨l', a', hl', ha', hf⟩ := holds_iri (hb _ b3)
  obtain ⟨l'', l2, hl'', hl2, hr⟩ := holds_iri (hb _ b4)
  obtain ⟨l2', d', hl2', hd', hf2⟩ := holds_iri (hb _ b5)
  obtain ⟨l2'', hl2'', hnil⟩ := holds_const (hb _ b6)
  cases same hc hc'; cases same ha ha'; cases same hd hd'; cases same hl hl'; cases same hl hl''
  cases same hl2 hl2'; cases same hl2 hl2''
  obtain ⟨hxc, -, -, hy⟩ := intersection_two hI.2 hint (listOf_two hf hr hf2 hnil)
  exact Holds.intro I hc rfl hx (hI.2.subClass_of _ _ (sub_ic hI hca).1 hxc fun y h =>
    (hy y (ir_of h)).2 ⟨hI.1.subClass_ext _ _ hca y h, hI.1.subClass_ext _ _ hcd y h⟩)

theorem elIntI3_sound : elIntI3.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨c, a, hc, ha, hca⟩ := holds_iri (hb _ b0)
  obtain ⟨c', d, hc', hd, hcd⟩ := holds_iri (hb _ b1)
  obtain ⟨c'', e, hc'', he, hce⟩ := holds_iri (hb _ b2)
  obtain ⟨x, l, hx, hl, hint⟩ := holds_iri (hb _ b3)
  obtain ⟨l', a', hl', ha', hf⟩ := holds_iri (hb _ b4)
  obtain ⟨l'', l2, hl'', hl2, hr⟩ := holds_iri (hb _ b5)
  obtain ⟨l2', d', hl2', hd', hf2⟩ := holds_iri (hb _ b6)
  obtain ⟨l2'', l3, hl2'', hl3, hr2⟩ := holds_iri (hb _ b7)
  obtain ⟨l3', e', hl3', he', hf3⟩ := holds_iri (hb _ b8)
  obtain ⟨l3'', hl3'', hnil⟩ := holds_const (hb _ b9)
  cases same hc hc'; cases same hc hc''; cases same ha ha'; cases same hd hd'; cases same he he'
  cases same hl hl'; cases same hl hl''; cases same hl2 hl2'; cases same hl2 hl2''
  cases same hl3 hl3'; cases same hl3 hl3''
  obtain ⟨hxc, -, -, -, hy⟩ := intersection_three hI.2 hint (listOf_three hf hr hf2 hr2 hf3 hnil)
  exact Holds.intro I hc rfl hx (hI.2.subClass_of _ _ (sub_ic hI hca).1 hxc fun y h =>
    (hy y (ir_of h)).2 ⟨hI.1.subClass_ext _ _ hca y h, hI.1.subClass_ext _ _ hcd y h,
      hI.1.subClass_ext _ _ hce y h⟩)

/-! ## Existentials -/

theorem elEx_sound : elEx.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨c, r, hc, hr, hcr⟩ := holds_iri (hb _ b0)
  obtain ⟨r', d, hr', hd, hsv1⟩ := holds_iri (hb _ b1)
  obtain ⟨r'', p, hr'', hp, hop1⟩ := holds_iri (hb _ b2)
  obtain ⟨d', e, hd', he, hde⟩ := holds_iri (hb _ b3)
  obtain ⟨s, e', hs, he', hsv2⟩ := holds_iri (hb _ b4)
  obtain ⟨s', p', hs', hp', hop2⟩ := holds_iri (hb _ b5)
  cases same hr hr'; cases same hr hr''; cases same hd hd'; cases same he he'; cases same hs hs'
  cases same hp hp'
  exact Holds.intro I hc rfl hs (hI.2.subClass_of _ _ (sub_ic hI hcr).1
    (hI.2.restriction_class _ _ hop2) fun y h => by
      obtain ⟨z, hyz, hzd⟩ := (hI.2.svf _ _ _ hsv1 hop1 y).1 (hI.1.subClass_ext _ _ hcr y h)
      exact (hI.2.svf _ _ _ hsv2 hop2 y).2 ⟨z, hyz, hI.1.subClass_ext _ _ hde z hzd⟩)

theorem elExSub_sound : elExSub.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨c, r, hc, hr, hcr⟩ := holds_iri (hb _ b0)
  obtain ⟨r', d, hr', hd, hsv1⟩ := holds_iri (hb _ b1)
  obtain ⟨r'', p, hr'', hp, hop1⟩ := holds_iri (hb _ b2)
  obtain ⟨p', q, hp', hq, hpq⟩ := holds_iri (hb _ b3)
  obtain ⟨s, d', hs, hd', hsv2⟩ := holds_iri (hb _ b4)
  obtain ⟨s', q', hs', hq', hop2⟩ := holds_iri (hb _ b5)
  cases same hr hr'; cases same hr hr''; cases same hp hp'; cases same hd hd'; cases same hs hs'
  cases same hq hq'
  exact Holds.intro I hc rfl hs (hI.2.subClass_of _ _ (sub_ic hI hcr).1
    (hI.2.restriction_class _ _ hop2) fun y h => by
      obtain ⟨z, hyz, hzd⟩ := (hI.2.svf _ _ _ hsv1 hop1 y).1 (hI.1.subClass_ext _ _ hcr y h)
      exact (hI.2.svf _ _ _ hsv2 hop2 y).2 ⟨z, hI.1.subProp_ext _ _ hpq y z hyz, hzd⟩)

theorem elExBot_sound : elExBot.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨c, r, hc, hr, hcr⟩ := holds_iri (hb _ b0)
  obtain ⟨r', d, hr', hd, hsv⟩ := holds_iri (hb _ b1)
  obtain ⟨r'', p, hr'', hp, hop⟩ := holds_iri (hb _ b2)
  obtain ⟨d', hd', hbot⟩ := holds_const (hb _ b3)
  cases same hr hr'; cases same hr hr''; cases same hd hd'
  exact Holds.intro I hc rfl rfl (hI.2.subClass_of _ _ (sub_ic hI hcr).1 (nothing_ic hI) fun y h => by
    obtain ⟨z, -, hzd⟩ := (hI.2.svf _ _ _ hsv hop y).1 (hI.1.subClass_ext _ _ hcr y h)
    exact absurd (hI.1.subClass_ext _ _ hbot z hzd) (hI.2.nothing z))

/-! ## The rule set -/

-- @tg: implements:: [[openspec:owl-el#EL soundness]]
theorem elRules_sound : ∀ r ∈ elRules, r.SoundIn OWLCore := by
  intro r hr
  simp only [elRules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact elIntE1_sound
  · exact elIntE2_sound
  · exact elIntE13_sound
  · exact elIntE23_sound
  · exact elIntE3_sound
  · exact elIntI2_sound
  · exact elIntI3_sound
  · exact elEx_sound
  · exact elExSub_sound
  · exact elExBot_sound

theorem owlELRules_sound : ∀ r ∈ owlELRules, r.SoundIn OWLCore := by
  intro r hr
  rcases List.mem_append.1 hr with hr | hr
  · exact owlRules_sound r hr
  · exact elRules_sound r hr

private theorem instantiate_bnode (t : Triple) : t.instantiate (fun b => .bnode b) = t := by
  obtain ⟨s, p, o⟩ := t
  cases s <;> cases p <;> cases o <;> rfl

/-- Soundness: every triple derivable from `g` by `owlELRules` is OWL-entailed by `g`. -/
theorem _root_.LeanRDF.Derives.el_sound {g : Graph} {t : Triple} (h : Derives owlELRules g t) :
    g.OWLEntails (Graph.singleton t) := by
  intro I hI hg
  refine Derives.satisfies_graph owlELRules_sound (fun b => .bnode b) (fun u hu => ?_)
    I.toSimpleInterp hI.toCore (fun _ hx => hI.1.1.IP_IR hx) hg
  rw [Graph.mem_singleton] at hu
  subst hu
  rw [instantiate_bnode]
  exact h

/-- Soundness for graph queries under `owlELRules`. -/
theorem _root_.LeanRDF.Derives.el_sound_graph {g q : Graph} (μ : BlankNode → Term)
    (h : ∀ t ∈ q, Derives owlELRules g (t.instantiate μ)) : g.OWLEntails q :=
  fun I hI hg => Derives.satisfies_graph owlELRules_sound μ h I.toSimpleInterp hI.toCore
    (fun _ hx => hI.1.1.IP_IR hx) hg

end LeanRDF.Owl
