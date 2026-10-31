import LeanRDFOwl.Rules

/-!
# Soundness of the OWL 2 RL rules

Every rule of `owlRules` is sound in every interpretation satisfying `OWLCore` (the core RDFS
conditions and the OWL conditions), so every derivation is an OWL entailment.
-/

namespace LeanRDF.Owl

open Vocab RDFS Semantics SimpleInterp

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

/-! ## Facts from the RDFS axioms -/

variable {I : SimpleInterp}

private theorem ax (hI : RDFSCore I) {a : IRI × IRI × IRI} (h : a ∈ rdfsAxioms) : I.HoldsIRI a :=
  hI.axioms a (List.mem_append_left _ (List.mem_append_right _ h))

/-- Both sides of `rdfs:subClassOf` are classes. -/
theorem sub_ic (hI : OWLCore I) {c d : I.Dom} (h : I.SubClass c d) : I.IC c ∧ I.IC d :=
  ⟨hI.1.domain _ _ _ _ (ax hI.1 (a := (rdfs.subClassOf, rdfs.domain, rdfs.Class)) (by simp [rdfsAxioms])).2 h,
   hI.1.range _ _ _ _ (ax hI.1 (a := (rdfs.subClassOf, rdfs.range, rdfs.Class)) (by simp [rdfsAxioms])).2 h⟩

/-- Both sides of `rdfs:subPropertyOf` are properties. -/
theorem sub_ip (hI : OWLCore I) {p q : I.Dom} (h : I.SubProp p q) : I.IP p ∧ I.IP q :=
  ⟨(hI.2.IP_iff _).2 (hI.1.domain _ _ _ _
      (ax hI.1 (a := (rdfs.subPropertyOf, rdfs.domain, rdf.Property)) (by simp [rdfsAxioms])).2 h),
   (hI.2.IP_iff _).2 (hI.1.range _ _ _ _
      (ax hI.1 (a := (rdfs.subPropertyOf, rdfs.range, rdf.Property)) (by simp [rdfsAxioms])).2 h)⟩

/-- A domain triple relates a property and a class. -/
theorem dom_ic (hI : OWLCore I) {p c : I.Dom} (h : I.IEXT (I.IS rdfs.domain) p c) : I.IP p ∧ I.IC c :=
  ⟨(hI.2.IP_iff _).2 (hI.1.domain _ _ _ _
      (ax hI.1 (a := (rdfs.domain, rdfs.domain, rdf.Property)) (by simp [rdfsAxioms])).2 h),
   hI.1.range _ _ _ _ (ax hI.1 (a := (rdfs.domain, rdfs.range, rdfs.Class)) (by simp [rdfsAxioms])).2 h⟩

/-- A range triple relates a property and a class. -/
theorem rng_ic (hI : OWLCore I) {p c : I.Dom} (h : I.IEXT (I.IS rdfs.range) p c) : I.IP p ∧ I.IC c :=
  ⟨(hI.2.IP_iff _).2 (hI.1.domain _ _ _ _
      (ax hI.1 (a := (rdfs.range, rdfs.domain, rdf.Property)) (by simp [rdfsAxioms])).2 h),
   hI.1.range _ _ _ _ (ax hI.1 (a := (rdfs.range, rdfs.range, rdfs.Class)) (by simp [rdfsAxioms])).2 h⟩

/-- Properties are resources. -/
theorem ip_ir (hI : OWLCore I) {p : I.Dom} (h : I.IP p) : I.IR p :=
  (I.IEXT_wt _ _ _ (hI.1.property p h)).2.1

/-- An OWL axiom holds. -/
private theorem owlAx (hI : OWLCore I) {a : IRI × IRI × IRI} (h : a ∈ owlAxioms) : I.HoldsIRI a :=
  hI.2.axioms a h

theorem thing_ic (hI : OWLCore I) : I.IC (I.IS Thing) :=
  hI.2.owlClass _ (owlAx hI (a := (Thing, rdf.type, «Class»)) (by simp [owlAxioms])).2

theorem nothing_ic (hI : OWLCore I) : I.IC (I.IS Nothing) :=
  hI.2.owlClass _ (owlAx hI (a := (Nothing, rdf.type, «Class»)) (by simp [owlAxioms])).2

/-- `x owl:sameAs x` for a resource. -/
private theorem same_refl (hI : OWLCore I) {x : I.Dom} (h : I.IR x) : I.IEXT (I.IS sameAs) x x :=
  (hI.2.sameAs x x).2 ⟨rfl, h⟩

/-! ## Equality -/

theorem eqRefS_sound : eqRefS.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨s, _, _, hs, _, _, h⟩ := holds_any (hb _ b0)
  exact Holds.intro I hs rfl hs (same_refl hI (I.IEXT_wt _ _ _ h).2.1)

theorem eqRefP_sound : eqRefP.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨_, p, _, _, hp, _, h⟩ := holds_any (hb _ b0)
  exact Holds.intro I hp rfl hp (same_refl hI (ip_ir hI (I.IEXT_wt _ _ _ h).1))

theorem eqRefO_sound : eqRefO.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨_, _, o, _, _, ho, h⟩ := holds_any (hb _ b0)
  exact Holds.intro I ho rfl ho (same_refl hI (I.IEXT_wt _ _ _ h).2.2)

theorem eqSym_sound : eqSym.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨x, y, hx, hy, h⟩ := holds_iri (hb _ b0)
  obtain ⟨rfl, hr⟩ := (hI.2.sameAs x y).1 h
  exact Holds.intro I hy rfl hx (same_refl hI hr)

theorem eqTrans_sound : eqTrans.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨x, y, hx, hy, h1⟩ := holds_iri (hb _ b0)
  obtain ⟨y', z, hy', hz, h2⟩ := holds_iri (hb _ b1)
  cases same hy hy'
  obtain ⟨rfl, hr⟩ := (hI.2.sameAs x y).1 h1
  obtain ⟨rfl, -⟩ := (hI.2.sameAs x z).1 h2
  exact Holds.intro I hx rfl hz (same_refl hI hr)

theorem eqRepS_sound : eqRepS.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨s, s2, hs, hs2, h1⟩ := holds_iri (hb _ b0)
  obtain ⟨s', p, o, hs', hp, ho, h2⟩ := holds_any (hb _ b1)
  cases same hs hs'
  obtain ⟨rfl, -⟩ := (hI.2.sameAs s s2).1 h1
  exact Holds.intro I hs2 hp ho h2

theorem eqRepP_sound : eqRepP.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨p, p2, hp, hp2, h1⟩ := holds_iri (hb _ b0)
  obtain ⟨s, p', o, hs, hp', ho, h2⟩ := holds_any (hb _ b1)
  cases same hp hp'
  obtain ⟨rfl, -⟩ := (hI.2.sameAs p p2).1 h1
  exact Holds.intro I hs hp2 ho h2

theorem eqRepO_sound : eqRepO.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨o, o2, ho, ho2, h1⟩ := holds_iri (hb _ b0)
  obtain ⟨s, p, o', hs, hp, ho', h2⟩ := holds_any (hb _ b1)
  cases same ho ho'
  obtain ⟨rfl, -⟩ := (hI.2.sameAs o o2).1 h1
  exact Holds.intro I hs hp ho2 h2

/-! ## Properties -/

theorem prpFp_sound : prpFp.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨p, hp, hf⟩ := holds_type (hb _ b0)
  obtain ⟨x, p₁, y1, hx, hp₁, hy1, h1⟩ := holds_any (hb _ b1)
  obtain ⟨x', p₂, y2, hx', hp₂, hy2, h2⟩ := holds_any (hb _ b2)
  cases same hp hp₁; cases same hp hp₂; cases same hx hx'
  cases hI.2.functional _ hf _ _ _ h1 h2
  exact Holds.intro I hy1 rfl hy2 (same_refl hI (I.IEXT_wt _ _ _ h1).2.2)

theorem prpIfp_sound : prpIfp.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨p, hp, hf⟩ := holds_type (hb _ b0)
  obtain ⟨x1, p₁, y, hx1, hp₁, hy, h1⟩ := holds_any (hb _ b1)
  obtain ⟨x2, p₂, y', hx2, hp₂, hy', h2⟩ := holds_any (hb _ b2)
  cases same hp hp₁; cases same hp hp₂; cases same hy hy'
  cases hI.2.invFunctional _ hf _ _ _ h1 h2
  exact Holds.intro I hx1 rfl hx2 (same_refl hI (I.IEXT_wt _ _ _ h1).2.1)

theorem prpSymp_sound : prpSymp.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨p, hp, hs⟩ := holds_type (hb _ b0)
  obtain ⟨x, p₁, y, hx, hp₁, hy, h⟩ := holds_any (hb _ b1)
  cases same hp hp₁
  exact Holds.intro I hy hp hx (hI.2.symmetric _ hs _ _ h)

theorem prpTrp_sound : prpTrp.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨p, hp, ht⟩ := holds_type (hb _ b0)
  obtain ⟨x, p₁, y, hx, hp₁, hy, h1⟩ := holds_any (hb _ b1)
  obtain ⟨y', p₂, z, hy', hp₂, hz, h2⟩ := holds_any (hb _ b2)
  cases same hp hp₁; cases same hp hp₂; cases same hy hy'
  exact Holds.intro I hx hp hz (hI.2.transitive _ ht _ _ _ h1 h2)

theorem prpEqp1_sound : prpEqp1.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨p1, p2, hp1, hp2, he⟩ := holds_iri (hb _ b0)
  obtain ⟨x, p₁, y, hx, hp₁, hy, h⟩ := holds_any (hb _ b1)
  cases same hp1 hp₁
  exact Holds.intro I hx hp2 hy (((hI.2.eqProp _ _ he).2.2 x y).1 h)

theorem prpEqp2_sound : prpEqp2.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨p1, p2, hp1, hp2, he⟩ := holds_iri (hb _ b0)
  obtain ⟨x, p₂, y, hx, hp₂, hy, h⟩ := holds_any (hb _ b1)
  cases same hp2 hp₂
  exact Holds.intro I hx hp1 hy (((hI.2.eqProp _ _ he).2.2 x y).2 h)

theorem prpInv1_sound : prpInv1.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨p1, p2, hp1, hp2, he⟩ := holds_iri (hb _ b0)
  obtain ⟨x, p₁, y, hx, hp₁, hy, h⟩ := holds_any (hb _ b1)
  cases same hp1 hp₁
  exact Holds.intro I hy hp2 hx ((hI.2.inverse _ _ he x y).1 h)

theorem prpInv2_sound : prpInv2.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨p1, p2, hp1, hp2, he⟩ := holds_iri (hb _ b0)
  obtain ⟨x, p₂, y, hx, hp₂, hy, h⟩ := holds_any (hb _ b1)
  cases same hp2 hp₂
  exact Holds.intro I hy hp1 hx ((hI.2.inverse _ _ he y x).2 h)

/-! ## Classes -/

/-- Unpack `x pred const` with a constant object IRI. -/
theorem holds_const {A : BlankNode → I.Dom} {s : Term} {p o : IRI}
    (h : I.Holds A ⟨s, .iri p, .iri o⟩) : ∃ x, I.denote A s = some x ∧ I.IEXT (I.IS p) x (I.IS o) := by
  obtain ⟨x, o', hx, ho, h⟩ := holds_iri h
  simp only [denote_iri, Option.some.injEq] at ho
  subst ho
  exact ⟨x, hx, h⟩

theorem clsSvf1_sound : clsSvf1.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨x, y, hx, hy, hs⟩ := holds_iri (hb _ b0)
  obtain ⟨x', p, hx', hp, ho⟩ := holds_iri (hb _ b1)
  obtain ⟨u, p', v, hu, hp', hv, h⟩ := holds_any (hb _ b2)
  obtain ⟨v', y', hv', hy', ht⟩ := holds_iri (hb _ b3)
  cases same hx hx'; cases same hp hp'; cases same hv hv'; cases same hy hy'
  exact Holds.intro I hu rfl hx ((hI.2.svf _ _ _ hs ho u).2 ⟨v, h, ht⟩)

theorem clsSvf2_sound : clsSvf2.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨x, hx, hs⟩ := holds_const (hb _ b0)
  obtain ⟨x', p, hx', hp, ho⟩ := holds_iri (hb _ b1)
  obtain ⟨u, p', v, hu, hp', hv, h⟩ := holds_any (hb _ b2)
  cases same hx hx'; cases same hp hp'
  exact Holds.intro I hu rfl hx ((hI.2.svf _ _ _ hs ho u).2 ⟨v, h, hI.2.thing _ (I.IEXT_wt _ _ _ h).2.2⟩)

theorem clsAvf_sound : clsAvf.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨x, y, hx, hy, ha⟩ := holds_iri (hb _ b0)
  obtain ⟨x', p, hx', hp, ho⟩ := holds_iri (hb _ b1)
  obtain ⟨u, x'', hu, hx'', ht⟩ := holds_iri (hb _ b2)
  obtain ⟨u', p', v, hu', hp', hv, h⟩ := holds_any (hb _ b3)
  cases same hx hx'; cases same hx hx''; cases same hp hp'; cases same hu hu'
  exact Holds.intro I hv rfl hy ((hI.2.avf _ _ _ ha ho u).1 ht v h)

theorem clsHv1_sound : clsHv1.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨x, y, hx, hy, hv⟩ := holds_iri (hb _ b0)
  obtain ⟨x', p, hx', hp, ho⟩ := holds_iri (hb _ b1)
  obtain ⟨u, x'', hu, hx'', ht⟩ := holds_iri (hb _ b2)
  cases same hx hx'; cases same hx hx''
  exact Holds.intro I hu hp hy ((hI.2.hasValue _ _ _ hv ho u).1 ht)

theorem clsHv2_sound : clsHv2.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨x, y, hx, hy, hv⟩ := holds_iri (hb _ b0)
  obtain ⟨x', p, hx', hp, ho⟩ := holds_iri (hb _ b1)
  obtain ⟨u, p', y', hu, hp', hy', h⟩ := holds_any (hb _ b2)
  cases same hx hx'; cases same hp hp'; cases same hy hy'
  exact Holds.intro I hu rfl hx ((hI.2.hasValue _ _ _ hv ho u).2 h)

theorem clsMaxc2_sound : clsMaxc2.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨x, n, hx, hn, hm⟩ := holds_iri (hb _ b0)
  obtain ⟨x', p, hx', hp, ho⟩ := holds_iri (hb _ b1)
  obtain ⟨u, x'', hu, hx'', ht⟩ := holds_iri (hb _ b2)
  obtain ⟨u1, p1, y1, hu1, hp1, hy1, h1⟩ := holds_any (hb _ b3)
  obtain ⟨u2, p2, y2, hu2, hp2, hy2, h2⟩ := holds_any (hb _ b4)
  cases same hx hx'; cases same hx hx''; cases same hu hu1; cases same hu hu2
  cases same hp hp1; cases same hp hp2
  cases hI.2.maxCard1 _ _ _ hn hm ho _ ht _ _ h1 h2
  exact Holds.intro I hy1 rfl hy2 (same_refl hI (I.IEXT_wt _ _ _ h1).2.2)

theorem clsMaxqc3_sound : clsMaxqc3.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨x, n, hx, hn, hm⟩ := holds_iri (hb _ b0)
  obtain ⟨x₁, p, hx₁, hp, ho⟩ := holds_iri (hb _ b1)
  obtain ⟨x₂, c, hx₂, hc, hoc⟩ := holds_iri (hb _ b2)
  obtain ⟨u, x₃, hu, hx₃, ht⟩ := holds_iri (hb _ b3)
  obtain ⟨u1, p1, y1, hu1, hp1, hy1, h1⟩ := holds_any (hb _ b4)
  obtain ⟨y1', c1, hy1', hc1, t1⟩ := holds_iri (hb _ b5)
  obtain ⟨u2, p2, y2, hu2, hp2, hy2, h2⟩ := holds_any (hb _ b6)
  obtain ⟨y2', c2, hy2', hc2, t2⟩ := holds_iri (hb _ b7)
  cases same hx hx₁; cases same hx hx₂; cases same hx hx₃; cases same hu hu1; cases same hu hu2
  cases same hp hp1; cases same hp hp2; cases same hy1 hy1'; cases same hy2 hy2'
  cases same hc hc1; cases same hc hc2
  cases hI.2.maxQCard1 _ _ _ _ hn hm ho hoc _ ht _ _ h1 t1 h2 t2
  exact Holds.intro I hy1 rfl hy2 (same_refl hI (I.IEXT_wt _ _ _ h1).2.2)

theorem clsMaxqc4_sound : clsMaxqc4.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨x, n, hx, hn, hm⟩ := holds_iri (hb _ b0)
  obtain ⟨x₁, p, hx₁, hp, ho⟩ := holds_iri (hb _ b1)
  obtain ⟨x₂, hx₂, hoc⟩ := holds_const (hb _ b2)
  obtain ⟨u, x₃, hu, hx₃, ht⟩ := holds_iri (hb _ b3)
  obtain ⟨u1, p1, y1, hu1, hp1, hy1, h1⟩ := holds_any (hb _ b4)
  obtain ⟨u2, p2, y2, hu2, hp2, hy2, h2⟩ := holds_any (hb _ b5)
  cases same hx hx₁; cases same hx hx₂; cases same hx hx₃; cases same hu hu1; cases same hu hu2
  cases same hp hp1; cases same hp hp2
  cases hI.2.maxQCard1 _ _ _ _ hn hm ho hoc _ ht _ _ h1 (hI.2.thing _ (I.IEXT_wt _ _ _ h1).2.2) h2
    (hI.2.thing _ (I.IEXT_wt _ _ _ h2).2.2)
  exact Holds.intro I hy1 rfl hy2 (same_refl hI (I.IEXT_wt _ _ _ h1).2.2)

/-! ## Class axioms -/

theorem caxEqc1_sound : caxEqc1.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨c1, c2, hc1, hc2, he⟩ := holds_iri (hb _ b0)
  obtain ⟨x, c1', hx, hc1', ht⟩ := holds_iri (hb _ b1)
  cases same hc1 hc1'
  exact Holds.intro I hx rfl hc2 (((hI.2.eqClass _ _ he).2.2 x).1 ht)

theorem caxEqc2_sound : caxEqc2.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨c1, c2, hc1, hc2, he⟩ := holds_iri (hb _ b0)
  obtain ⟨x, c2', hx, hc2', ht⟩ := holds_iri (hb _ b1)
  cases same hc2 hc2'
  exact Holds.intro I hx rfl hc1 (((hI.2.eqClass _ _ he).2.2 x).2 ht)

/-! ## Schema -/

theorem scmCls1_sound : scmCls1.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨x, hx, h⟩ := holds_type (hb _ b0)
  exact Holds.intro I hx rfl hx (hI.1.subClass_refl _ (hI.2.owlClass _ h))

theorem scmCls2_sound : scmCls2.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨x, hx, h⟩ := holds_type (hb _ b0)
  have hc := hI.2.owlClass _ h
  exact Holds.intro I hx rfl hx (hI.2.eqClass_of _ _ hc hc fun _ => Iff.rfl)

theorem scmCls3_sound : scmCls3.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨x, hx, h⟩ := holds_type (hb _ b0)
  exact Holds.intro I hx rfl rfl (hI.2.subClass_of _ _ (hI.2.owlClass _ h) (thing_ic hI)
    fun y hy => hI.2.thing _ (I.IEXT_wt _ _ _ hy).2.1)

theorem scmCls4_sound : scmCls4.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨x, hx, h⟩ := holds_type (hb _ b0)
  exact Holds.intro I rfl rfl hx (hI.2.subClass_of _ _ (nothing_ic hI) (hI.2.owlClass _ h)
    fun y hy => absurd hy (hI.2.nothing y))

theorem scmEqc1a_sound : scmEqc1a.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨c1, c2, hc1, hc2, he⟩ := holds_iri (hb _ b0)
  obtain ⟨i1, i2, ext⟩ := hI.2.eqClass _ _ he
  exact Holds.intro I hc1 rfl hc2 (hI.2.subClass_of _ _ i1 i2 fun x hx => (ext x).1 hx)

theorem scmEqc1b_sound : scmEqc1b.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨c1, c2, hc1, hc2, he⟩ := holds_iri (hb _ b0)
  obtain ⟨i1, i2, ext⟩ := hI.2.eqClass _ _ he
  exact Holds.intro I hc2 rfl hc1 (hI.2.subClass_of _ _ i2 i1 fun x hx => (ext x).2 hx)

theorem scmEqc2_sound : scmEqc2.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨c1, c2, hc1, hc2, h1⟩ := holds_iri (hb _ b0)
  obtain ⟨c2', c1', hc2', hc1', h2⟩ := holds_iri (hb _ b1)
  cases same hc1 hc1'; cases same hc2 hc2'
  obtain ⟨i1, i2⟩ := sub_ic hI h1
  exact Holds.intro I hc1 rfl hc2 (hI.2.eqClass_of _ _ i1 i2 fun x =>
    ⟨hI.1.subClass_ext _ _ h1 x, hI.1.subClass_ext _ _ h2 x⟩)

private theorem op_ip (hI : OWLCore I) {p : I.Dom} (h : I.InClass p (I.IS ObjectProperty) ∨
    I.InClass p (I.IS DatatypeProperty)) : I.IP p :=
  h.elim (hI.2.objProp p) (hI.2.dataProp p)

theorem scmOp1_sound : scmOp1.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨p, hp, h⟩ := holds_type (hb _ b0)
  exact Holds.intro I hp rfl hp (hI.1.prop_refl _ (hI.1.property _ (op_ip hI (.inl h))))

theorem scmOp2_sound : scmOp2.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨p, hp, h⟩ := holds_type (hb _ b0)
  have ip := op_ip hI (.inl h)
  exact Holds.intro I hp rfl hp (hI.2.eqProp_refl _ ip)

theorem scmDp1_sound : scmDp1.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨p, hp, h⟩ := holds_type (hb _ b0)
  exact Holds.intro I hp rfl hp (hI.1.prop_refl _ (hI.1.property _ (op_ip hI (.inr h))))

theorem scmDp2_sound : scmDp2.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨p, hp, h⟩ := holds_type (hb _ b0)
  have ip := op_ip hI (.inr h)
  exact Holds.intro I hp rfl hp (hI.2.eqProp_refl _ ip)

theorem scmEqp1a_sound : scmEqp1a.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨p1, p2, hp1, hp2, he⟩ := holds_iri (hb _ b0)
  exact Holds.intro I hp1 rfl hp2 (hI.2.eqProp_sub _ _ he).1

theorem scmEqp1b_sound : scmEqp1b.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨p1, p2, hp1, hp2, he⟩ := holds_iri (hb _ b0)
  exact Holds.intro I hp2 rfl hp1 (hI.2.eqProp_sub _ _ he).2

theorem scmEqp2_sound : scmEqp2.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨p1, p2, hp1, hp2, h1⟩ := holds_iri (hb _ b0)
  obtain ⟨p2', p1', hp2', hp1', h2⟩ := holds_iri (hb _ b1)
  cases same hp1 hp1'; cases same hp2 hp2'
  exact Holds.intro I hp1 rfl hp2 (hI.2.eqProp_of_sub _ _ h1 h2)

theorem scmDom1_sound : scmDom1.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨p, c1, hp, hc1, hd⟩ := holds_iri (hb _ b0)
  obtain ⟨c1', c2, hc1', hc2, hs⟩ := holds_iri (hb _ b1)
  cases same hc1 hc1'
  exact Holds.intro I hp rfl hc2 (hI.2.domain_sub _ _ _ hd hs)

theorem scmDom2_sound : scmDom2.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨p2, c, hp2, hc, hd⟩ := holds_iri (hb _ b0)
  obtain ⟨p1, p2', hp1, hp2', hs⟩ := holds_iri (hb _ b1)
  cases same hp2 hp2'
  exact Holds.intro I hp1 rfl hc (hI.2.domain_subProp _ _ _ hd hs)

theorem scmRng1_sound : scmRng1.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨p, c1, hp, hc1, hd⟩ := holds_iri (hb _ b0)
  obtain ⟨c1', c2, hc1', hc2, hs⟩ := holds_iri (hb _ b1)
  cases same hc1 hc1'
  exact Holds.intro I hp rfl hc2 (hI.2.range_sub _ _ _ hd hs)

theorem scmRng2_sound : scmRng2.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨p2, c, hp2, hc, hd⟩ := holds_iri (hb _ b0)
  obtain ⟨p1, p2', hp1, hp2', hs⟩ := holds_iri (hb _ b1)
  cases same hp2 hp2'
  exact Holds.intro I hp1 rfl hc (hI.2.range_subProp _ _ _ hd hs)

theorem scmHv_sound : scmHv.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨c1, i, hc1, hi, hv1⟩ := holds_iri (hb _ b0)
  obtain ⟨c1', p1, hc1', hp1, ho1⟩ := holds_iri (hb _ b1)
  obtain ⟨c2, i', hc2, hi', hv2⟩ := holds_iri (hb _ b2)
  obtain ⟨c2', p2, hc2', hp2, ho2⟩ := holds_iri (hb _ b3)
  obtain ⟨p1', p2'', hp1', hp2'', hs⟩ := holds_iri (hb _ b4)
  cases same hc1 hc1'; cases same hc2 hc2'; cases same hi hi'; cases same hp1 hp1'; cases same hp2 hp2''
  exact Holds.intro I hc1 rfl hc2 (hI.2.subClass_of _ _ (hI.2.restriction_class _ _ ho1)
    (hI.2.restriction_class _ _ ho2) fun x hx =>
      (hI.2.hasValue _ _ _ hv2 ho2 x).2 (hI.1.subProp_ext _ _ hs x i ((hI.2.hasValue _ _ _ hv1 ho1 x).1 hx)))

theorem scmSvf1_sound : scmSvf1.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨c1, y1, hc1, hy1, hs1⟩ := holds_iri (hb _ b0)
  obtain ⟨c1', p, hc1', hp, ho1⟩ := holds_iri (hb _ b1)
  obtain ⟨c2, y2, hc2, hy2, hs2⟩ := holds_iri (hb _ b2)
  obtain ⟨c2', p', hc2', hp', ho2⟩ := holds_iri (hb _ b3)
  obtain ⟨y1', y2', hy1', hy2', hsub⟩ := holds_iri (hb _ b4)
  cases same hc1 hc1'; cases same hc2 hc2'; cases same hp hp'; cases same hy1 hy1'; cases same hy2 hy2'
  exact Holds.intro I hc1 rfl hc2 (hI.2.subClass_of _ _ (hI.2.restriction_class _ _ ho1)
    (hI.2.restriction_class _ _ ho2) fun x hx => by
      obtain ⟨y, hxy, hyc⟩ := (hI.2.svf _ _ _ hs1 ho1 x).1 hx
      exact (hI.2.svf _ _ _ hs2 ho2 x).2 ⟨y, hxy, hI.1.subClass_ext _ _ hsub y hyc⟩)

theorem scmSvf2_sound : scmSvf2.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨c1, y, hc1, hy, hs1⟩ := holds_iri (hb _ b0)
  obtain ⟨c1', p1, hc1', hp1, ho1⟩ := holds_iri (hb _ b1)
  obtain ⟨c2, y', hc2, hy', hs2⟩ := holds_iri (hb _ b2)
  obtain ⟨c2', p2, hc2', hp2, ho2⟩ := holds_iri (hb _ b3)
  obtain ⟨p1', p2', hp1', hp2', hsub⟩ := holds_iri (hb _ b4)
  cases same hc1 hc1'; cases same hc2 hc2'; cases same hy hy'; cases same hp1 hp1'; cases same hp2 hp2'
  exact Holds.intro I hc1 rfl hc2 (hI.2.subClass_of _ _ (hI.2.restriction_class _ _ ho1)
    (hI.2.restriction_class _ _ ho2) fun x hx => by
      obtain ⟨z, hxz, hzc⟩ := (hI.2.svf _ _ _ hs1 ho1 x).1 hx
      exact (hI.2.svf _ _ _ hs2 ho2 x).2 ⟨z, hI.1.subProp_ext _ _ hsub x z hxz, hzc⟩)

theorem scmAvf1_sound : scmAvf1.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨c1, y1, hc1, hy1, ha1⟩ := holds_iri (hb _ b0)
  obtain ⟨c1', p, hc1', hp, ho1⟩ := holds_iri (hb _ b1)
  obtain ⟨c2, y2, hc2, hy2, ha2⟩ := holds_iri (hb _ b2)
  obtain ⟨c2', p', hc2', hp', ho2⟩ := holds_iri (hb _ b3)
  obtain ⟨y1', y2', hy1', hy2', hsub⟩ := holds_iri (hb _ b4)
  cases same hc1 hc1'; cases same hc2 hc2'; cases same hp hp'; cases same hy1 hy1'; cases same hy2 hy2'
  exact Holds.intro I hc1 rfl hc2 (hI.2.subClass_of _ _ (hI.2.restriction_class _ _ ho1)
    (hI.2.restriction_class _ _ ho2) fun x hx =>
      (hI.2.avf _ _ _ ha2 ho2 x).2 fun z hxz =>
        hI.1.subClass_ext _ _ hsub z ((hI.2.avf _ _ _ ha1 ho1 x).1 hx z hxz))

theorem scmAvf2_sound : scmAvf2.SoundIn OWLCore := by
  intro I hI A σ _ hb
  obtain ⟨c1, y, hc1, hy, ha1⟩ := holds_iri (hb _ b0)
  obtain ⟨c1', p1, hc1', hp1, ho1⟩ := holds_iri (hb _ b1)
  obtain ⟨c2, y', hc2, hy', ha2⟩ := holds_iri (hb _ b2)
  obtain ⟨c2', p2, hc2', hp2, ho2⟩ := holds_iri (hb _ b3)
  obtain ⟨p1', p2', hp1', hp2', hsub⟩ := holds_iri (hb _ b4)
  cases same hc1 hc1'; cases same hc2 hc2'; cases same hy hy'; cases same hp1 hp1'; cases same hp2 hp2'
  exact Holds.intro I hc2 rfl hc1 (hI.2.subClass_of _ _ (hI.2.restriction_class _ _ ho2)
    (hI.2.restriction_class _ _ ho1) fun x hx =>
      (hI.2.avf _ _ _ ha1 ho1 x).2 fun z hxz =>
        (hI.2.avf _ _ _ ha2 ho2 x).1 hx z (hI.1.subProp_ext _ _ hsub x z hxz))

/-! ## The rule set -/

theorem owlRLDerivationRules_sound : ∀ r ∈ owlRLDerivationRules, r.SoundIn OWLCore := by
  intro r hr
  simp only [owlRLDerivationRules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  all_goals first
    | exact eqRefS_sound
    | exact eqRefP_sound
    | exact eqRefO_sound
    | exact eqSym_sound
    | exact eqTrans_sound
    | exact eqRepS_sound
    | exact eqRepP_sound
    | exact eqRepO_sound
    | exact prpFp_sound
    | exact prpIfp_sound
    | exact prpSymp_sound
    | exact prpTrp_sound
    | exact prpEqp1_sound
    | exact prpEqp2_sound
    | exact prpInv1_sound
    | exact prpInv2_sound
    | exact clsSvf1_sound
    | exact clsSvf2_sound
    | exact clsAvf_sound
    | exact clsHv1_sound
    | exact clsHv2_sound
    | exact clsMaxc2_sound
    | exact clsMaxqc3_sound
    | exact clsMaxqc4_sound
    | exact caxEqc1_sound
    | exact caxEqc2_sound
    | exact scmCls1_sound
    | exact scmCls2_sound
    | exact scmCls3_sound
    | exact scmCls4_sound
    | exact scmEqc1a_sound
    | exact scmEqc1b_sound
    | exact scmEqc2_sound
    | exact scmOp1_sound
    | exact scmOp2_sound
    | exact scmDp1_sound
    | exact scmDp2_sound
    | exact scmEqp1a_sound
    | exact scmEqp1b_sound
    | exact scmEqp2_sound
    | exact scmDom1_sound
    | exact scmDom2_sound
    | exact scmRng1_sound
    | exact scmRng2_sound
    | exact scmHv_sound
    | exact scmSvf1_sound
    | exact scmSvf2_sound
    | exact scmAvf1_sound
    | exact scmAvf2_sound

theorem owlAxiomRules_sound : ∀ r ∈ owlAxioms.map RDFS.axiomRule, r.SoundIn OWLCore := by
  intro r hr
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hr
  intro I hI A _ _ _
  exact (holds_iri_iff I A _ _ _).2 (hI.2.axioms a ha)

-- @tg: implements:: [[openspec:owl-rl#OWL soundness]]
/-- Every rule of `owlRules` is sound in the OWL interpretations. -/
theorem owlRules_sound : ∀ r ∈ owlRules, r.SoundIn OWLCore := by
  intro r hr
  rcases List.mem_append.1 hr with hr | hr
  · exact (rdfsRules_sound r hr).mono fun _ h => h.1
  · rcases List.mem_append.1 hr with hr | hr
    · exact owlRLDerivationRules_sound r hr
    · exact owlAxiomRules_sound r hr

/-- Soundness: every triple derivable from `g` by `owlRules` is OWL-entailed by `g`. -/
theorem _root_.LeanRDF.Derives.owl_sound {g : Graph} {t : Triple} (h : Derives owlRules g t) :
    g.OWLEntails (Graph.singleton t) := by
  intro I hI hg
  refine Derives.satisfies_graph owlRules_sound (fun b => .bnode b) (fun u hu => ?_)
    I.toSimpleInterp hI.toCore (fun _ hx => hI.1.1.IP_IR hx) hg
  rw [Graph.mem_singleton] at hu
  subst hu
  rw [Triple.instantiate_bnode]
  exact h

/-- Soundness for graph queries: OWL entailment of `q` from derivations of its instance. -/
theorem _root_.LeanRDF.Derives.owl_sound_graph {g q : Graph} (μ : BlankNode → Term)
    (h : ∀ t ∈ q, Derives owlRules g (t.instantiate μ)) : g.OWLEntails q :=
  fun I hI hg => Derives.satisfies_graph owlRules_sound μ h I.toSimpleInterp hI.toCore
    (fun _ hx => hI.1.1.IP_IR hx) hg

end LeanRDF.Owl
