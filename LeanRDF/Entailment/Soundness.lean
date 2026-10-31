import LeanRDF.Entailment.Rules
import LeanRDF.Entailment.Derivation
import LeanRDF.Semantics.Entails

/-!
# Soundness

Every rule of `rdfsRules` is sound in every interpretation satisfying `RDFSCore`, so every
derivation is an RDFS entailment; every rule of `rdfRules` is sound under `RDFCore`, so every
derivation by them is an RDF entailment; and a query instance in the graph is a simple
entailment (RDF 1.2 Semantics §5.3, §8.1.1 and §9.2.1 state the patterns; this file proves
them).
-/

namespace LeanRDF

open Vocab RDFS

/-- A rule is sound in a class `C` of interpretations when, in every interpretation of `C` and
under every blank-node mapping, true body instances (with true guards) make the head instance
true. -/
def Rule.SoundIn (C : SimpleInterp → Prop) (r : Rule) : Prop :=
  ∀ (I : SimpleInterp), C I → ∀ (A : BlankNode → I.Dom) (σ : Subst),
    (∀ gd ∈ r.guards, gd.Holds σ) → (∀ b ∈ r.body, I.Holds A (b.apply σ)) →
    I.Holds A (r.head.apply σ)

/-- A rule is sound when it is sound in every interpretation with the core RDFS conditions. -/
def Rule.Sound (r : Rule) : Prop := r.SoundIn RDFSCore

/-- Soundness carries over to a smaller class of interpretations. -/
theorem Rule.SoundIn.mono {C C' : SimpleInterp → Prop} (h : ∀ I, C' I → C I) {r : Rule}
    (hr : r.SoundIn C) : r.SoundIn C' :=
  fun I hI => hr I (h I hI)

namespace SimpleInterp

variable {I : SimpleInterp} {A : BlankNode → I.Dom}

/-- Unpack a true triple `s p o` with a fixed IRI predicate. -/
theorem holds_iri {s o : Term} {p : IRI} (h : I.Holds A ⟨s, .iri p, o⟩) :
    ∃ s' o', I.denote A s = some s' ∧ I.denote A o = some o' ∧ I.IEXT (I.IS p) s' o' := by
  obtain ⟨s', p', o', hs, hp, ho, -, he⟩ := h
  simp only [denote_iri, Option.some.injEq] at hp
  subst hp
  exact ⟨s', o', hs, ho, he⟩

/-- Unpack a true triple. -/
theorem holds_any {s p o : Term} (h : I.Holds A ⟨s, p, o⟩) :
    ∃ s' p' o', I.denote A s = some s' ∧ I.denote A p = some p' ∧ I.denote A o = some o' ∧
      I.IEXT p' s' o' := by
  obtain ⟨s', p', o', hs, hp, ho, -, he⟩ := h
  exact ⟨s', p', o', hs, hp, ho, he⟩

end SimpleInterp

open SimpleInterp

/-- Two denotations of the same term agree. -/
theorem same {α : Type} {t : Option α} {x y : α} (hx : t = some x) (hy : t = some y) :
    x = y := by
  rw [hx] at hy; exact Option.some.inj hy

theorem rdfs2_sound : rdfs2.Sound := by
  intro I hI A σ _ hb
  obtain ⟨a, x, ha, hx, h1⟩ := holds_iri (hb _ (.head _))
  obtain ⟨y, a', z, hy, ha', hz, h2⟩ := holds_any (hb _ (.tail _ (.head _)))
  cases same ha ha'
  exact Holds.intro I hy rfl hx (hI.domain _ _ _ _ h1 h2)

theorem rdfs3_sound : rdfs3.Sound := by
  intro I hI A σ _ hb
  obtain ⟨a, x, ha, hx, h1⟩ := holds_iri (hb _ (.head _))
  obtain ⟨y, a', z, hy, ha', hz, h2⟩ := holds_any (hb _ (.tail _ (.head _)))
  cases same ha ha'
  exact Holds.intro I hz rfl hx (hI.range _ _ _ _ h1 h2)

theorem rdfs5_sound : rdfs5.Sound := by
  intro I hI A σ _ hb
  obtain ⟨x, y, hx, hy, h1⟩ := holds_iri (hb _ (.head _))
  obtain ⟨y', z, hy', hz, h2⟩ := holds_iri (hb _ (.tail _ (.head _)))
  cases same hy hy'
  exact Holds.intro I hx rfl hz (hI.subProp_trans _ _ _ h1 h2)

theorem rdfs7_sound : rdfs7.Sound := by
  intro I hI A σ _ hb
  obtain ⟨a, b, ha, hb', h1⟩ := holds_iri (hb _ (.head _))
  obtain ⟨x, a', y, hx, ha', hy, h2⟩ := holds_any (hb _ (.tail _ (.head _)))
  cases same ha ha'
  exact Holds.intro I hx hb' hy (hI.subProp_ext _ _ h1 _ _ h2)

theorem rdfs9_sound : rdfs9.Sound := by
  intro I hI A σ _ hb
  obtain ⟨x, y, hx, hy, h1⟩ := holds_iri (hb _ (.head _))
  obtain ⟨z, x', hz, hx', h2⟩ := holds_iri (hb _ (.tail _ (.head _)))
  cases same hx hx'
  exact Holds.intro I hz rfl hy (hI.subClass_ext _ _ h1 _ h2)

theorem rdfs11_sound : rdfs11.Sound := by
  intro I hI A σ _ hb
  obtain ⟨x, y, hx, hy, h1⟩ := holds_iri (hb _ (.head _))
  obtain ⟨y', z, hy', hz, h2⟩ := holds_iri (hb _ (.tail _ (.head _)))
  cases same hy hy'
  exact Holds.intro I hx rfl hz (hI.subClass_trans _ _ _ h1 h2)

/-- The basic rules (M3) are sound. -/
theorem rdfsBasicRules_sound : ∀ r ∈ rdfsBasicRules, r.Sound := by
  intro r hr
  simp only [rdfsBasicRules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact rdfs2_sound
  · exact rdfs3_sound
  · exact rdfs5_sound
  · exact rdfs7_sound
  · exact rdfs9_sound
  · exact rdfs11_sound

/-- The single premise of a one-premise rule. -/
private theorem prem {I : SimpleInterp} {A : BlankNode → I.Dom} {σ : Subst} {b : TPat}
    (hb : ∀ b' ∈ [b], I.Holds A (b'.apply σ)) : I.Holds A (b.apply σ) := hb b (.head _)

theorem rdfD2_sound : rdfD2.Sound := by
  intro I hI A σ _ hb
  obtain ⟨_, a, _, -, ha, -, h⟩ := holds_any (prem hb)
  exact Holds.intro I ha rfl rfl (hI.property _ (I.IEXT_wt _ _ _ h).1)

theorem rdfs4a_sound : rdfs4a.Sound := by
  intro I hI A σ _ hb
  obtain ⟨x, _, _, hx, -, -, h⟩ := holds_any (prem hb)
  exact Holds.intro I hx rfl rfl (hI.resource _ (I.IEXT_wt _ _ _ h).2.1)

theorem rdfs4b_sound : rdfs4b.Sound := by
  intro I hI A σ _ hb
  obtain ⟨_, _, y, -, -, hy, h⟩ := holds_any (prem hb)
  exact Holds.intro I hy rfl rfl (hI.resource _ (I.IEXT_wt _ _ _ h).2.2)

/-- Unpack a true `x rdf:type C` for a fixed class IRI `C`. -/
theorem holds_type {I : SimpleInterp} {A : BlankNode → I.Dom} {s : Term} {c : IRI}
    (h : I.Holds A ⟨s, .iri rdf.type, .iri c⟩) :
    ∃ x, I.denote A s = some x ∧ I.InClass x (I.IS c) := by
  obtain ⟨x, o, hx, ho, h⟩ := holds_iri h
  simp only [denote_iri, Option.some.injEq] at ho
  subst ho
  exact ⟨x, hx, h⟩

theorem rdfs6_sound : rdfs6.Sound := by
  intro I hI A σ _ hb
  obtain ⟨x, hx, h⟩ := holds_type (prem hb)
  exact Holds.intro I hx rfl hx (hI.prop_refl x h)

theorem rdfs8_sound : rdfs8.Sound := by
  intro I hI A σ _ hb
  obtain ⟨x, hx, h⟩ := holds_type (prem hb)
  exact Holds.intro I hx rfl rfl (hI.class_resource x h)

theorem rdfs10_sound : rdfs10.Sound := by
  intro I hI A σ _ hb
  obtain ⟨x, hx, h⟩ := holds_type (prem hb)
  exact Holds.intro I hx rfl hx (hI.subClass_refl x h)

theorem rdfs12_sound : rdfs12.Sound := by
  intro I hI A σ _ hb
  obtain ⟨x, hx, h⟩ := holds_type (prem hb)
  exact Holds.intro I hx rfl rfl (hI.cmp x h)

theorem rdfs13_sound : rdfs13.Sound := by
  intro I hI A σ _ hb
  obtain ⟨x, hx, h⟩ := holds_type (prem hb)
  exact Holds.intro I hx rfl rfl (hI.datatype_literal x h)

theorem grdfD1String_sound : grdfD1String.Sound := by
  intro I hI A σ hg hb
  obtain ⟨s, hs⟩ := hg (.stringLiteral "lll") (.head _)
  obtain ⟨_, _, o, -, -, ho, -⟩ := holds_any (prem hb)
  have ho' : I.denote A (σ "lll") = some o := ho
  rw [hs, denote_lit] at ho'
  refine Holds.intro I (s := o) ?_ rfl rfl (hI.string_lit s o ho')
  show I.denote A (σ "lll") = some o
  rw [hs, denote_lit]; exact ho'

theorem grdfD1Lang_sound : grdfD1Lang.Sound := by
  intro I hI A σ hg hb
  obtain ⟨s, t, hs⟩ := hg (.langLiteral "lll") (.head _)
  obtain ⟨_, _, o, -, -, ho, -⟩ := holds_any (prem hb)
  have ho' : I.denote A (σ "lll") = some o := ho
  rw [hs, denote_lit] at ho'
  refine Holds.intro I (s := o) ?_ rfl rfl (hI.lang_lit s t o ho')
  show I.denote A (σ "lll") = some o
  rw [hs, denote_lit]; exact ho'

theorem grdfD1DirLang_sound : grdfD1DirLang.Sound := by
  intro I hI A σ hg hb
  obtain ⟨s, t, d, hs⟩ := hg (.dirLangLiteral "lll") (.head _)
  obtain ⟨_, _, o, -, -, ho, -⟩ := holds_any (prem hb)
  have ho' : I.denote A (σ "lll") = some o := ho
  rw [hs, denote_lit] at ho'
  refine Holds.intro I (s := o) ?_ rfl rfl (hI.dirLang_lit s t d o ho')
  show I.denote A (σ "lll") = some o
  rw [hs, denote_lit]; exact ho'

/-- A triple term that denotes denotes a proposition (RDF 1.2 Semantics §9): its denotation is
`IT` on `IT`'s domain. -/
theorem tripleTerm_proposition {I : SimpleInterp} (hI : RDFSCore I) {A : BlankNode → I.Dom}
    {s p o : Term} {v : I.Dom} (h : I.denote A (.triple s p o) = some v) :
    I.InClass v (I.IS rdfs.Proposition) := by
  obtain ⟨x, y, z, -, -, -, hx, hy, hz, rfl⟩ := I.denote_triple.mp h
  exact hI.proposition x y z hx hy hz

theorem grdfs14S_sound : grdfs14S.Sound := by
  intro I hI A σ _ hb
  obtain ⟨x, _, _, hx, -, -, -⟩ := holds_any (prem hb)
  exact Holds.intro I hx rfl rfl (tripleTerm_proposition hI hx)

theorem grdfs14P_sound : grdfs14P.Sound := by
  intro I hI A σ _ hb
  obtain ⟨_, x, _, -, hx, -, -⟩ := holds_any (prem hb)
  exact Holds.intro I hx rfl rfl (tripleTerm_proposition hI hx)

theorem grdfs14O_sound : grdfs14O.Sound := by
  intro I hI A σ _ hb
  obtain ⟨_, _, x, -, -, hx, -⟩ := holds_any (prem hb)
  exact Holds.intro I hx rfl rfl (tripleTerm_proposition hI hx)

theorem grdfs14InS_sound : grdfs14InS.Sound := by
  intro I hI A σ _ hb
  obtain ⟨x, -, hx, -, -⟩ := holds_iri (prem hb)
  obtain ⟨y, _, _, hy, -, -, -⟩ := I.denote_triple.mp hx
  exact Holds.intro I hy rfl rfl (tripleTerm_proposition hI hy)

theorem grdfs14InP_sound : grdfs14InP.Sound := by
  intro I hI A σ _ hb
  obtain ⟨x, -, hx, -, -⟩ := holds_iri (prem hb)
  obtain ⟨_, y, _, -, hy, -, -⟩ := I.denote_triple.mp hx
  exact Holds.intro I hy rfl rfl (tripleTerm_proposition hI hy)

theorem grdfs14InO_sound : grdfs14InO.Sound := by
  intro I hI A σ _ hb
  obtain ⟨x, -, hx, -, -⟩ := holds_iri (prem hb)
  obtain ⟨_, _, y, -, -, hy, -⟩ := I.denote_triple.mp hx
  exact Holds.intro I hy rfl rfl (tripleTerm_proposition hI hy)

theorem rdfs14a_sound : rdfs14a.Sound := by
  intro I hI A σ _ _
  have hax := hI.axioms (rdf.type, rdf.type, rdf.Property) (by simp [Semantics.rdfAxioms])
  obtain ⟨hP, he⟩ := hax
  obtain ⟨-, hS, hO⟩ := I.IEXT_wt _ _ _ he
  have hd : I.denote A (.triple (.iri rdf.type) (.iri rdf.type) (.iri rdf.Property)) =
      some (I.IT (I.IS rdf.type) (I.IS rdf.type) (I.IS rdf.Property)) :=
    I.denote_triple.mpr ⟨_, _, _, rfl, rfl, rfl, hS, hP, hO, rfl⟩
  exact Holds.intro I hd rfl rfl (tripleTerm_proposition hI hd)

/-- The head of a container-membership rule is the axiom for `rdf:_n`. -/
private theorem cmp_head {I : SimpleInterp} {A : BlankNode → I.Dom} {σ : Subst} {p o : IRI}
    (hg : ∃ n, σ "ppp" = .iri (rdf.member (n + 1)))
    (hax : ∀ n, I.HoldsIRI (rdf.member (n + 1), p, o)) :
    I.Holds A ⟨σ "ppp", .iri p, .iri o⟩ := by
  obtain ⟨n, hn⟩ := hg
  rw [hn]
  exact (holds_iri_iff I A _ _ _).2 (hax n)

theorem cmpType_sound : cmpType.Sound := fun _ hI _ _ hg _ =>
  cmp_head (hg (.containerMembership "ppp") (.head _)) fun n => (hI.member_axioms n).1

theorem cmpDomain_sound : cmpDomain.Sound := fun _ hI _ _ hg _ =>
  cmp_head (hg (.containerMembership "ppp") (.head _)) fun n => (hI.member_axioms n).2.1

theorem cmpRange_sound : cmpRange.Sound := fun _ hI _ _ hg _ =>
  cmp_head (hg (.containerMembership "ppp") (.head _)) fun n => (hI.member_axioms n).2.2

/-- The other RDFS patterns are sound. -/
theorem rdfsExtraRules_sound : ∀ r ∈ rdfsExtraRules, r.Sound := by
  intro r hr
  simp only [rdfsExtraRules, propositionRules, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rdfD2_sound
  · exact rdfs4a_sound
  · exact rdfs4b_sound
  · exact rdfs6_sound
  · exact rdfs8_sound
  · exact rdfs10_sound
  · exact rdfs12_sound
  · exact rdfs13_sound
  · exact grdfD1String_sound
  · exact grdfD1Lang_sound
  · exact grdfD1DirLang_sound
  · exact cmpType_sound
  · exact cmpDomain_sound
  · exact cmpRange_sound
  · exact grdfs14S_sound
  · exact grdfs14P_sound
  · exact grdfs14O_sound
  · exact grdfs14InS_sound
  · exact grdfs14InP_sound
  · exact grdfs14InO_sound
  · exact rdfs14a_sound

/-- Every axiomatic-triple rule is sound: its head is an axiom of every RDFS interpretation. -/
theorem axiomRules_sound : ∀ r ∈ axiomRules, r.Sound := by
  intro r hr
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hr
  intro I hI A _ _ _
  exact (holds_iri_iff I A _ _ _).2 (hI.axioms a ha)

/-- Every rule of `rdfsRules` is sound. -/
theorem rdfsRules_sound : ∀ r ∈ rdfsRules, r.Sound := by
  intro r hr
  rcases List.mem_append.1 hr with hr | hr
  · rcases List.mem_append.1 hr with hr | hr
    · exact rdfsBasicRules_sound r hr
    · exact rdfsExtraRules_sound r hr
  · exact axiomRules_sound r hr

/-! ## The RDF regime -/

theorem rdfD2_sound_rdf : rdfD2.SoundIn RDFCore := by
  intro I hI A σ _ hb
  obtain ⟨_, a, _, -, ha, -, h⟩ := holds_any (prem hb)
  exact Holds.intro I ha rfl rfl (hI.property _ (I.IEXT_wt _ _ _ h).1)

/-- A GrdfD1 rule is sound under `RDFCore` when the class of the guarded literal is. -/
private theorem grdfD1_sound_rdf {r : Rule} {c : IRI} (hbody : r.body = [⟨.var "xxx", .var "aaa", .var "lll"⟩])
    (hhead : r.head = ⟨.var "lll", .const (.iri rdf.type), .const (.iri c)⟩)
    (hlit : ∀ (I : SimpleInterp), RDFCore I → ∀ (A : BlankNode → I.Dom) (σ : Subst),
      (∀ gd ∈ r.guards, gd.Holds σ) → ∀ x, I.denote A (σ "lll") = some x → I.InClass x (I.IS c)) :
    r.SoundIn RDFCore := by
  intro I hI A σ hg hb
  rw [hbody] at hb
  obtain ⟨_, _, o, -, -, ho, -⟩ := holds_any (prem hb)
  rw [hhead]
  exact Holds.intro I ho rfl rfl (hlit I hI A σ hg o ho)

theorem grdfD1String_sound_rdf : grdfD1String.SoundIn RDFCore :=
  grdfD1_sound_rdf rfl rfl fun I hI A σ hg x hx => by
    obtain ⟨s, hs⟩ := hg (.stringLiteral "lll") (.head _)
    rw [hs, denote_lit] at hx
    exact hI.string_lit s x hx

theorem grdfD1Lang_sound_rdf : grdfD1Lang.SoundIn RDFCore :=
  grdfD1_sound_rdf rfl rfl fun I hI A σ hg x hx => by
    obtain ⟨s, t, hs⟩ := hg (.langLiteral "lll") (.head _)
    rw [hs, denote_lit] at hx
    exact hI.lang_lit s t x hx

theorem grdfD1DirLang_sound_rdf : grdfD1DirLang.SoundIn RDFCore :=
  grdfD1_sound_rdf rfl rfl fun I hI A σ hg x hx => by
    obtain ⟨s, t, d, hs⟩ := hg (.dirLangLiteral "lll") (.head _)
    rw [hs, denote_lit] at hx
    exact hI.dirLang_lit s t d x hx

theorem cmpProperty_sound_rdf : cmpProperty.SoundIn RDFCore := fun _ hI _ _ hg _ =>
  cmp_head (hg (.containerMembership "ppp") (.head _)) hI.member_axioms

-- @tg: implements:: [[openspec:rdfs-entailment#Regime rule sets]] {since: "0.2.0"}
/-- Every rule of `rdfRules` is sound under the RDF core conditions. -/
theorem rdfRules_sound : ∀ r ∈ rdfRules, r.SoundIn RDFCore := by
  intro r hr
  rcases List.mem_append.1 hr with hr | hr
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact rdfD2_sound_rdf
    · exact grdfD1String_sound_rdf
    · exact grdfD1Lang_sound_rdf
    · exact grdfD1DirLang_sound_rdf
    · exact cmpProperty_sound_rdf
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hr
    intro I hI A _ _ _
    exact (holds_iri_iff I A _ _ _).2 (hI.axioms a ha)

/-- A derivation by rules sound in `C` is true, in every interpretation of `C`, under any
blank-node mapping that makes the graph true. -/
theorem Derives.holdsIn {C : SimpleInterp → Prop} {rules : List Rule} {g : Graph} {t : Triple}
    (hr : ∀ r ∈ rules, r.SoundIn C) (I : SimpleInterp) (hI : C I) (A : BlankNode → I.Dom)
    (hg : ∀ u ∈ g, I.Holds A u) (h : Derives rules g t) : I.Holds A t := by
  induction h with
  | fact hu => exact hg _ hu
  | apply r σ hmem hgd _ ih => exact hr r hmem I hI A σ hgd ih

/-- A derivation by sound rules is true under any blank-node mapping that makes the graph true. -/
theorem Derives.holds {rules : List Rule} {g : Graph} {t : Triple} (hr : ∀ r ∈ rules, r.Sound)
    (I : SimpleInterp) (hI : RDFSCore I) (A : BlankNode → I.Dom) (hg : ∀ u ∈ g, I.Holds A u)
    (h : Derives rules g t) : I.Holds A t :=
  Derives.holdsIn hr I hI A hg h

-- @tg: implements:: [[openspec:rdfs-entailment#Soundness]]
/-- Soundness (the key theorem): every triple derivable from `g` by `rdfsRules` is RDFS-entailed
by `g` (RDF 1.1 Semantics §9.2). -/
theorem Derives.sound {g : Graph} {t : Triple} (h : Derives rdfsRules g t) :
    g.RDFSEntails (Graph.singleton t) := by
  intro I hI ⟨A, hA, hg⟩
  refine ⟨A, hA, fun u hu => ?_⟩
  rw [Graph.mem_singleton] at hu
  subst hu
  exact Derives.holds rdfsRules_sound I.toSimpleInterp hI.toCore A hg h

/-- The value a blank node takes under an instance mapping: the denotation of its image, or an
arbitrary resource if that does not denote. -/
private noncomputable def instAssign (I : SimpleInterp) (A : BlankNode → I.Dom)
    (μ : BlankNode → Term) (b : BlankNode) : I.Dom :=
  match I.denote A (μ b) with
  | some d => d
  | none => Classical.choose I.IR_nonempty

private theorem instAssign_IR (I : SimpleInterp) (hPR : ∀ x, I.IP x → I.IR x)
    (A : BlankNode → I.Dom) (hA : ∀ b, I.IR (A b)) (μ : BlankNode → Term) (b : BlankNode) :
    I.IR (instAssign I A μ b) := by
  unfold instAssign
  split
  · rename_i d hd
    cases hμ : μ b with
    | iri i =>
      rw [hμ, denote_iri, Option.some.injEq] at hd; subst hd
      exact (I.IS_wt i).elim id (hPR _)
    | bnode b' => rw [hμ, denote_bnode, Option.some.injEq] at hd; subst hd; exact hA b'
    | lit l => rw [hμ, denote_lit] at hd; exact I.IL_wt l d hd
    | triple s p o =>
      rw [hμ] at hd
      obtain ⟨x, y, z, -, -, -, hx, hy, hz, rfl⟩ := I.denote_triple.mp hd
      exact I.IT_wt x y z hx hy hz
  · exact Classical.choose_spec I.IR_nonempty

private theorem denote_instantiate (I : SimpleInterp) (A : BlankNode → I.Dom)
    (μ : BlankNode → Term) {u : Term} {d : I.Dom} (h : I.denote A (u.instantiate μ) = some d) :
    I.denote (instAssign I A μ) u = some d := by
  induction u generalizing d with
  | bnode b =>
    simp only [Term.instantiate] at h
    simp only [denote_bnode, instAssign, h]
  | iri i => exact h
  | lit l => exact h
  | triple s p o ihs ihp iho =>
    simp only [Term.instantiate] at h
    obtain ⟨x, y, z, hs, hp, ho, hx, hy, hz, rfl⟩ := I.denote_triple.mp h
    exact I.denote_triple.mpr ⟨x, y, z, ihs hs, ihp hp, iho ho, hx, hy, hz, rfl⟩

private theorem holds_of_instantiate (I : SimpleInterp) (A : BlankNode → I.Dom)
    (μ : BlankNode → Term) {t : Triple} (h : I.Holds A (t.instantiate μ)) :
    I.Holds (instAssign I A μ) t := by
  obtain ⟨s, p, o, hs, hp, ho, hP, he⟩ := h
  exact ⟨s, p, o, denote_instantiate I A μ hs, denote_instantiate I A μ hp,
    denote_instantiate I A μ ho, hP, he⟩

/-- Soundness for graph queries in any class of interpretations whose properties are resources:
if every triple of `q`, with its blank nodes replaced by `μ`, is derivable from `g` by rules
sound in `C`, then every interpretation of `C` that satisfies `g` satisfies `q`. -/
theorem Derives.satisfies_graph {C : SimpleInterp → Prop} {rules : List Rule}
    (hr : ∀ r ∈ rules, r.SoundIn C) {g q : Graph} (μ : BlankNode → Term)
    (h : ∀ t ∈ q, Derives rules g (t.instantiate μ)) (I : SimpleInterp) (hC : C I)
    (hPR : ∀ x, I.IP x → I.IR x) (hg : I.Satisfies g) : I.Satisfies q := by
  obtain ⟨A, hA, hg⟩ := hg
  exact ⟨instAssign I A μ, instAssign_IR I hPR A hA μ, fun t ht =>
    holds_of_instantiate I A μ (Derives.holdsIn hr I hC A hg (h t ht))⟩

/-- Soundness for graph queries in RDF entailment: if every triple of `q`, with its blank nodes
replaced by `μ`, is derivable from `g` by `rdfRules`, then `g` RDF-entails `q`. -/
theorem Derives.sound_graph_rdf {g q : Graph} (μ : BlankNode → Term)
    (h : ∀ t ∈ q, Derives rdfRules g (t.instantiate μ)) : g.RDFEntails q := by
  intro I hI hg
  exact Derives.satisfies_graph rdfRules_sound μ h I.toSimpleInterp hI.toRDFCore
    (fun _ hx => RDFConditions.IP_IR hI hx) hg

/-! ## The simple regime -/

open Classical in
/-- A blank-node mapping for a simple interpretation: the denotation of the image under `μ` when
it is a resource, an arbitrary resource otherwise. Simple interpretations do not make every
property a resource, so the image is used only where it is one. -/
private noncomputable def safeAssign (I : SimpleInterp) (A : BlankNode → I.Dom)
    (μ : BlankNode → Term) (b : BlankNode) : I.Dom :=
  if h : ∃ d, I.denote A (μ b) = some d ∧ I.IR d then Classical.choose h
  else Classical.choose I.IR_nonempty

private theorem safeAssign_IR (I : SimpleInterp) (A : BlankNode → I.Dom) (μ : BlankNode → Term)
    (b : BlankNode) : I.IR (safeAssign I A μ b) := by
  unfold safeAssign
  split
  · rename_i h; exact (Classical.choose_spec h).2
  · exact Classical.choose_spec I.IR_nonempty

private theorem safeAssign_eq {I : SimpleInterp} {A : BlankNode → I.Dom} {μ : BlankNode → Term}
    {b : BlankNode} {d : I.Dom} (hd : I.denote A (μ b) = some d) (hr : I.IR d) :
    safeAssign I A μ b = d := by
  have h : ∃ d, I.denote A (μ b) = some d ∧ I.IR d := ⟨d, hd, hr⟩
  unfold safeAssign
  rw [dif_pos h]
  exact Option.some.inj ((Classical.choose_spec h).1.symm.trans hd)

private theorem isObject_of_isSubject {t : Term} (h : t.isSubject = true) : t.isObject = true := by
  cases t <;> simp_all [Term.isSubject, Term.isObject]

/-- A term in a strict object position (RDF 1.2 Concepts §3.1) whose instance denotes a resource
denotes the same resource under `safeAssign`: every blank node in it sits where a resource
is required. -/
private theorem denote_safe (I : SimpleInterp) (A : BlankNode → I.Dom) (μ : BlankNode → Term) :
    ∀ {u : Term} {d : I.Dom}, u.isObject = true → I.denote A (u.instantiate μ) = some d →
      I.IR d → I.denote (safeAssign I A μ) u = some d
  | .iri _, _, _, h, _ => h
  | .lit _, _, _, h, _ => h
  | .bnode b, d, _, h, hr => by
    simp only [Term.instantiate] at h
    simp only [denote_bnode, safeAssign_eq h hr]
  | .triple s p o, _, hu, h, _ => by
    simp only [Term.isObject, Bool.and_eq_true] at hu
    obtain ⟨⟨hs, hp⟩, ho⟩ := hu
    simp only [Term.instantiate] at h
    obtain ⟨x, y, z, hsx, hpy, hoz, hx, hy, hz, rfl⟩ := I.denote_triple.mp h
    cases p with
    | iri i =>
      exact I.denote_triple.mpr ⟨x, y, z, denote_safe I A μ (isObject_of_isSubject hs) hsx hx,
        hpy, denote_safe I A μ ho hoz hz, hx, hy, hz, rfl⟩
    | _ => simp [Term.isPredicate] at hp

-- @tg: implements:: [[openspec:rdfs-entailment#Regime rule sets]] {since: "0.2.0"}
/-- Soundness for graph queries in simple entailment (the interpolation lemma, RDF 1.2 Semantics
§5.3): if every triple of a well-formed query `q`, with its blank nodes replaced by `μ`, is in
`g`, then `g` simply entails `q`. -/
theorem Derives.sound_graph_simple {g q : Graph} (μ : BlankNode → Term)
    (hq : ∀ t ∈ q, t.WellFormed) (h : ∀ t ∈ q, t.instantiate μ ∈ g) : g.SimpleEntails q := by
  intro I ⟨A, _, hg⟩
  refine ⟨safeAssign I A μ, safeAssign_IR I A μ, fun t ht => ?_⟩
  obtain ⟨s', p', o', hs, hp, ho, hP, he⟩ := hg _ (h t ht)
  have hw := hq t ht
  simp only [Triple.WellFormed, Bool.and_eq_true] at hw
  obtain ⟨⟨hws, hwp⟩, hwo⟩ := hw
  obtain ⟨-, hrs, hro⟩ := I.IEXT_wt _ _ _ he
  have hp' : I.denote (safeAssign I A μ) t.p = some p' := by
    obtain ⟨_, p, _⟩ := t
    cases p with
    | iri i => exact hp
    | _ => simp [Term.isPredicate] at hwp
  exact ⟨s', p', o', denote_safe I A μ (isObject_of_isSubject hws) hs hrs, hp',
    denote_safe I A μ hwo ho hro, hP, he⟩

/-- A derivation from no rules is membership. -/
theorem Derives.mem_of_nil {g : Graph} {t : Triple} (h : Derives [] g t) : t ∈ g := by
  cases h with
  | fact h => exact h
  | apply r _ hr _ _ => exact absurd hr List.not_mem_nil

/-- Soundness for graph queries: if every triple of `q`, with its blank nodes replaced by `μ`,
is derivable from `g`, then `g` RDFS-entails `q` (the blank nodes of `q` are existential,
RDF 1.2 Semantics §5.1 and §5.3). -/
theorem Derives.sound_graph {g q : Graph} (μ : BlankNode → Term)
    (h : ∀ t ∈ q, Derives rdfsRules g (t.instantiate μ)) : g.RDFSEntails q := by
  intro I hI ⟨A, hA, hg⟩
  refine ⟨instAssign I.toSimpleInterp A μ,
    instAssign_IR I.toSimpleInterp (fun _ hx => hI.1.IP_IR hx) A hA μ, fun t ht => ?_⟩
  exact holds_of_instantiate I.toSimpleInterp A μ
    (Derives.holds rdfsRules_sound I.toSimpleInterp hI.toCore A hg (h t ht))

end LeanRDF
