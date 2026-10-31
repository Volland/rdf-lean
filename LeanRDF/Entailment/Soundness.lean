import LeanRDF.Entailment.Rules
import LeanRDF.Entailment.Derivation
import LeanRDF.Semantics.Entails

/-!
# Soundness

Every rule of `rdfsRules` is sound in every interpretation satisfying `RDFSCore`, so every
derivation is an RDFS entailment (RDF 1.1 Semantics §9.2.1 states the patterns; this file
proves them).
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
  simp only [rdfsExtraRules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · exact cmpType_sound
  · exact cmpDomain_sound
  · exact cmpRange_sound

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

/-- Soundness for graph queries: if every triple of `q`, with its blank nodes replaced by `μ`,
is derivable from `g`, then `g` RDFS-entails `q` (the blank nodes of `q` are existential,
RDF 1.1 Semantics §5.1 and §5.3). -/
theorem Derives.sound_graph {g q : Graph} (μ : BlankNode → Term)
    (h : ∀ t ∈ q, Derives rdfsRules g (t.instantiate μ)) : g.RDFSEntails q := by
  intro I hI ⟨A, hA, hg⟩
  refine ⟨instAssign I.toSimpleInterp A μ,
    instAssign_IR I.toSimpleInterp (fun _ hx => hI.1.IP_IR hx) A hA μ, fun t ht => ?_⟩
  exact holds_of_instantiate I.toSimpleInterp A μ
    (Derives.holds rdfsRules_sound I.toSimpleInterp hI.toCore A hg (h t ht))

end LeanRDF
