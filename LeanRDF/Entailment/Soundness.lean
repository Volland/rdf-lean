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

/-- A rule is sound when, in every interpretation with the core RDFS conditions and under every
blank-node mapping, true body instances (with true guards) make the head instance true. -/
def Rule.Sound (r : Rule) : Prop :=
  ∀ (I : SimpleInterp), RDFSCore I → ∀ (A : BlankNode → I.Dom) (σ : Subst),
    (∀ gd ∈ r.guards, gd.Holds σ) → (∀ b ∈ r.body, I.Holds A (b.apply σ)) →
    I.Holds A (r.head.apply σ)

namespace SimpleInterp

variable {I : SimpleInterp} {A : BlankNode → I.Dom}

/-- Unpack a true triple `s p o` with a fixed IRI predicate. -/
private theorem holds_iri {s o : Term} {p : IRI} (h : I.Holds A ⟨s, .iri p, o⟩) :
    ∃ s' o', I.denote A s = some s' ∧ I.denote A o = some o' ∧ I.IEXT (I.IS p) s' o' := by
  obtain ⟨s', p', o', hs, hp, ho, -, he⟩ := h
  simp only [denote_iri, Option.some.injEq] at hp
  subst hp
  exact ⟨s', o', hs, ho, he⟩

/-- Unpack a true triple. -/
private theorem holds_any {s p o : Term} (h : I.Holds A ⟨s, p, o⟩) :
    ∃ s' p' o', I.denote A s = some s' ∧ I.denote A p = some p' ∧ I.denote A o = some o' ∧
      I.IEXT p' s' o' := by
  obtain ⟨s', p', o', hs, hp, ho, -, he⟩ := h
  exact ⟨s', p', o', hs, hp, ho, he⟩

end SimpleInterp

open SimpleInterp

/-- Two denotations of the same term agree. -/
private theorem same {α : Type} {t : Option α} {x y : α} (hx : t = some x) (hy : t = some y) :
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

/-- Every rule of `rdfsRules` is sound. -/
theorem rdfsRules_sound : ∀ r ∈ rdfsRules, r.Sound := by
  intro r hr
  simp only [rdfsRules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact rdfs2_sound
  · exact rdfs3_sound
  · exact rdfs5_sound
  · exact rdfs7_sound
  · exact rdfs9_sound
  · exact rdfs11_sound

/-- A derivation by sound rules is true under any blank-node mapping that makes the graph true. -/
theorem Derives.holds {rules : List Rule} {g : Graph} {t : Triple} (hr : ∀ r ∈ rules, r.Sound)
    (I : SimpleInterp) (hI : RDFSCore I) (A : BlankNode → I.Dom) (hg : ∀ u ∈ g, I.Holds A u)
    (h : Derives rules g t) : I.Holds A t := by
  induction h with
  | fact hu => exact hg _ hu
  | apply r σ hmem hgd _ ih => exact hr r hmem I hI A σ hgd ih

-- @tg: implements:: [[openspec:rdfs-entailment#Soundness]]
/-- Soundness (the key theorem): every triple derivable from `g` by `rdfsRules` is RDFS-entailed
by `g` (RDF 1.1 Semantics §9.2). -/
theorem Derives.sound {g : Graph} {t : Triple} (h : Derives rdfsRules g t) :
    g.RDFSEntails (Graph.singleton t) := by
  intro I hI ⟨A, hA, hg⟩
  refine ⟨A, hA, fun u hu => ?_⟩
  rw [Graph.mem_singleton] at hu
  subst hu
  exact Derives.holds rdfsRules_sound I.toSimpleInterp hI.2.toCore A hg h

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
  · exact Classical.choose_spec I.IR_nonempty

private theorem denote_instantiate (I : SimpleInterp) (A : BlankNode → I.Dom)
    (μ : BlankNode → Term) {u : Term} {d : I.Dom} (h : I.denote A (u.instantiate μ) = some d) :
    I.denote (instAssign I A μ) u = some d := by
  cases u with
  | bnode b =>
    simp only [Term.instantiate] at h
    simp only [denote_bnode, instAssign, h]
  | iri i => exact h
  | lit l => exact h

private theorem holds_of_instantiate (I : SimpleInterp) (A : BlankNode → I.Dom)
    (μ : BlankNode → Term) {t : Triple} (h : I.Holds A (t.instantiate μ)) :
    I.Holds (instAssign I A μ) t := by
  obtain ⟨s, p, o, hs, hp, ho, hP, he⟩ := h
  exact ⟨s, p, o, denote_instantiate I A μ hs, denote_instantiate I A μ hp,
    denote_instantiate I A μ ho, hP, he⟩

/-- Soundness for graph queries: if every triple of `q`, with its blank nodes replaced by `μ`,
is derivable from `g`, then `g` RDFS-entails `q` (the blank nodes of `q` are existential,
RDF 1.1 Semantics §5.1 and §5.3). -/
theorem Derives.sound_graph {g q : Graph} (μ : BlankNode → Term)
    (h : ∀ t ∈ q, Derives rdfsRules g (t.instantiate μ)) : g.RDFSEntails q := by
  intro I hI ⟨A, hA, hg⟩
  refine ⟨instAssign I.toSimpleInterp A μ,
    instAssign_IR I.toSimpleInterp (fun _ hx => hI.1.IP_IR hx) A hA μ, fun t ht => ?_⟩
  exact holds_of_instantiate I.toSimpleInterp A μ
    (Derives.holds rdfsRules_sound I.toSimpleInterp hI.2.toCore A hg (h t ht))

end LeanRDF
