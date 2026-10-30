import LeanRDFShacl.Vocab

/-!
# Property paths

SHACL property paths (SHACL §2.3.1) and their value nodes. `ValueNode G p x y` is the path
relation as an inductive definition; `valueNodes G p x` computes the value nodes, with a
fixpoint for `sh:zeroOrMorePath` and `sh:oneOrMorePath`, and `valueNodes_iff` proves that it
lists exactly the `y` with `ValueNode G p x y`, each once.
-/

namespace LeanRDF.Shacl

/-- A SHACL property path (§2.3.1). Sequences and alternatives take lists. -/
inductive Path where
  | pred (p : IRI)
  | inv (p : Path)
  | seq (ps : List Path)
  | alt (ps : List Path)
  | zeroOrMore (p : Path)
  | oneOrMore (p : Path)
  | zeroOrOne (p : Path)
  deriving Inhabited, Repr

mutual
/-- Structural equality of paths. -/
def Path.beq : Path → Path → Bool
  | .pred p, .pred q => p == q
  | .inv p, .inv q => p.beq q
  | .seq ps, .seq qs => Path.beqList ps qs
  | .alt ps, .alt qs => Path.beqList ps qs
  | .zeroOrMore p, .zeroOrMore q => p.beq q
  | .oneOrMore p, .oneOrMore q => p.beq q
  | .zeroOrOne p, .zeroOrOne q => p.beq q
  | _, _ => false
def Path.beqList : List Path → List Path → Bool
  | [], [] => true
  | p :: ps, q :: qs => p.beq q && Path.beqList ps qs
  | _, _ => false
end

instance : BEq Path := ⟨Path.beq⟩

/-- The terms of a graph, in every position. -/
def graphTerms (G : Graph) : List Term := G.toList.flatMap fun t => [t.s, t.p, t.o]

/-! ## The path relation -/

-- @tg: implements:: [[openspec:shacl-core#SHACL Core semantics]] {note: "value nodes"}
/-- `y` is reached from `x` by the path (§2.3.1, the SPARQL 1.1 property path semantics). -/
inductive ValueNode (G : Graph) : Path → Term → Term → Prop
  | pred {p : IRI} {x y : Term} : ⟨x, .iri p, y⟩ ∈ G → ValueNode G (.pred p) x y
  | inv {p : Path} {x y : Term} : ValueNode G p y x → ValueNode G (.inv p) x y
  | seqNil {x : Term} : ValueNode G (.seq []) x x
  | seqCons {p : Path} {ps : List Path} {x z y : Term} :
      ValueNode G p x z → ValueNode G (.seq ps) z y → ValueNode G (.seq (p :: ps)) x y
  | alt {p : Path} {ps : List Path} {x y : Term} :
      p ∈ ps → ValueNode G p x y → ValueNode G (.alt ps) x y
  | starRefl {p : Path} {x : Term} : ValueNode G (.zeroOrMore p) x x
  | starTail {p : Path} {x z y : Term} :
      ValueNode G (.zeroOrMore p) x z → ValueNode G p z y → ValueNode G (.zeroOrMore p) x y
  | plus {p : Path} {x z y : Term} :
      ValueNode G (.zeroOrMore p) x z → ValueNode G p z y → ValueNode G (.oneOrMore p) x y
  | optNone {p : Path} {x : Term} : ValueNode G (.zeroOrOne p) x x
  | optSome {p : Path} {x y : Term} : ValueNode G p x y → ValueNode G (.zeroOrOne p) x y

/-- A path either stays put or moves between terms of the graph. -/
theorem ValueNode.ends {G : Graph} {p : Path} {x y : Term} (h : ValueNode G p x y) :
    x = y ∨ (x ∈ graphTerms G ∧ y ∈ graphTerms G) := by
  have hT : ∀ {t : Triple}, t ∈ G → t.s ∈ graphTerms G ∧ t.o ∈ graphTerms G := fun ht =>
    ⟨List.mem_flatMap.2 ⟨_, Graph.mem_toList.2 ht, by simp⟩,
     List.mem_flatMap.2 ⟨_, Graph.mem_toList.2 ht, by simp⟩⟩
  have tr : ∀ {a b c : Term}, (a = b ∨ (a ∈ graphTerms G ∧ b ∈ graphTerms G)) →
      (b = c ∨ (b ∈ graphTerms G ∧ c ∈ graphTerms G)) →
      a = c ∨ (a ∈ graphTerms G ∧ c ∈ graphTerms G) := by
    intro a b c h1 h2
    rcases h1 with rfl | ⟨h1, h1'⟩ <;> rcases h2 with rfl | ⟨h2, h2'⟩
    · exact .inl rfl
    · exact .inr ⟨h2, h2'⟩
    · exact .inr ⟨h1, h1'⟩
    · exact .inr ⟨h1, h2'⟩
  induction h with
  | pred h => exact .inr (hT h)
  | inv _ ih => rcases ih with rfl | ⟨a, b⟩; exact .inl rfl; exact .inr ⟨b, a⟩
  | seqNil => exact .inl rfl
  | seqCons _ _ ih1 ih2 => exact tr ih1 ih2
  | alt _ _ ih => exact ih
  | starRefl => exact .inl rfl
  | starTail _ _ ih1 ih2 => exact tr ih1 ih2
  | plus _ _ ih1 ih2 => exact tr ih1 ih2
  | optNone => exact .inl rfl
  | optSome _ ih => exact ih

/-! ## Lists without duplicates -/

/-- Append the elements of `l` that are not yet in `acc`, in order. -/
def addNew {α : Type} [DecidableEq α] (acc : List α) : List α → List α
  | [] => acc
  | a :: l => if a ∈ acc then addNew acc l else addNew (acc ++ [a]) l

/-- The elements of a list, each once, in order of first occurrence. -/
def uniq {α : Type} [DecidableEq α] (l : List α) : List α := addNew [] l

theorem mem_addNew {α : Type} [DecidableEq α] {acc l : List α} {a : α} : a ∈ addNew acc l ↔ a ∈ acc ∨ a ∈ l := by
  induction l generalizing acc with
  | nil => simp [addNew]
  | cons b l ih =>
    unfold addNew
    split
    · rename_i hb
      rw [ih, List.mem_cons]
      constructor
      · rintro (h | h)
        · exact .inl h
        · exact .inr (.inr h)
      · rintro (h | rfl | h)
        · exact .inl h
        · exact .inl hb
        · exact .inr h
    · rw [ih]
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      exact or_assoc

theorem nodup_addNew {α : Type} [DecidableEq α] {acc l : List α} (h : acc.Nodup) : (addNew acc l).Nodup := by
  induction l generalizing acc with
  | nil => exact h
  | cons b l ih =>
    unfold addNew
    split
    · exact ih h
    · rename_i hb
      refine ih (List.nodup_append.2 ⟨h, List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩)
      intro a ha c hc
      rw [List.mem_singleton] at hc
      subst hc
      exact fun e => hb (e ▸ ha)

theorem length_addNew_le {α : Type} [DecidableEq α] {acc l : List α} : acc.length ≤ (addNew acc l).length := by
  induction l generalizing acc with
  | nil => exact Nat.le_refl _
  | cons b l ih =>
    unfold addNew
    split
    · exact ih
    · exact Nat.le_trans (by simp) (ih (acc := acc ++ [b]))

/-- Something new makes the list longer. -/
theorem length_addNew_lt {α : Type} [DecidableEq α] {acc l : List α} {a : α} (ha : a ∈ l) (hn : a ∉ acc) :
    acc.length < (addNew acc l).length := by
  induction l generalizing acc with
  | nil => exact absurd ha List.not_mem_nil
  | cons b l ih =>
    unfold addNew
    split
    · rename_i hb
      rcases List.mem_cons.1 ha with rfl | ha
      · exact absurd hb hn
      · exact ih ha hn
    · exact Nat.lt_of_lt_of_le (by simp) (length_addNew_le (acc := acc ++ [b]))

@[simp] theorem mem_uniq {α : Type} [DecidableEq α] {l : List α} {a : α} : a ∈ uniq l ↔ a ∈ l := by
  simp [uniq, mem_addNew]

theorem nodup_uniq {α : Type} [DecidableEq α] (l : List α) : (uniq l).Nodup := nodup_addNew List.nodup_nil

/-! ## Reflexive-transitive closure by a fixpoint -/

/-- What `step` reaches from `x` in zero or more steps. -/
inductive Reach (step : Term → List Term) (x : Term) : Term → Prop
  | refl : Reach step x x
  | tail {y z : Term} : Reach step x y → z ∈ step y → Reach step x z

/-- Add the successors of every element until nothing changes, at most `n` times. -/
def closure (step : Term → List Term) : Nat → List Term → List Term
  | 0, S => S
  | n + 1, S =>
    let S' := addNew S (S.flatMap step)
    if S'.length = S.length then S else closure step n S'

/-- Within enough rounds, the closure is closed under `step` and reached from `x`. -/
theorem closure_spec {step : Term → List Term} {cand : List Term} {x : Term}
    (hcand : ∀ y ∈ cand, ∀ z ∈ step y, z ∈ cand) :
    ∀ (n : Nat) (S : List Term), x ∈ S → (∀ z ∈ S, Reach step x z) → S.Nodup → (∀ z ∈ S, z ∈ cand) →
      cand.length < n + S.length →
      x ∈ closure step n S ∧ (∀ z ∈ closure step n S, Reach step x z) ∧
        (∀ y ∈ closure step n S, ∀ z ∈ step y, z ∈ closure step n S) := by
  intro n
  induction n with
  | zero =>
    intro S hx hr hnd hsub hlen
    have := List.Nodup.length_le_of_subset hnd hsub
    exact absurd hlen (by simp at hlen ⊢; omega)
  | succ n ih =>
    intro S hx hr hnd hsub hlen
    simp only [closure]
    split
    · rename_i heq
      refine ⟨hx, hr, fun y hy z hz => ?_⟩
      apply Classical.byContradiction
      intro hn
      have := length_addNew_lt (acc := S) (List.mem_flatMap.2 ⟨y, hy, hz⟩) hn
      omega
    · rename_i hne
      have hle := length_addNew_le (acc := S) (l := S.flatMap step)
      refine ih _ (mem_addNew.2 (.inl hx)) ?_ (nodup_addNew hnd) ?_ (by omega)
      · intro z hz
        rcases mem_addNew.1 hz with hz | hz
        · exact hr z hz
        · obtain ⟨y, hy, hz⟩ := List.mem_flatMap.1 hz
          exact .tail (hr y hy) hz
      · intro z hz
        rcases mem_addNew.1 hz with hz | hz
        · exact hsub z hz
        · obtain ⟨y, hy, hz⟩ := List.mem_flatMap.1 hz
          exact hcand y (hsub y hy) z hz

/-- The closure from `x` holds exactly what `step` reaches from `x`. -/
theorem mem_closure_iff {step : Term → List Term} {cand : List Term} {x z : Term}
    (hcand : ∀ y ∈ cand, ∀ z ∈ step y, z ∈ cand) (hx : x ∈ cand) :
    z ∈ closure step (cand.length + 1) [x] ↔ Reach step x z := by
  obtain ⟨h1, h2, h3⟩ := closure_spec hcand (cand.length + 1) [x] (List.mem_singleton.2 rfl)
    (fun z hz => by rw [List.mem_singleton.1 hz]; exact .refl) (List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩)
    (fun z hz => by rw [List.mem_singleton.1 hz]; exact hx) (by simp only [List.length_singleton]; omega)
  refine ⟨h2 z, fun h => ?_⟩
  induction h with
  | refl => exact h1
  | tail _ hz ih => exact h3 _ ih _ hz

/-! ## Computing value nodes -/

mutual
/-- The value nodes of a path, possibly with repetitions. -/
def vn (G : Graph) : Path → Term → List Term
  | .pred p, x => (G.toList.filter fun t => t.s == x && t.p == .iri p).map (·.o)
  | .inv p, x => (x :: graphTerms G).filter fun y => (vn G p y).contains x
  | .seq ps, x => seqNodes G ps [x]
  | .alt ps, x => altNodes G ps x
  | .zeroOrMore p, x => closure (fun y => vn G p y) ((graphTerms G).length + 2) [x]
  | .oneOrMore p, x =>
    (closure (fun y => vn G p y) ((graphTerms G).length + 2) [x]).flatMap fun y => vn G p y
  | .zeroOrOne p, x => x :: vn G p x
/-- The value nodes of a sequence from each of a list of nodes. -/
def seqNodes (G : Graph) : List Path → List Term → List Term
  | [], S => S
  | p :: ps, S => seqNodes G ps (uniq (S.flatMap fun y => vn G p y))
/-- The value nodes of each alternative. -/
def altNodes (G : Graph) : List Path → Term → List Term
  | [], _ => []
  | p :: ps, x => vn G p x ++ altNodes G ps x
end

/-- The value nodes of a path from a node, each once (§2.3.1). -/
def valueNodes (G : Graph) (p : Path) (x : Term) : List Term := uniq (vn G p x)

private theorem reach_iff {G : Graph} {p : Path} (ih : ∀ x y, y ∈ vn G p x ↔ ValueNode G p x y)
    {x z : Term} : Reach (fun y => vn G p y) x z ↔ ValueNode G (.zeroOrMore p) x z := by
  constructor
  · intro h
    induction h with
    | refl => exact .starRefl
    | tail _ hz ih' => exact .starTail ih' ((ih _ _).1 hz)
  · intro h
    generalize hq : Path.zeroOrMore p = q at h
    induction h with
    | starRefl => exact .refl
    | starTail _ h2 ih1 =>
      cases hq
      exact .tail (ih1 rfl) ((ih _ _).2 h2)
    | _ => cases hq

private theorem star_cand {G : Graph} {p : Path} (ih : ∀ x y, y ∈ vn G p x ↔ ValueNode G p x y)
    (x : Term) : ∀ y ∈ x :: graphTerms G, ∀ z ∈ vn G p y, z ∈ x :: graphTerms G := by
  intro y hy z hz
  rcases ((ih _ _).1 hz).ends with rfl | ⟨_, hz⟩
  · exact hy
  · exact List.mem_cons_of_mem _ hz

mutual
theorem vn_iff (G : Graph) : ∀ (p : Path) (x y : Term), y ∈ vn G p x ↔ ValueNode G p x y
  | .pred q, x, y => by
    simp only [vn, List.mem_map, List.mem_filter, Graph.mem_toList, Bool.and_eq_true, beq_iff_eq]
    constructor
    · rintro ⟨⟨s, p, o⟩, ⟨ht, rfl, rfl⟩, rfl⟩
      exact .pred ht
    · intro h
      cases h with
      | pred h => exact ⟨_, ⟨h, rfl, rfl⟩, rfl⟩
  | .inv p, x, y => by
    have ih := vn_iff G p
    simp only [vn, List.mem_filter, List.contains_iff_mem]
    constructor
    · rintro ⟨-, h⟩
      exact .inv ((ih _ _).1 h)
    · intro h
      cases h with
      | inv h =>
        refine ⟨?_, (ih _ _).2 h⟩
        rcases h.ends with rfl | ⟨hy, _⟩
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ hy
  | .seq ps, x, y => by
    rw [vn, seqNodes_iff G ps [x] y]
    constructor
    · rintro ⟨x', hx', h⟩
      obtain rfl := List.mem_singleton.1 hx'; exact h
    · intro h; exact ⟨x, List.mem_singleton.2 rfl, h⟩
  | .alt ps, x, y => by
    rw [vn, altNodes_iff G ps x y]
    constructor
    · rintro ⟨q, hq, h⟩; exact .alt hq h
    · intro h
      cases h with
      | alt hq h => exact ⟨_, hq, h⟩
  | .zeroOrMore p, x, y => by
    have ih := vn_iff G p
    rw [vn, show (graphTerms G).length + 2 = (x :: graphTerms G).length + 1 by simp,
      mem_closure_iff (star_cand ih x) List.mem_cons_self, reach_iff ih]
  | .oneOrMore p, x, y => by
    have ih := vn_iff G p
    rw [vn, show (graphTerms G).length + 2 = (x :: graphTerms G).length + 1 by simp]
    simp only [List.mem_flatMap]
    constructor
    · rintro ⟨z, hz, hy⟩
      rw [mem_closure_iff (star_cand ih x) List.mem_cons_self, reach_iff ih] at hz
      exact .plus hz ((ih _ _).1 hy)
    · intro h
      cases h with
      | plus h1 h2 =>
        refine ⟨_, ?_, (ih _ _).2 h2⟩
        rw [mem_closure_iff (star_cand ih x) List.mem_cons_self, reach_iff ih]
        exact h1
  | .zeroOrOne p, x, y => by
    have ih := vn_iff G p
    rw [vn, List.mem_cons, ih]
    constructor
    · rintro (rfl | h)
      · exact .optNone
      · exact .optSome h
    · intro h
      cases h with
      | optNone => exact .inl rfl
      | optSome h => exact .inr h
theorem seqNodes_iff (G : Graph) : ∀ (ps : List Path) (S : List Term) (y : Term),
    y ∈ seqNodes G ps S ↔ ∃ x ∈ S, ValueNode G (.seq ps) x y
  | [], S, y => by
    rw [seqNodes]
    constructor
    · intro h; exact ⟨y, h, .seqNil⟩
    · rintro ⟨x, hx, h⟩
      cases h with
      | seqNil => exact hx
  | p :: ps, S, y => by
    rw [seqNodes, seqNodes_iff G ps]
    have ih := vn_iff G p
    constructor
    · rintro ⟨z, hz, h⟩
      obtain ⟨x, hx, hz⟩ := List.mem_flatMap.1 (mem_uniq.1 hz)
      exact ⟨x, hx, .seqCons ((ih _ _).1 hz) h⟩
    · rintro ⟨x, hx, h⟩
      cases h with
      | seqCons h1 h2 => exact ⟨_, mem_uniq.2 (List.mem_flatMap.2 ⟨x, hx, (ih _ _).2 h1⟩), h2⟩
theorem altNodes_iff (G : Graph) : ∀ (ps : List Path) (x y : Term),
    y ∈ altNodes G ps x ↔ ∃ p ∈ ps, ValueNode G p x y
  | [], x, y => by simp [altNodes]
  | p :: ps, x, y => by
    rw [altNodes, List.mem_append, vn_iff G p, altNodes_iff G ps]
    constructor
    · rintro (h | ⟨q, hq, h⟩)
      · exact ⟨p, List.mem_cons_self, h⟩
      · exact ⟨q, List.mem_cons_of_mem _ hq, h⟩
    · rintro ⟨q, hq, h⟩
      rcases List.mem_cons.1 hq with rfl | hq
      · exact .inl h
      · exact .inr ⟨q, hq, h⟩
end

-- @tg: implements:: [[openspec:shacl-core#Proven validator]] {note: "valueNodes_iff"}
/-- The computed value nodes are exactly those of the path relation. -/
theorem valueNodes_iff {G : Graph} {p : Path} {x y : Term} :
    y ∈ valueNodes G p x ↔ ValueNode G p x y := by
  rw [valueNodes, mem_uniq, vn_iff]

theorem valueNodes_nodup (G : Graph) (p : Path) (x : Term) : (valueNodes G p x).Nodup :=
  nodup_uniq _

end LeanRDF.Shacl
