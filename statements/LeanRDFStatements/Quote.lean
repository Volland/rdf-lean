import LeanRDFStatements.Kernel
import LeanRDFStatements.Abstract.Quoting

/-!
# The quoting view

The paper's quoting map on a statement graph: a record becomes the triple term of its content,
with every eid reference replaced by the quoted triple term of the referenced record. Triple
terms then appear as subjects, so the result is generalized RDF 1.2, not strict. `quote` computes
it on the kernel; `quote_sound` proves that it computes the paper's `Quotes` relation, and the
paper's results on that relation (`quotes_total`, `quotes_functional`, `quotes_injective_iff`)
hold for statement graphs as instantiated below.
-/

namespace LeanRDF.Statements

open StatementExport

/-- A quoted value as an RDF term: a leaf is its term, a quoted triple a triple term. -/
def qtTerm : QT Term → Term
  | .leaf l => l
  | .triple s p o => .triple (qtTerm s) p (qtTerm o)

namespace StatementGraph

/-- Quote a node with `fuel` levels of nesting. -/
def quoteNode (g : StatementGraph) (f : Nat) (n : Node) : Option Term :=
  match n with
  | .term t => some t
  | .eid e =>
    match f with
    | 0 => none
    | f + 1 =>
      match g.find? e with
      | none => none
      | some r =>
        match g.quoteNode f r.s, g.quoteNode f r.o with
        | some s, some o => some (.triple s (.iri r.p) o)
        | _, _ => none

-- @tg: implements:: [[openspec:statement-graphs#Quoting view]]
/-- The quoted triple term of a record, or an error when it is outside the kernel. -/
def quote (g : StatementGraph) (e : Nat) : Except String Term :=
  match g.quoteNode (g.eids.length + 1) (.eid e) with
  | some t => .ok t
  | none => .error s!"statement {e} is outside the kernel: it references a missing statement or lies on a cycle"

/-- What `quoteNode` computes is the paper's quoting relation. -/
theorem quoteNode_sound (g : StatementGraph) :
    ∀ (f : Nat) {n : Node} {t : Term}, g.quoteNode f n = some t →
      ∃ q, Quotes g.content id g.S n q ∧ qtTerm q = t := by
  intro f
  induction f with
  | zero =>
    intro n t h
    cases n with
    | term t' => exact ⟨.leaf t', .term t', Option.some.inj h⟩
    | eid e => simp [quoteNode] at h
  | succ f ih =>
    intro n t h
    cases n with
    | term t' => exact ⟨.leaf t', .term t', Option.some.inj h⟩
    | eid e =>
      cases hr : g.find? e with
      | none => simp [quoteNode, hr] at h
      | some r =>
        cases hs : g.quoteNode f r.s with
        | none => simp [quoteNode, hr, hs] at h
        | some ts =>
          cases ho : g.quoteNode f r.o with
          | none => simp [quoteNode, hr, hs, ho] at h
          | some to =>
            simp only [quoteNode, hr, hs, ho, Option.some.injEq] at h
            subst h
            obtain ⟨hmem, rfl⟩ := mem_of_find? hr
            obtain ⟨qs, hqs, rfl⟩ := ih hs
            obtain ⟨qo, hqo, rfl⟩ := ih ho
            have hc := content_of_mem hmem
            refine ⟨.triple qs (id (g.content r.eid).p) qo, .eid (mem_eids.2 ⟨r, hmem, rfl⟩)
              (by rw [hc]; exact hqs) (by rw [hc]; exact hqo), ?_⟩
            simp [qtTerm, hc, Record.content]

theorem quote_sound {g : StatementGraph} {e : Nat} {t : Term} (h : g.quote e = .ok t) :
    ∃ q, Quotes g.content id g.S (.eid e) q ∧ qtTerm q = t := by
  unfold quote at h
  split at h
  · rename_i ht; cases h; exact quoteNode_sound g _ ht
  · cases h

/-- With enough fuel, a member of `F_S^k(∅)` is quoted. -/
private theorem quoteNode_of_iter (g : StatementGraph) :
    ∀ {k : Nat} {e : Nat}, iter (crefs g.content) g.S k e → ∃ t, g.quoteNode k (.eid e) = some t
  | 0, _, h => h.elim
  | k + 1, e, h => by
    obtain ⟨he, hrefs⟩ := h
    obtain ⟨r, hr, rfl⟩ := mem_eids.1 he
    have node : ∀ n : Node, (∀ y, n = .eid y → y ∈ r.refs) → ∃ t, g.quoteNode k n = some t := by
      intro n hn
      cases n with
      | term t => exact ⟨t, by simp [quoteNode]⟩
      | eid y =>
        have := hrefs y (by rw [crefs_of_mem hr]; exact hn y rfl)
        exact quoteNode_of_iter g this
    obtain ⟨ts, hs⟩ := node r.s (fun y hy => by simp [Record.refs, hy, StatementExport.Node.refs])
    obtain ⟨to, ho⟩ := node r.o (fun y hy => by simp [Record.refs, hy, StatementExport.Node.refs])
    exact ⟨_, by simp [quoteNode, find?_of_mem hr, hs, ho]; rfl⟩

/-- Every record of the kernel is quoted. -/
theorem quote_kernel {g : StatementGraph} {e : Nat} (h : e ∈ g.kernel) : ∃ t, g.quote e = .ok t := by
  obtain ⟨t, ht⟩ := quoteNode_of_iter g (mem_peel.1 h)
  exact ⟨t, by simp [quote, ht]⟩

/-! ## The paper's quoting results, instantiated -/

theorem quotes_total' (g : StatementGraph) (hC : g.isClosed = true) (hA : g.isAcyclic = true)
    {e : Nat} (he : g.S e) : ∃ q : QT Term, Quotes g.content id g.S (.eid e) q :=
  quotes_total g.covered ((isClosed_iff g).1 hC) ((isAcyclic_iff g).1 hA) he

theorem quotes_functional' (g : StatementGraph) {n : Node} {q q' : QT Term}
    (h : Quotes g.content id g.S n q) (h' : Quotes g.content id g.S n q') : q = q' :=
  quotes_functional h h'

/-- Quoting is injective on a closed, acyclic graph exactly when no two records have the same
content (`quotes_injective_iff`). -/
theorem quotes_injective' (g : StatementGraph) (hC : g.isClosed = true) (hA : g.isAcyclic = true) :
    (∀ x y (q : QT Term), Quotes g.content id g.S (.eid x) q → Quotes g.content id g.S (.eid y) q →
      x = y) ↔ (∀ x y, g.S x → g.S y → g.content x = g.content y → x = y) :=
  quotes_injective_iff (fun _ _ e => e) g.covered ((isClosed_iff g).1 hC) ((isAcyclic_iff g).1 hA)

/-- Basic graph patterns have the same solutions over the asserted records `A` and over their
quoted image, under set semantics (`bgp_view`, the paper's `prop:queries` (iii)). -/
theorem bgp_view' (g : StatementGraph) {V : Type}
    (hd : ∀ x y, g.S x → g.S y → g.content x = g.content y → x = y) {A : Nat → Prop}
    (hAS : ∀ r, A r → g.S r) {B : List (StatementExport.Pat V Term Nat)} {B' : List (QPat V Term)}
    (hB : Forall2 (PatRel g.content id g.S) B B') :
    (∀ (μ : V → Node) (ν : V → QT Term),
      (∀ v, (∃ P ∈ B, P.Has v) → Quotes g.content id g.S (μ v) (ν v)) →
        (Sol g.content A μ B ↔ QSol g.content id g.S A ν B')) ∧
    (∀ ν : V → QT Term, QSol g.content id g.S A ν B' →
      ∃ μ : V → Node, ∀ v, (∃ P ∈ B, P.Has v) → Quotes g.content id g.S (μ v) (ν v)) ∧
    (∀ (μ μ' : V → Node) (ν : V → QT Term),
      (∀ v, (∃ P ∈ B, P.Has v) → Quotes g.content id g.S (μ v) (ν v)) →
      (∀ v, (∃ P ∈ B, P.Has v) → Quotes g.content id g.S (μ' v) (ν v)) →
        ∀ v, (∃ P ∈ B, P.Has v) → μ v = μ' v) :=
  bgp_view (f := id) (fun _ _ e => e) hd hAS hB

end StatementGraph

end LeanRDF.Statements
