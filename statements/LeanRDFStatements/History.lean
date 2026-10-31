import LeanRDFStatements.Kernel

/-!
# History closure

The counterparts, on records, of the paper's `history_closed`, `history_cycle` and
`history_kernel`, with transactions in place of insert batches. Under tiramemsu's write rule that
a record references only records added in the same or an earlier transaction, the full history
is closed and every reference cycle lies inside one transaction (a correction replay); when
every reference points to a strictly earlier transaction, the history is acyclic and is its own
kernel.
-/

namespace LeanRDF.Statements

open StatementExport

namespace StatementGraph

/-- The transaction that added an eid's record. -/
def txOf (g : StatementGraph) (e : Nat) : Nat := ((g.find? e).map (·.txAdded)).getD 0

/-- Every reference points to a record added in the same or an earlier transaction. -/
def TxOrdered (g : StatementGraph) : Prop :=
  ∀ r ∈ g.records, ∀ x ∈ r.refs, ∃ r' ∈ g.records, r'.eid = x ∧ r'.txAdded ≤ r.txAdded

/-- Every reference points to a record added in a strictly earlier transaction. -/
def TxStrict (g : StatementGraph) : Prop :=
  ∀ r ∈ g.records, ∀ x ∈ r.refs, ∃ r' ∈ g.records, r'.eid = x ∧ r'.txAdded < r.txAdded

private theorem txOf_of_mem {g : StatementGraph} {r : Record} (h : r ∈ g.records) :
    g.txOf r.eid = r.txAdded := by
  simp [txOf, find?_of_mem h]

-- @tg: implements:: [[openspec:statement-graphs#History closure]]
/-- The full history is closed (`history_closed`). -/
theorem history_closed {g : StatementGraph} (h : g.TxOrdered) : Closed (crefs g.content) g.S := by
  intro e he x hx
  obtain ⟨r, hr, rfl⟩ := mem_eids.1 he
  rw [crefs_of_mem hr] at hx
  obtain ⟨r', hr', rfl, -⟩ := h r hr x hx
  exact mem_eids.2 ⟨r', hr', rfl⟩

/-- A reference never points forward in transaction time. -/
private theorem txOf_ref {g : StatementGraph} (h : g.TxOrdered) {y x : Nat}
    (hyx : Ref (crefs g.content) g.S y x) : g.txOf y ≤ g.txOf x := by
  obtain ⟨hx, -, hy⟩ := hyx
  obtain ⟨r, hr, rfl⟩ := mem_eids.1 hx
  rw [crefs_of_mem hr] at hy
  obtain ⟨r', hr', rfl, hle⟩ := h r hr y hy
  rw [txOf_of_mem hr, txOf_of_mem hr']; exact hle

private theorem txOf_trans {g : StatementGraph} (h : g.TxOrdered) {y x : Nat}
    (hyx : Relation.TransGen (Ref (crefs g.content) g.S) y x) : g.txOf y ≤ g.txOf x := by
  induction hyx with
  | single h' => exact txOf_ref h h'
  | tail _ h' ih => exact Nat.le_trans ih (txOf_ref h h')

/-- Every reference cycle lies inside one transaction (`history_cycle`): two eids on a common
cycle were added by the same transaction. -/
theorem history_cycle {g : StatementGraph} (h : g.TxOrdered) {a b : Nat}
    (hab : Relation.TransGen (Ref (crefs g.content) g.S) a b)
    (hba : Relation.TransGen (Ref (crefs g.content) g.S) b a) : g.txOf a = g.txOf b :=
  Nat.le_antisymm (txOf_trans h hab) (txOf_trans h hba)

private theorem txOf_trans_lt {g : StatementGraph} (h : g.TxStrict) {y x : Nat}
    (hyx : Relation.TransGen (Ref (crefs g.content) g.S) y x) : g.txOf y < g.txOf x := by
  have step : ∀ {y x}, Ref (crefs g.content) g.S y x → g.txOf y < g.txOf x := by
    intro y x hyx
    obtain ⟨hx, -, hy⟩ := hyx
    obtain ⟨r, hr, rfl⟩ := mem_eids.1 hx
    rw [crefs_of_mem hr] at hy
    obtain ⟨r', hr', rfl, hlt⟩ := h r hr y hy
    rw [txOf_of_mem hr, txOf_of_mem hr']; exact hlt
  induction hyx with
  | single h' => exact step h'
  | tail _ h' ih => exact Nat.lt_trans ih (step h')

/-- With strictly earlier references, the history is acyclic and is its own kernel
(`history_kernel`). -/
theorem history_kernel {g : StatementGraph} (h : g.TxStrict) :
    Acyclic (crefs g.content) g.S ∧ ∀ e, e ∈ g.kernel ↔ e ∈ g.eids := by
  have hO : g.TxOrdered := fun r hr x hx =>
    let ⟨r', hr', he, hlt⟩ := h r hr x hx; ⟨r', hr', he, Nat.le_of_lt hlt⟩
  have hA : Acyclic (crefs g.content) g.S := fun a ha => Nat.lt_irrefl _ (txOf_trans_lt h ha)
  refine ⟨hA, fun e => ?_⟩
  rw [mem_kernel_iff]
  exact (K_eq_self_iff g.covered).2 ⟨history_closed hO, hA⟩ e

end StatementGraph

end LeanRDF.Statements
