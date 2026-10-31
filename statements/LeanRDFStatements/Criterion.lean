import LeanRDFStatements.Kernel

/-!
# The Statement Graph criterion on LeanRDF types

The paper's `thm:criterion`, instantiated: the records of a statement graph, with RDF terms as
leaves, eids as statement identifiers and the identity as leaf encoding, have an
identity-preserving export to a Gelling–Fletcher–Schmidt Statement Graph exactly when they are
closed and acyclic, as decided by `isClosed` and `isAcyclic`. The export is unique and
determines the record contents.
-/

namespace LeanRDF.Statements

open StatementExport

namespace StatementGraph

-- @tg: implements:: [[openspec:statement-graphs#Statement Graph criterion]]
/-- `thm:criterion` on a statement graph: a direct Statement Graph export exists iff the records
are closed and acyclic. -/
theorem criterion (g : StatementGraph) :
    (∃ G : SGraph Nat Term, G.IsSG ∧ DirectExport g.content id g.S G) ↔
      g.isClosed = true ∧ g.isAcyclic = true := by
  rw [isClosed_iff, isAcyclic_iff]
  exact direct_export_iff g.content id g.S

/-- The direct export is unique. -/
theorem criterion_unique (g : StatementGraph) {G G' : SGraph Nat Term}
    (h : DirectExport g.content id g.S G) (h' : DirectExport g.content id g.S G') :
    (∀ e, G.internal e ↔ G'.internal e) ∧ ∀ r, g.S r → ∀ ρ, G.edge r ρ = G'.edge r ρ :=
  direct_export_unique h h'

/-- The direct export determines the content of every record. -/
theorem criterion_recovers (g : StatementGraph) {c' : Nat → Content Term Nat} {G : SGraph Nat Term}
    (h : DirectExport g.content id g.S G) (h' : DirectExport c' id g.S G) {r : Nat} (hr : g.S r) :
    g.content r = c' r :=
  direct_export_recovers (fun _ _ e => e) h h' hr

end StatementGraph

end LeanRDF.Statements
