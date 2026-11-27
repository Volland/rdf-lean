import LeanRDFStatements.Decode
import LeanRDFStatements.Kernel
import LeanRDFStatements.Criterion

/-! Solution: the main theorems of `leanrdf-statements`, stated exactly as BASE f9c67cf states
them (text copied from `git show f9c67cf:<file>`), in a fresh `Challenge` namespace,
proven by the perf/10x theorem of the same name. -/

-- f9c67cf:statements/LeanRDFStatements/Decode.lean
namespace LeanRDF.Statements

open Vocab

theorem Challenge.toRDF_decode {v : View} {g : Graph} {sg : StatementGraph} (h : decode v g = .ok sg) :
    sg.WellFormed ∧ ∀ t, t ∈ sg.toRDF v ↔ t ∈ g := by
  exact LeanRDF.Statements.toRDF_decode h

section
variable {v : View} {sg : StatementGraph}

theorem Challenge.decode_toRDF (hw : sg.WellFormed) : decode v (sg.toRDF v) = .ok sg := by
  exact LeanRDF.Statements.decode_toRDF hw

end

end LeanRDF.Statements

-- f9c67cf:statements/LeanRDFStatements/Criterion.lean
namespace LeanRDF.Statements

open StatementExport

namespace StatementGraph

theorem Challenge.criterion (g : StatementGraph) :
    (∃ G : SGraph Nat Term, G.IsSG ∧ DirectExport g.content id g.S G) ↔
      g.isClosed = true ∧ g.isAcyclic = true := by
  exact LeanRDF.Statements.StatementGraph.criterion g

end StatementGraph

end LeanRDF.Statements

-- f9c67cf:statements/LeanRDFStatements/Kernel.lean
namespace LeanRDF.Statements

open StatementExport

namespace StatementGraph

theorem Challenge.kernel_greatest (g : StatementGraph) {U : Nat → Prop} (hUS : ∀ r, U r → g.S r)
    (hU : Closed (crefs g.content) U) (hA : Acyclic (crefs g.content) U) :
    ∀ r, U r → r ∈ g.kernel := by
  exact LeanRDF.Statements.StatementGraph.kernel_greatest g hUS hU hA

end StatementGraph

end LeanRDF.Statements
