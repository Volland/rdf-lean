import LeanRDFSparql.Correct
import LeanRDFSparql.Query

/-! Challenge: the main theorems of `leanrdf-sparql`, stated exactly as BASE f9c67cf states them
(text copied from `git show f9c67cf:<file>`), in a fresh `Challenge` namespace. -/

-- f9c67cf:sparql/LeanRDFSparql/Correct.lean
namespace LeanRDF.Sparql

open List

theorem Challenge.evalN_perm : ∀ (n : Nat) (D : Dataset) (G : Graph) (P : Pattern),
    Eval.evalN n D G P ~ Spec.evalN n D G P :=
  sorry

end LeanRDF.Sparql

-- f9c67cf:sparql/LeanRDFSparql/Query.lean
namespace LeanRDF.Sparql

open List Xsd

theorem Challenge.runQuery_answer (D : Dataset) (q : Query) : Spec.Answer D q (Eval.runQuery D q) :=
  sorry

end LeanRDF.Sparql
