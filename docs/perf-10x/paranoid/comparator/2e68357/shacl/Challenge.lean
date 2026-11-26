import LeanRDFShacl.Correct

/-! Challenge: the main theorems of `leanrdf-shacl`, stated exactly as BASE f9c67cf states them
(text copied from `git show f9c67cf:<file>`), in a fresh `Challenge` namespace. -/

-- f9c67cf:shacl/LeanRDFShacl/Correct.lean
namespace LeanRDF.Shacl

open Vocab

variable (G : Graph)

theorem Challenge.validate_conforms (S : List Shape) : (validate G S).conforms = true ↔ DataConforms G S := by
  sorry

theorem Challenge.validate_sound (S : List Shape) {r : Result} (h : r ∈ (validate G S).results) :
    Violation G r := by
  sorry

end LeanRDF.Shacl
