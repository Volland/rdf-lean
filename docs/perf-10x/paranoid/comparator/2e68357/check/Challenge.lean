import LeanRDFCheck.Regime

/-! Challenge: the main theorem of `leanrdf-check`, stated exactly as BASE f9c67cf states it
(text copied from `git show f9c67cf:<file>`), in a fresh `Challenge` namespace. -/

-- f9c67cf:check/LeanRDFCheck/Regime.lean
namespace LeanRDF.Check

open Cert

theorem Challenge.checkRegime_sound {r : Regime} {g q : Graph} {c : Certificate}
    (h : checkRegime r g q c = .ok ()) : r.Entails g q := by
  sorry

end LeanRDF.Check
