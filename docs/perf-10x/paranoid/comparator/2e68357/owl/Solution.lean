import LeanRDFOwl.Soundness
import LeanRDFOwl.ELSoundness
import LeanRDFOwl.ClashSoundness

/-! Solution: the main theorems of `leanrdf-owl`, stated exactly as BASE f9c67cf states them
(text copied from `git show f9c67cf:<file>`), in a fresh `Challenge` namespace,
proven by the perf/10x theorem of the same name. -/

-- f9c67cf:owl/LeanRDFOwl/Soundness.lean
namespace LeanRDF.Owl

open Vocab RDFS Semantics SimpleInterp

variable {I : SimpleInterp}

theorem _root_.LeanRDF.Derives.Challenge.owl_sound {g : Graph} {t : Triple} (h : Derives owlRules g t) :
    g.OWLEntails (Graph.singleton t) := by
  exact LeanRDF.Derives.owl_sound h

end LeanRDF.Owl

-- f9c67cf:owl/LeanRDFOwl/ELSoundness.lean
namespace LeanRDF.Owl

open Vocab RDFS Semantics SimpleInterp

variable {I : SimpleInterp}

theorem _root_.LeanRDF.Derives.Challenge.el_sound {g : Graph} {t : Triple} (h : Derives owlELRules g t) :
    g.OWLEntails (Graph.singleton t) := by
  exact LeanRDF.Derives.el_sound h

end LeanRDF.Owl

-- f9c67cf:owl/LeanRDFOwl/ClashSoundness.lean
namespace LeanRDF.Owl

open Vocab RDFS Semantics SimpleInterp Cert

theorem _root_.LeanRDF.Cert.Challenge.checkClash_sound_owl {g : Graph} {c : Certificate}
    (h : checkClash owlRules owlClashRules g c = .ok ()) :
    ¬ ∃ I : DInterp, I.IsOWL ∧ I.Satisfies g := by
  exact LeanRDF.Cert.checkClash_sound_owl h

end LeanRDF.Owl
