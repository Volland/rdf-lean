import LeanRDF.Cert.Check
import LeanRDF.Canon.Rdfc
import LeanRDF.Model.Check

/-! Solution: the main theorems of `leanrdf`, stated exactly as BASE f9c67cf states them
(text copied from `git show f9c67cf:<file>`), in a fresh `Challenge` namespace,
proven by the perf/10x theorem of the same name. -/

-- f9c67cf:LeanRDF/Cert/Check.lean
namespace LeanRDF.Cert

theorem Challenge.checkQuery_sound {g q : Graph} {c : Certificate}
    (h : checkQuery RDFS.rdfsRules g q c = .ok ()) : g.RDFSEntails q :=
  LeanRDF.Cert.checkQuery_sound h

theorem Challenge.checkQuery_sound_rdf {g q : Graph} {c : Certificate}
    (h : checkQuery RDFS.rdfRules g q c = .ok ()) : g.RDFEntails q :=
  LeanRDF.Cert.checkQuery_sound_rdf h

theorem Challenge.checkQuery_sound_simple {g q : Graph} {c : Certificate} (hq : ∀ t ∈ q, t.WellFormed)
    (h : checkQuery RDFS.simpleRules g q c = .ok ()) : g.SimpleEntails q :=
  LeanRDF.Cert.checkQuery_sound_simple hq h

end LeanRDF.Cert

-- f9c67cf:LeanRDF/Canon/Rdfc.lean
namespace LeanRDF.Canon

theorem Challenge.canonical_iso (σ : Labeling) (d : Dataset) : Dataset.Iso d (canonicalize σ d) :=
  LeanRDF.Canon.canonical_iso σ d

end LeanRDF.Canon

-- f9c67cf:LeanRDF/Model/Check.lean
namespace LeanRDF.Model

open Vocab
open Presentation

theorem Challenge.checkCountermodel_sound_rdfs {g q : Graph} {P : Presentation} {budget : Nat}
    (h : checkCountermodel .rdfs g q P budget = .ok ()) : ¬ g.RDFSEntails q := by
  exact LeanRDF.Model.checkCountermodel_sound_rdfs h

end LeanRDF.Model
