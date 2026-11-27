import LeanRDF

/-! Audit only (never committed): BASE f9c67cf definitions copied verbatim, re-elaborated
against perf/10x, and related to the perf/10x definitions. -/

namespace LeanRDF.Cert
namespace AuditOld
-- f9c67cf:LeanRDF/Cert/Check.lean
def checkQuery (rules : List Rule) (g q : Graph) (c : Certificate) : Except String Unit :=
  match checkCert rules g c with
  | .error e => .error e
  | .ok ts =>
    if q.toList.all (fun t => ts.contains (t.instantiate c.mu)) then .ok ()
    else .error "a query triple is not among the certified conclusions"
end AuditOld

theorem checkQuery_eq_old : @checkQuery = @AuditOld.checkQuery := by
  funext rules g q c
  unfold checkQuery AuditOld.checkQuery
  cases checkCert rules g c with
  | error e => rfl
  | ok ts => simp only [Certificate.muFast_eq, Std.HashSet.contains_ofList, Array.contains_toList]
end LeanRDF.Cert

namespace LeanRDF.Canon
-- f9c67cf:LeanRDF/Canon/Rdfc.lean: `def canonicalize (σ : Labeling) (d : Dataset) : Dataset := d.renameBNodes σ.rename`
theorem canonicalize_eq_old (σ : Labeling) (d : Dataset) : canonicalize σ d = d.renameBNodes σ.rename := by
  show d.renameBNodes σ.renameFast = _
  rw [Labeling.renameFast_eq]
end LeanRDF.Canon

namespace LeanRDF.Model
open Vocab
open Presentation
namespace AuditOld
-- f9c67cf:LeanRDF/Model/Check.lean
def countermodelFailure (r : CRegime) (g q : Graph) (P : Presentation) (budget : Nat) :
    Option String :=
  match failed? P.wfChecks with
  | some e => some s!"not well-formed: {e}"
  | none =>
    match (if r = .simple then none else failed? P.rdfChecks) with
    | some e => some s!"condition failed: {e}"
    | none =>
      match (if r = .rdfs then failed? P.rdfsChecks else none) with
      | some e => some s!"condition failed: {e}"
      | none =>
        match g.toList.find? (fun t => !P.sHolds P.assignSort t) with
        | some t => some s!"a data triple does not hold: {t.s.toNTriples} {t.p.toNTriples} {t.o.toNTriples}"
        | none =>
          if P.searchSize q > budget then
            some s!"the query search needs {P.searchSize q} assignments, over the budget of {budget}"
          else
            match (assignments (graphBNodes q) P.irSorts).find?
                (fun f => q.toList.all (P.sHolds (asFun f))) with
            | some f => some s!"the query holds under the assignment {f.map fun (b, k) => s!"_:{b.label}↦{k}"}"
            | none => none

def checkCountermodel (r : CRegime) (g q : Graph) (P : Presentation) (budget : Nat := 1000000) :
    Except String Unit :=
  match countermodelFailure r g q P budget with
  | some e => .error e
  | none => .ok ()
end AuditOld

/-- The perf/10x checker fails exactly when the BASE checker fails (only the failure messages
differ). -/
theorem countermodelFailure_isNone_eq_old (r : CRegime) (g q : Graph) (P : Presentation) (budget : Nat) :
    (countermodelFailure r g q P budget).isNone = (AuditOld.countermodelFailure r g q P budget).isNone := by
  rw [countermodelFailure_eq_spec]
  unfold countermodelFailureSpec AuditOld.countermodelFailure
  repeat' split
  all_goals simp_all

theorem checkCountermodel_ok_iff_old (r : CRegime) (g q : Graph) (P : Presentation) (budget : Nat) :
    checkCountermodel r g q P budget = .ok () ↔ AuditOld.checkCountermodel r g q P budget = .ok () := by
  have h := countermodelFailure_isNone_eq_old r g q P budget
  unfold checkCountermodel AuditOld.checkCountermodel
  cases h1 : countermodelFailure r g q P budget <;>
    cases h2 : AuditOld.countermodelFailure r g q P budget <;> simp_all
end LeanRDF.Model

#print axioms LeanRDF.Cert.checkQuery_eq_old
#print axioms LeanRDF.Canon.canonicalize_eq_old
#print axioms LeanRDF.Model.checkCountermodel_ok_iff_old
