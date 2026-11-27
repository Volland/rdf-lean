import LeanRDFSparql

/-! Audit only (never committed): the BASE f9c67cf definitions of `Spec.groupOp`, `Eval.bgp`
and `Eval.evalN`, copied verbatim, re-elaborated against perf/10x, and proven equal to the
perf/10x definitions. -/

namespace LeanRDF.Sparql

namespace Spec
namespace AuditOld
-- f9c67cf:sparql/LeanRDFSparql/Ops.lean
def groupOp (ex : Pattern → Bool) (keys : List (Expr × Option Var)) (aggs : List (Var × Aggregate))
    (Ω : List Mapping) : List Mapping :=
  let keyOf (μ : Mapping) : List (Option Term) := keys.map fun (e, _) => (e.eval ex μ).toOption
  let groups : List (List (Option Term)) :=
    if keys.isEmpty then [[]] else dedup (Ω.map keyOf)
  groups.map fun k =>
    let rows := Ω.filter fun μ => keyOf μ == k
    let base := (keys.zip k).foldl (fun μ ((_, v?), t?) =>
      match v?, t? with
      | some v, some t => μ.insert v t
      | _, _ => μ) Mapping.empty
    aggs.foldl (fun μ (v, agg) =>
      match aggregateValue ex rows agg with
      | .ok t => μ.insert v t
      | .error _ => μ) base
end AuditOld

theorem groupOp_eq_old : @Spec.groupOp = @AuditOld.groupOp := rfl
end Spec

namespace Eval
namespace AuditOld
-- f9c67cf:sparql/LeanRDFSparql/Eval.lean
def bgp (G : Graph) (tps : List TriplePattern) : List Mapping :=
  (matchAll G tps [Mapping.empty]).map (·.restrict (visibleVars tps))

def evalN : Nat → Dataset → Graph → Pattern → List Mapping
  | 0, _, _, _ => []
  | n + 1, D, G, P =>
    let ex : Pattern → Bool := fun q => !(evalN n D G q).isEmpty
    match P with
    | .bgp tps => bgp G tps
    | .join a b => Spec.join (evalN n D G a) (evalN n D G b)
    | .leftJoin a b e => Spec.leftJoin (evalN n D G a) (evalN n D G b) fun μ => (e.eval ex μ).holds
    | .filter e a => (evalN n D G a).filter fun μ => (e.eval ex μ).holds
    | .union a b => evalN n D G a ++ evalN n D G b
    | .graph (.term g) a => if D.graphNames.contains g then evalN n D (D.namedGraph g) a else []
    | .graph (.var v) a =>
      D.graphNames.flatMap fun g => (evalN n D (D.namedGraph g) a).filterMap (Spec.bindGraph v g)
    | .extend a v e => Spec.extend (evalN n D G a) v fun μ => e.eval ex μ
    | .minus a b => Spec.minus (evalN n D G a) (evalN n D G b)
    | .table rows => rows
    | .path s p o => Spec.pathOp G s p o
    | .group keys aggs a => Spec.groupOp ex keys aggs (evalN n D G a)
    | .subquery pr d ob off lim a => Spec.subqueryOp ex pr d ob off lim (evalN n D G a)
end AuditOld
end Eval

theorem evalNI_eq_old : ∀ (n : Nat) (D : Dataset) (G : Graph) (P : Pattern),
    Eval.evalNI n D G (Eval.TIdx.build G.toList) P = Eval.AuditOld.evalN n D G P
  | 0, _, _, _ => by simp [Eval.evalNI, Eval.AuditOld.evalN]
  | n + 1, D, G, P => by
    have ih : ∀ G q, Eval.evalNI n D G (Eval.TIdx.build G.toList) q = Eval.AuditOld.evalN n D G q :=
      fun G q => evalNI_eq_old n D G q
    have hex : (fun q => !(Eval.evalNI n D G (Eval.TIdx.build G.toList) q).isEmpty) =
        (fun q => !(Eval.AuditOld.evalN n D G q).isEmpty) :=
      funext fun q => by rw [ih G q]
    cases P with
    | bgp tps =>
      simp only [Eval.evalNI, Eval.AuditOld.evalN, Eval.AuditOld.bgp]
      rw [← bgp_eq]; rfl
    | join a b => simp only [Eval.evalNI, Eval.AuditOld.evalN, evalJoin_eq, ih]
    | leftJoin a b e => simp only [Eval.evalNI, Eval.AuditOld.evalN, evalLeftJoin_eq, ih]
    | filter e a => simp only [Eval.evalNI, Eval.AuditOld.evalN, ih]
    | union a b => simp only [Eval.evalNI, Eval.AuditOld.evalN, ih]
    | graph g a =>
      cases g with
      | term g => simp only [Eval.evalNI, Eval.AuditOld.evalN, ih]
      | var v => simp only [Eval.evalNI, Eval.AuditOld.evalN, ih]
    | extend a v e => simp only [Eval.evalNI, Eval.AuditOld.evalN, ih]
    | minus a b => simp only [Eval.evalNI, Eval.AuditOld.evalN, evalMinus_eq, ih]
    | table rows => simp only [Eval.evalNI, Eval.AuditOld.evalN]
    | path s p o => simp only [Eval.evalNI, Eval.AuditOld.evalN, pathOp_eq]
    | group keys aggs a => simp only [Eval.evalNI, Eval.AuditOld.evalN, evalGroupOp_eq, ih]
    | subquery pr d ob off lim a =>
      simp only [Eval.evalNI, Eval.AuditOld.evalN, evalSubqueryOp_eq, ih]

/-- The perf/10x evaluator is, as a function, the BASE evaluator (re-elaborated over the
perf/10x `Graph`/`Dataset`). Hence `Spec.evalN`, whose GROUP and subquery cases call
`Eval.evalN`, also means what it meant at BASE. -/
theorem evalN_eq_old : @Eval.evalN = @Eval.AuditOld.evalN := by
  funext n D G P; exact evalNI_eq_old n D G P

-- f9c67cf:sparql/LeanRDFSparql/Query.lean: `def Eval.runQuery (D : Dataset) (q : Query) : List Mapping :=
--   q.finish ((Eval.eval D q.pattern).mergeSort (q.le D))`
theorem runQuery_eq_old (D : Dataset) (q : Query) :
    Eval.runQuery D q = q.finish ((Eval.eval D q.pattern).mergeSort (q.le D)) := by
  simp only [Eval.runQuery, Query.finishF_eq]

end LeanRDF.Sparql

#print axioms LeanRDF.Sparql.evalN_eq_old
#print axioms LeanRDF.Sparql.Spec.groupOp_eq_old
#print axioms LeanRDF.Sparql.runQuery_eq_old
