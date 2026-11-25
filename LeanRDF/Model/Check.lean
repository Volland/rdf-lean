import LeanRDF.Model.Index
import LeanRDF.Parse.NTriples.Serializer

/-!
# The model checker

`checkCountermodel r g q P` accepts a presentation as a countermodel to `g ⊨ q` under the
regime `r` when:
- `P` is well-formed;
- the regime's sort-level conditions hold;
- the blank-node assignment of `P` makes every triple of `g` true;
- no assignment of resource sorts to the blank nodes of `q` makes every triple of `q` true,
  decided by enumerating every such assignment within a step budget.

Since truth depends only on sorts (`holds_iff`), the last check covers every assignment
`A : BlankNode → CDom` into IR (`not_satisfies_q`). Acceptance gives `¬ g.SimpleEntails q`,
`¬ g.RDFEntails q` or `¬ g.RDFSEntails q`.

The checker decides the conditions through hash indexes of the presentation
(`LeanRDF.Model.Index`); `countermodelFailure_eq_spec` proves it equal to
`countermodelFailureSpec`, which decides them over the lists as they are defined.
-/

namespace LeanRDF.Model

open Vocab

/-- The regimes a countermodel refutes in. -/
inductive CRegime where
  | simple | rdf | rdfs
  deriving DecidableEq, Repr, Inhabited

def CRegime.name : CRegime → String
  | .simple => "simple" | .rdf => "rdf" | .rdfs => "rdfs"

def CRegime.ofName? (s : String) : Option CRegime :=
  [CRegime.simple, .rdf, .rdfs].find? (·.name == s)

/-- The theorem an accepted countermodel stands for. -/
def CRegime.theoremName : CRegime → String
  | .simple => "checkCountermodel_sound_simple"
  | .rdf => "checkCountermodel_sound_rdf"
  | .rdfs => "checkCountermodel_sound_rdfs"

namespace Presentation

variable (P : Presentation)

/-- The sort of a blank node of the data. -/
def assignSort (b : BlankNode) : Nat := (P.assign.lookup b).getD 0

/-- The resource sorts. -/
def irSorts : List Nat := (List.range P.n).filter (P.irB · = true)

/-- Every assignment of the sorts `ks` to the blank nodes `bs`. -/
def assignments : List BlankNode → List Nat → List (List (BlankNode × Nat))
  | [], _ => [[]]
  | b :: bs, ks => (assignments bs ks).flatMap fun f => ks.map fun k => (b, k) :: f

/-- An assignment list as a function; unlisted blank nodes get sort 0. -/
def asFun (f : List (BlankNode × Nat)) (b : BlankNode) : Nat := (f.lookup b).getD 0

/-- The blank nodes of a graph, each once. -/
def graphBNodes (g : Graph) : List BlankNode := dedup (g.toList.flatMap tripleBNodes)

/-- The data holds under the assignment of the presentation. -/
def DataHolds (g : Graph) : Prop := ∀ t ∈ g.toList, P.sHolds P.assignSort t = true

/-- No assignment of resource sorts satisfies the query. -/
def QueryFails (q : Graph) : Prop :=
  ∀ f ∈ assignments (graphBNodes q) P.irSorts, ∃ t ∈ q.toList, P.sHolds (asFun f) t = false

instance (g : Graph) : Decidable (P.DataHolds g) := by unfold DataHolds; infer_instance
instance (q : Graph) : Decidable (P.QueryFails q) := by unfold QueryFails; infer_instance

/-- The number of query assignments to try. -/
def searchSize (q : Graph) : Nat := P.irSorts.length ^ (graphBNodes q).length

/-- `assignSort` through the index. -/
def Idx.assignSort (x : Idx) (b : BlankNode) : Nat := (x.assign[b]?).getD 0

theorem assignSortX_eq : (P.index).assignSort = P.assignSort := by
  funext b
  simp only [Idx.assignSort, assignSort, index, Index.getElem?_assocMap]

end Presentation

open Presentation

/-- A term nests triple terms at most `n` deep. -/
def termDepthLE : Nat → Term → Bool
  | n, .triple s p o => n != 0 && termDepthLE (n - 1) s && termDepthLE (n - 1) p &&
      termDepthLE (n - 1) o
  | _, _ => true

/-- A term of the data as a failure message shows it: in N-Triples, cut after 1000 characters,
and elided when it nests triple terms more than 64 deep, so a rejection does not echo unbounded
input. -/
def showTerm (t : Term) : String :=
  if termDepthLE 64 t then
    let s := t.toNTriples
    if s.length ≤ 1000 then s else (s.take 1000).toString ++ "…"
  else "<<( … )>>"

/-- Why a presentation is not a countermodel, if it is not: the conditions decided over the
lists of the presentation, as they are defined. -/
def countermodelFailureSpec (r : CRegime) (g q : Graph) (P : Presentation) (budget : Nat) :
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
        | some t => some s!"a data triple does not hold: {showTerm t.s} {showTerm t.p} {showTerm t.o}"
        | none =>
          if P.searchSize q > budget then
            some s!"the query search needs {P.searchSize q} assignments, over the budget of {budget}"
          else
            match (assignments (graphBNodes q) P.irSorts).find?
                (fun f => q.toList.all (P.sHolds (asFun f))) with
            | some f => some s!"the query holds under the assignment {f.map fun (b, k) => s!"_:{b.label}↦{k}"}"
            | none => none

/-- Why a presentation is not a countermodel, if it is not. The conditions are decided through
hash indexes built once (`Presentation.index`); the result, messages included, is the one of
`countermodelFailureSpec` (`countermodelFailure_eq_spec`). -/
def countermodelFailure (r : CRegime) (g q : Graph) (P : Presentation) (budget : Nat) :
    Option String :=
  let x := P.index
  match failed? (P.wfChecksX x) with
  | some e => some s!"not well-formed: {e}"
  | none =>
    match (if r = .simple then none else failed? (P.rdfChecksX x)) with
    | some e => some s!"condition failed: {e}"
    | none =>
      match (if r = .rdfs then failed? (P.rdfsChecksX x) else none) with
      | some e => some s!"condition failed: {e}"
      | none =>
        match g.toList.find? (fun t => !P.sHoldsX x x.assignSort t) with
        | some t => some s!"a data triple does not hold: {showTerm t.s} {showTerm t.p} {showTerm t.o}"
        | none =>
          if P.searchSize q > budget then
            some s!"the query search needs {P.searchSize q} assignments, over the budget of {budget}"
          else
            match (assignments (graphBNodes q) P.irSorts).find?
                (fun f => q.toList.all (P.sHoldsX x (asFun f))) with
            | some f => some s!"the query holds under the assignment {f.map fun (b, k) => s!"_:{b.label}↦{k}"}"
            | none => none

/-- The indexed checker gives the result of the list definitions. -/
theorem countermodelFailure_eq_spec (r : CRegime) (g q : Graph) (P : Presentation)
    (budget : Nat) : countermodelFailure r g q P budget = countermodelFailureSpec r g q P budget := by
  simp only [countermodelFailure, countermodelFailureSpec, wfChecksX_eq, rdfChecksX_eq,
    rdfsChecksX_eq, sHoldsX_eq, assignSortX_eq]

-- @tg: implements:: [[openspec:countermodels#Model checker]]
/-- Check a countermodel to `g ⊨ q` under a regime, with a step budget for the query search. -/
def checkCountermodel (r : CRegime) (g q : Graph) (P : Presentation) (budget : Nat := 1000000) :
    Except String Unit :=
  match countermodelFailure r g q P budget with
  | some e => .error e
  | none => .ok ()

/-! ## Soundness -/

namespace Presentation

variable {P : Presentation}

theorem mem_assignments {bs : List BlankNode} {ks : List Nat} {σ : BlankNode → Nat}
    (h : ∀ b ∈ bs, σ b ∈ ks) : bs.map (fun b => (b, σ b)) ∈ assignments bs ks := by
  induction bs with
  | nil => exact .head _
  | cons b bs ih =>
    simp only [List.map_cons, assignments, List.mem_flatMap, List.mem_map]
    exact ⟨_, ih (fun c hc => h c (.tail _ hc)), σ b, h b (.head _), rfl⟩

theorem asFun_map {bs : List BlankNode} {σ : BlankNode → Nat} {b : BlankNode} (h : b ∈ bs) :
    asFun (bs.map fun c => (c, σ c)) b = σ b := by
  induction bs with
  | nil => cases h
  | cons c cs ih =>
    unfold asFun
    simp only [List.map_cons, List.lookup]
    by_cases e : b = c
    · subst e; simp
    · have hb : b ∈ cs := (List.mem_cons.1 h).resolve_left e
      have : (b == c) = false := by simpa using e
      rw [this]; exact ih hb

theorem sortOf_assign (hw : P.WellFormed) (b : BlankNode) :
    P.sortOf (.base (P.assignSort b)) = P.assignSort b ∧ P.irB (P.assignSort b) = true := by
  unfold assignSort
  cases h : P.assign.lookup b with
  | some k =>
    obtain ⟨h1, h2, h3⟩ := hw.assign _ (lookup_mem h)
    exact ⟨sortOf_base_of h1 h2, h3⟩
  | none => exact ⟨sortOf_base_of hw.zero.1 hw.zero.2.1, hw.zero.2.2⟩

/-- The presented interpretation satisfies the data. -/
theorem satisfies_g (hw : P.WellFormed) {g : Graph} (h : P.DataHolds g) :
    (P.interp hw).Satisfies g := by
  refine ⟨fun b => .base (P.assignSort b), fun b => ?_, fun t ht => ?_⟩
  · show P.irB (P.sortOf (.base (P.assignSort b))) = true
    rw [(sortOf_assign hw b).1]; exact (sortOf_assign hw b).2
  rw [holds_iff hw]
  have e : (fun b => P.sortOf (CDom.base (P.assignSort b))) = P.assignSort :=
    funext fun b => (sortOf_assign hw b).1
  rw [e]
  exact h t (Graph.mem_toList.2 ht)

-- @tg: implements:: [[openspec:countermodels#Countermodel soundness]] {note: "query-search completeness"}
/-- Query-search completeness: if no enumerated sort assignment satisfies `q`, no blank-node
mapping into IR does. -/
theorem not_satisfies_q (hw : P.WellFormed) {q : Graph} (h : P.QueryFails q) :
    ¬ (P.interp hw).Satisfies q := by
  rintro ⟨A, hA, hq⟩
  let σ := fun b => P.sortOf (A b)
  have hirs : ∀ b ∈ graphBNodes q, σ b ∈ P.irSorts := fun b _ => by
    simp only [irSorts, List.mem_filter, List.mem_range]
    exact ⟨sortOf_lt hw (A b), hA b⟩
  obtain ⟨t, ht, hf⟩ := h _ (mem_assignments hirs)
  have hagree : ∀ b ∈ tripleBNodes t, σ b = asFun ((graphBNodes q).map fun c => (c, σ c)) b :=
    fun b hb => (asFun_map (mem_dedup.2 (List.mem_flatMap.2 ⟨t, ht, hb⟩))).symm
  have := (holds_iff hw A t).1 (hq t (Graph.mem_toList.1 ht))
  rw [sHolds_congr P hagree] at this
  rw [this] at hf
  cases hf

/-- What an accepted countermodel gives. -/
structure Accepted (r : CRegime) (g q : Graph) (P : Presentation) : Prop where
  wf : P.WellFormed
  rdf : r ≠ .simple → P.RDFSorts
  rdfs : r = .rdfs → P.RDFSSorts
  data : P.DataHolds g
  query : P.QueryFails q

theorem accepted_of_none {r : CRegime} {g q : Graph} {P : Presentation} {budget : Nat}
    (hf : countermodelFailure r g q P budget = none) : Accepted r g q P := by
  rw [countermodelFailure_eq_spec] at hf
  unfold countermodelFailureSpec at hf
  split at hf
  · cases hf
  rename_i hwf
  have wf := wellFormed_of hwf
  split at hf
  · cases hf
  rename_i hrdf
  split at hf
  · cases hf
  rename_i hrdfs
  split at hf
  · cases hf
  rename_i hdata
  split at hf
  · cases hf
  split at hf
  · cases hf
  rename_i hq
  refine ⟨wf, fun hr => ?_, fun hr => ?_, ?_, ?_⟩
  · simp only [hr, ite_false] at hrdf; exact rdfSorts_of hrdf
  · simp only [hr, ite_true] at hrdfs; exact rdfsSorts_of hrdfs
  · intro t ht
    rw [List.find?_eq_none] at hdata
    simpa using hdata t ht
  · intro f hf'
    rw [List.find?_eq_none] at hq
    have h2 : q.toList.all (P.sHolds (asFun f)) = false := by simpa using hq f hf'
    rw [List.all_eq_false] at h2
    obtain ⟨t, ht, e⟩ := h2
    exact ⟨t, ht, by simpa using e⟩

theorem accepted_of {r : CRegime} {g q : Graph} {P : Presentation} {budget : Nat}
    (h : checkCountermodel r g q P budget = .ok ()) : Accepted r g q P := by
  unfold checkCountermodel at h
  split at h
  · cases h
  · rename_i hf; exact accepted_of_none hf

end Presentation

open Presentation

/-- An accepted countermodel's interpretation satisfies the data and not the query. -/
theorem checkCountermodel_interp {r : CRegime} {g q : Graph} {P : Presentation} {budget : Nat}
    (h : checkCountermodel r g q P budget = .ok ()) :
    ∃ hw : P.WellFormed, (P.interp hw).Satisfies g ∧ ¬ (P.interp hw).Satisfies q := by
  have a := accepted_of h
  exact ⟨a.wf, satisfies_g a.wf a.data, not_satisfies_q a.wf a.query⟩

/-- An accepted countermodel under `simple` proves non-entailment. -/
theorem checkCountermodel_sound_simple {g q : Graph} {P : Presentation} {budget : Nat}
    (h : checkCountermodel .simple g q P budget = .ok ()) : ¬ g.SimpleEntails q := by
  obtain ⟨hw, hg, hq⟩ := checkCountermodel_interp h
  exact fun e => hq (e _ hg)

/-- An accepted countermodel under `rdf` proves non-entailment. -/
theorem checkCountermodel_sound_rdf {g q : Graph} {P : Presentation} {budget : Nat}
    (h : checkCountermodel .rdf g q P budget = .ok ()) : ¬ g.RDFEntails q := by
  have a := accepted_of h
  exact fun e => not_satisfies_q a.wf a.query
    (e (P.dinterp a.wf) (isRDF_of a.wf (a.rdf (by decide))) (satisfies_g a.wf a.data))

/-- An accepted countermodel under `rdfs` proves non-entailment. -/
theorem checkCountermodel_sound_rdfs {g q : Graph} {P : Presentation} {budget : Nat}
    (h : checkCountermodel .rdfs g q P budget = .ok ()) : ¬ g.RDFSEntails q := by
  have a := accepted_of h
  exact fun e => not_satisfies_q a.wf a.query
    (e (P.dinterp a.wf) (isRDFS_of a.wf (a.rdf (by decide)) (a.rdfs rfl)) (satisfies_g a.wf a.data))

/-- An accepted countermodel under `rdfs` also gives an RDFS model of the data: the data is
consistent, so no clash certificate for it can be accepted. -/
theorem checkCountermodel_consistent {g q : Graph} {P : Presentation} {budget : Nat}
    (h : checkCountermodel .rdfs g q P budget = .ok ()) :
    ∃ I : DInterp, I.IsRDFS ∧ I.Satisfies g := by
  have a := accepted_of h
  exact ⟨P.dinterp a.wf, isRDFS_of a.wf (a.rdf (by decide)) (a.rdfs rfl), satisfies_g a.wf a.data⟩

/-- `checkCountermodel` as a Boolean, for `native_decide` in tests. -/
def checkCountermodelB (r : CRegime) (g q : Graph) (P : Presentation) (budget : Nat := 1000000) : Bool :=
  (checkCountermodel r g q P budget).toBool

theorem checkCountermodelB_ok {r : CRegime} {g q : Graph} {P : Presentation} {budget : Nat}
    (h : checkCountermodelB r g q P budget = true) : checkCountermodel r g q P budget = .ok () := by
  unfold checkCountermodelB at h
  cases e : checkCountermodel r g q P budget with
  | ok u => rfl
  | error m => rw [e] at h; simp [Except.toBool] at h

end LeanRDF.Model
