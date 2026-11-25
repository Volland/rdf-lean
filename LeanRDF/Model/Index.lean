import LeanRDF.Model.Lift
import LeanRDF.Core.Index

/-!
# Indexed deciders for the model checker

The conditions of `Presentation.wfChecks`, `rdfChecks` and `rdfsChecks`, and the truth of a
triple `sHolds`, are defined over the lists of a presentation: `iris` and `overrides` are read by
`List.lookup`, and `P.E p s o` is membership in the list `ext`. Deciding them as written costs a
list scan per lookup, and the RDFS conditions nest two scans of `ext`.

This file builds hash indexes of the tables once (`Presentation.index`) and decides the same
conditions through them. Every indexed decider is proved equal to the definition it replaces:
- `wfChecksX_eq`, `rdfChecksX_eq` and `rdfsChecksX_eq`: the named checks, names, order and
  results, are the same lists;
- `sHoldsX_eq` and `assignSortX_eq`: truth of a triple and the blank-node sorts are the same
  functions.

The model checker (`LeanRDF.Model.Check`) runs the indexed deciders and rewrites with these
equalities, so its soundness proof is the one for the list definitions.
-/

namespace LeanRDF.Model

open Vocab Semantics

namespace Presentation

/-- Hash indexes of the tables of a presentation, built once per check. -/
structure Idx where
  /-- `iris` as a map: the first sort of each IRI. -/
  iris : Std.HashMap IRI Nat
  /-- `overrides` as a map: the first sort of each literal. -/
  overrides : Std.HashMap Literal Nat
  /-- `assign` as a map: the first sort of each blank node. -/
  assign : Std.HashMap BlankNode Nat
  /-- The entries of `ext`. -/
  ext : Std.HashSet (Nat × Nat × Nat)
  /-- The entries of `ext` by property sort. -/
  byP : Std.HashMap Nat (List (Nat × Nat × Nat))
  /-- The entries of `ext` by property and subject sort. -/
  byPS : Std.HashMap (Nat × Nat) (List (Nat × Nat × Nat))
  /-- The entries of `ext` by property and object sort. -/
  byPO : Std.HashMap (Nat × Nat) (List (Nat × Nat × Nat))
  /-- The sorts of the overrides. -/
  ovSorts : Std.HashSet Nat

/-- The indexes of a presentation. -/
def index (P : Presentation) : Idx where
  iris := Index.assocMap P.iris
  overrides := Index.assocMap P.overrides
  assign := Index.assocMap P.assign
  ext := Std.HashSet.ofList P.ext
  byP := Index.groupBy (·.1) P.ext
  byPS := Index.groupBy (fun e => (e.1, e.2.1)) P.ext
  byPO := Index.groupBy (fun e => (e.1, e.2.2)) P.ext
  ovSorts := Std.HashSet.ofList (P.overrides.map (·.2))

namespace Idx

/-- `(p, s, o)` is in the extension table. -/
def E (x : Idx) (p s o : Nat) : Bool := x.ext.contains (p, s, o)

/-- The entries of `ext` with property `p`. -/
def withP (x : Idx) (p : Nat) : List (Nat × Nat × Nat) := x.byP.getD p []

/-- The entries of `ext` with property `p` and subject `s`. -/
def withPS (x : Idx) (p s : Nat) : List (Nat × Nat × Nat) := x.byPS.getD (p, s) []

/-- The entries of `ext` with property `p` and object `o`. -/
def withPO (x : Idx) (p o : Nat) : List (Nat × Nat × Nat) := x.byPO.getD (p, o) []

end Idx

variable (P : Presentation) (x : Idx)

/-- `iriIdx` through the index. -/
def iriIdxX (i : IRI) : Nat :=
  match x.iris[i]? with
  | some k => k
  | none => if isMemberIri i then P.defaultCmp else P.defaultIri

/-- `sI` through the index. -/
def sIX (i : IRI) : Nat := P.sortOf (.base (P.iriIdxX x i))

/-- `sortOfLit` through the index. -/
def sortOfLitX (l : Literal) : Nat :=
  if litNormal l then (x.overrides[l]?).getD (P.defaultOf (kindOfLit l)) else 0

/-- `sden` through the index. -/
def sdenX (P : Presentation) (x : Idx) (σ : BlankNode → Nat) : Term → Option Nat
  | .iri i => some (P.sIX x i)
  | .bnode b => some (σ b)
  | .lit l => some (P.sortOfLitX x (normLit l))
  | .triple s p o =>
    match P.sdenX x σ s, P.sdenX x σ p, P.sdenX x σ o with
    | some a, some b, some c =>
      if P.irB a && P.ipB b && P.irB c then some P.tripleSort else none
    | _, _, _ => none

/-- `sHolds` through the index. -/
def sHoldsX (σ : BlankNode → Nat) (t : Triple) : Bool :=
  match P.sdenX x σ t.s, P.sdenX x σ t.p, P.sdenX x σ t.o with
  | some a, some b, some c => P.ipB b && x.E b a c
  | _, _, _ => false

/-- `HoldsI` through the index. -/
def holdsIX (a : IRI × IRI × IRI) : Bool :=
  let p := P.sIX x a.2.1
  P.ipB p && x.E p (P.sIX x a.1) (P.sIX x a.2.2)

/-- Every sort satisfies `f`. -/
def allSorts (f : Nat → Bool) : Bool := (List.range P.n).all f

/-- The well-formedness checks through the index: as `wfChecks`, with `LitSortsUsed` decided
through the set of override sorts. -/
def wfChecksX : List (String × Bool) :=
  [("sort 0 is a base resource sort", decide P.ZeroOK),
   ("IRI sorts are in range, base, and resources or properties", decide P.IrisOK),
   ("literal default sorts have their kinds and are resources", decide P.LitsOK),
   ("the triple sort has kind triple and is a resource", decide P.TripleOK),
   ("overrides are values in resource sorts of their kind", decide P.OverridesOK),
   ("every literal sort is a default or an override sort",
      P.allSorts fun k => P.kind k == .base || P.kind k == .triple ||
        P.litDefaults.contains k || x.ovSorts.contains k),
   ("IEXT relates resources by properties", decide P.ExtOK),
   ("blank nodes have base resource sorts", decide P.AssignOK)]

/-- The RDF checks through the index. -/
def rdfChecksX : List (String × Bool) :=
  let T := P.sIX x rdf.type
  [("RDF: IP is the class rdf:Property",
      let c := P.sIX x rdf.Property
      P.allSorts fun k => P.ipB k == x.E T k c),
   ("RDF: the class xsd:string is the string literals",
      let c := P.sIX x xsd.string
      P.allSorts fun k => x.E T k c == (P.kind k == .string)),
   ("RDF: the class rdf:langString is the language-tagged literals",
      let c := P.sIX x rdf.langString
      P.allSorts fun k => x.E T k c == (P.kind k == .lang)),
   ("RDF: the class rdf:dirLangString is the directional literals",
      let c := P.sIX x rdf.dirLangString
      P.allSorts fun k => x.E T k c == (P.kind k == .dirLang)),
   ("RDF: the axiomatic triples", rdfAxioms.all (P.holdsIX x)),
   ("RDF: rdf:_n rdf:type rdf:Property",
      let c := P.sIX x rdf.Property
      P.memberSorts.all fun k => P.ipB T && x.E T k c)]

/-- The RDFS checks through the index. A condition over pairs of `ext` entries joins through
the entries with a given property, subject or object instead of scanning `ext` twice. -/
def rdfsChecksX : List (String × Bool) :=
  let T := P.sIX x rdf.type
  let SP := P.sIX x rdfs.subPropertyOf
  let SC := P.sIX x rdfs.subClassOf
  let Res := P.sIX x rdfs.Resource
  let Cls := P.sIX x rdfs.Class
  let DT := P.sIX x rdfs.Datatype
  [("RDFS: rdfs:Resource is IR", P.allSorts fun k => x.E T k Res == P.irB k),
   ("RDFS: the recognized datatypes are rdfs:Datatype",
      x.E T (P.sIX x xsd.string) DT && x.E T (P.sIX x rdf.langString) DT &&
        x.E T (P.sIX x rdf.dirLangString) DT),
   ("RDFS: rdfs:domain", (x.withP (P.sIX x rdfs.domain)).all fun e =>
      (x.withP e.2.1).all fun f => x.E T f.2.1 e.2.2),
   ("RDFS: rdfs:range", (x.withP (P.sIX x rdfs.range)).all fun e =>
      (x.withP e.2.1).all fun f => x.E T f.2.2 e.2.2),
   ("RDFS: rdfs:subPropertyOf is reflexive on IP",
      P.allSorts fun k => !P.ipB k || x.E SP k k),
   ("RDFS: rdfs:subPropertyOf is transitive", (x.withP SP).all fun e =>
      (x.withPS SP e.2.2).all fun f => x.E SP e.2.1 f.2.2),
   ("RDFS: rdfs:subPropertyOf includes extensions", (x.withP SP).all fun e =>
      P.ipB e.2.1 && P.ipB e.2.2 && (x.withP e.2.1).all fun f => x.E e.2.2 f.2.1 f.2.2),
   ("RDFS: classes are subclasses of rdfs:Resource", (x.withPO T Cls).all fun e =>
      x.E SC e.2.1 Res),
   ("RDFS: rdfs:subClassOf is reflexive on IC", (x.withPO T Cls).all fun e =>
      x.E SC e.2.1 e.2.1),
   ("RDFS: rdfs:subClassOf is transitive", (x.withP SC).all fun e =>
      (x.withPS SC e.2.2).all fun f => x.E SC e.2.1 f.2.2),
   ("RDFS: rdfs:subClassOf includes class extensions", (x.withP SC).all fun e =>
      x.E T e.2.1 Cls && x.E T e.2.2 Cls && (x.withPO T e.2.1).all fun f => x.E T f.2.1 e.2.2),
   ("RDFS: container membership properties are subproperties of rdfs:member",
      let M := P.sIX x rdfs.member
      (x.withPO T (P.sIX x rdfs.ContainerMembershipProperty)).all fun e => x.E SP e.2.1 M),
   ("RDFS: datatypes are subclasses of rdfs:Literal",
      let L := P.sIX x rdfs.Literal
      (x.withPO T DT).all fun e => x.E SC e.2.1 L),
   ("RDFS: triple terms are rdfs:Proposition", x.E T P.tripleSort (P.sIX x rdfs.Proposition)),
   ("RDFS: the axiomatic triples", rdfsAxioms.all (P.holdsIX x)),
   ("RDFS: the axiomatic triples of rdf:_n",
      let D := P.sIX x rdfs.domain
      let R := P.sIX x rdfs.range
      let CMP := P.sIX x rdfs.ContainerMembershipProperty
      P.memberSorts.all fun k =>
        (P.ipB T && x.E T k CMP) && (P.ipB D && x.E D k Res) && (P.ipB R && x.E R k Res))]

/-! ## The indexed deciders are the definitions -/

variable {P}

theorem iriIdxX_eq (i : IRI) : P.iriIdxX P.index i = P.iriIdx i := by
  simp only [iriIdxX, index, Index.getElem?_assocMap]
  unfold iriIdx
  cases P.iris.lookup i <;> rfl

theorem sIX_eq (i : IRI) : P.sIX P.index i = P.sI i := by
  simp only [sIX, sI, IS, iriIdxX_eq]

theorem sortOfLitX_eq (l : Literal) : P.sortOfLitX P.index l = P.sortOfLit l := by
  simp only [sortOfLitX, sortOfLit, index, Index.getElem?_assocMap]

theorem sdenX_eq (σ : BlankNode → Nat) : ∀ t, P.sdenX P.index σ t = P.sden σ t
  | .iri i => by simp only [sdenX, sden, sIX_eq]; rfl
  | .bnode _ => rfl
  | .lit l => by simp only [sdenX, sden, sortOfLitX_eq]
  | .triple s p o => by
    simp only [sdenX, sden, sdenX_eq σ s, sdenX_eq σ p, sdenX_eq σ o]
    cases P.sden σ s <;> cases P.sden σ p <;> cases P.sden σ o <;> rfl

theorem E_index (p s o : Nat) : (P.index).E p s o = decide (P.E p s o) := by
  simp only [Idx.E, index, Std.HashSet.contains_ofList, E]
  exact Bool.eq_iff_iff.2 (by simp)

theorem sHoldsX_eq : P.sHoldsX P.index = P.sHolds := by
  funext σ t
  simp only [sHoldsX, sHolds, sdenX_eq]
  cases P.sden σ t.s <;> cases P.sden σ t.p <;> cases P.sden σ t.o <;>
    simp [E_index, E]

theorem holdsIX_eq (a : IRI × IRI × IRI) : P.holdsIX P.index a = decide (P.HoldsI a) := by
  simp only [holdsIX, sIX_eq, E_index, HoldsI]
  exact Bool.eq_iff_iff.2 (by simp)

theorem mem_withP {p : Nat} {e : Nat × Nat × Nat} :
    e ∈ (P.index).withP p ↔ e ∈ P.ext ∧ e.1 = p := Index.mem_groupBy

theorem mem_withPS {p s : Nat} {e : Nat × Nat × Nat} :
    e ∈ (P.index).withPS p s ↔ e ∈ P.ext ∧ e.1 = p ∧ e.2.1 = s := by
  simp only [Idx.withPS, index, Index.mem_groupBy, Prod.mk.injEq]

theorem mem_withPO {p o : Nat} {e : Nat × Nat × Nat} :
    e ∈ (P.index).withPO p o ↔ e ∈ P.ext ∧ e.1 = p ∧ e.2.2 = o := by
  simp only [Idx.withPO, index, Index.mem_groupBy, Prod.mk.injEq]

theorem allSorts_iff {f : Nat → Bool} : P.allSorts f = true ↔ ∀ k, k < P.n → f k = true := by
  simp [allSorts, List.all_eq_true, List.mem_range]

/-- A Boolean equals the decision of a proposition it is true exactly for. -/
private theorem eq_decide {b : Bool} {p : Prop} [Decidable p] (h : b = true ↔ p) :
    b = decide p := Bool.eq_iff_iff.2 (by simpa using h)

private theorem eq_decide_iff {b : Bool} {p : Prop} [Decidable p] :
    b = decide p ↔ (b = true ↔ p) := by cases b <;> simp

private theorem decide_eq_iff {b : Bool} {p : Prop} [Decidable p] :
    decide p = b ↔ (p ↔ b = true) := by cases b <;> simp

theorem wfChecksX_eq : P.wfChecksX P.index = P.wfChecks := by
  simp only [wfChecksX, wfChecks, List.cons.injEq, Prod.mk.injEq, true_and, and_true]
  refine eq_decide ?_
  rw [allSorts_iff]
  unfold LitSortsUsed
  refine forall_congr' fun k => imp_congr_right fun _ => ?_
  simp only [index, Std.HashSet.contains_ofList, List.contains_iff_mem, List.mem_map,
    Bool.or_eq_true, beq_iff_eq]
  constructor
  · rintro (((h | h) | h) | h) h1 h2
    · exact absurd h h1
    · exact absurd h h2
    · exact .inl h
    · exact .inr h
  · intro h
    by_cases h1 : P.kind k = .base
    · exact .inl (.inl (.inl h1))
    by_cases h2 : P.kind k = .triple
    · exact .inl (.inl (.inr h2))
    rcases h h1 h2 with h | h
    · exact .inl (.inr h)
    · exact .inr h

theorem rdfChecksX_eq : P.rdfChecksX P.index = P.rdfChecks := by
  simp only [rdfChecksX, rdfChecks, List.cons.injEq, Prod.mk.injEq, true_and, and_true]
  refine ⟨eq_decide ?_, eq_decide ?_, eq_decide ?_, eq_decide ?_, eq_decide ?_, eq_decide ?_⟩
  · rw [allSorts_iff]; simp [sIX_eq, E_index, eq_decide_iff]
  · rw [allSorts_iff]; simp [sIX_eq, E_index, decide_eq_iff]
  · rw [allSorts_iff]; simp [sIX_eq, E_index, decide_eq_iff]
  · rw [allSorts_iff]; simp [sIX_eq, E_index, decide_eq_iff]
  · simp [List.all_eq_true, holdsIX_eq]
  · simp [List.all_eq_true, sIX_eq, E_index]

theorem rdfsChecksX_eq : P.rdfsChecksX P.index = P.rdfsChecks := by
  simp only [rdfsChecksX, rdfsChecks, List.cons.injEq, Prod.mk.injEq, true_and, and_true]
  refine ⟨eq_decide ?_, eq_decide ?_, eq_decide ?_, eq_decide ?_, eq_decide ?_, eq_decide ?_,
    eq_decide ?_, eq_decide ?_, eq_decide ?_, eq_decide ?_, eq_decide ?_, eq_decide ?_,
    eq_decide ?_, eq_decide ?_, eq_decide ?_, eq_decide ?_⟩
  · rw [allSorts_iff]; simp [sIX_eq, E_index, decide_eq_iff]
  · simp [sIX_eq, E_index, decide_eq_iff, and_assoc]
  · simp [List.all_eq_true, mem_withP, sIX_eq, E_index, and_imp, decide_eq_iff]
  · simp [List.all_eq_true, mem_withP, sIX_eq, E_index, and_imp, decide_eq_iff]
  · rw [allSorts_iff]
    refine forall_congr' fun k => imp_congr_right fun _ => ?_
    cases P.ipB k <;> simp [sIX_eq, E_index]
  · simp [List.all_eq_true, mem_withP, mem_withPS, sIX_eq, E_index, and_imp, decide_eq_iff]
  · simp [List.all_eq_true, mem_withP, sIX_eq, E_index, and_imp, decide_eq_iff, and_assoc]
  · simp [List.all_eq_true, mem_withPO, sIX_eq, E_index, and_imp, decide_eq_iff]
  · simp [List.all_eq_true, mem_withPO, sIX_eq, E_index, and_imp, decide_eq_iff]
  · simp [List.all_eq_true, mem_withP, mem_withPS, sIX_eq, E_index, and_imp, decide_eq_iff]
  · simp [List.all_eq_true, mem_withP, mem_withPO, sIX_eq, E_index, and_imp, decide_eq_iff, and_assoc]
  · simp [List.all_eq_true, mem_withPO, sIX_eq, E_index, and_imp, decide_eq_iff]
  · simp [List.all_eq_true, mem_withPO, sIX_eq, E_index, and_imp, decide_eq_iff]
  · simp [sIX_eq, E_index, decide_eq_iff]
  · simp [List.all_eq_true, holdsIX_eq]
  · simp [List.all_eq_true, sIX_eq, E_index, and_assoc]

end Presentation

end LeanRDF.Model
