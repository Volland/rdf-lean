import LeanRDFStatements.Export

/-!
# The exact decoder

`decode v g` reads every statement IRI that is the subject of one of the export's own predicates
as a record: the object of its `rdf:reifies` triple gives the content, its `tm:` triples the
clocks. It then accepts the result only if it is well formed and its export in `v` has exactly
the triples of `g`. So the decoder is sound by construction (`toRDF_decode`), and
`decode_toRDF` proves it complete: every well-formed statement graph is read back from its own
export.
-/

namespace LeanRDF.Statements

open Vocab

/-! ## Reading terms -/

/-- A non-negative integer as a natural number. -/
def natOf? (n : Int) : Option Nat := if 0 ≤ n then some n.toNat else none

/-- The eid of a statement IRI. -/
def stmtEid? : Term → Option Nat
  | .iri i =>
    if isStmtIRI i then (Xsd.parseIntegerChars (i.val.toList.drop stmtNS.length)).bind natOf?
    else none
  | _ => none

/-- A node from a term: a statement IRI is a reference, anything else a term. -/
def nodeOf (t : Term) : Node :=
  match stmtEid? t with
  | some e => .eid e
  | none => .term t

/-- The value of an `xsd:integer` literal. -/
def litInt? : Term → Option Int
  | .lit (.typed lex dt) => if dt = xsdInteger then Xsd.parseInteger lex else none
  | _ => none

/-- The value of a non-negative `xsd:integer` literal. -/
def litNat? (t : Term) : Option Nat := (litInt? t).bind natOf?

theorem stmtEid?_stmtIRI (e : Nat) : stmtEid? (.iri (stmtIRI e)) = some e := by
  have hl : stmtNS.length = stmtNS.toList.length := String.length_toList.symm
  have hc : (stmtIRI e).val.toList = stmtNS.toList ++ (Xsd.canonicalInteger e).toList := by
    simp [stmtIRI, String.toList_append]
  have hp : Xsd.parseIntegerChars (Xsd.canonicalInteger e).toList = some e :=
    Xsd.parseInteger_canonical e
  simp only [stmtEid?, isStmtIRI, hc, hl, List.take_left, beq_self_eq_true, ite_true,
    List.drop_left, hp]
  simp [natOf?]

theorem stmtIRI_inj {a b : Nat} (h : stmtIRI a = stmtIRI b) : a = b := by
  have := stmtEid?_stmtIRI a
  rw [h, stmtEid?_stmtIRI] at this
  exact (Option.some.inj this).symm

theorem stmtEid?_none {t : Term} (h : termHasStmtIRI t = false) : stmtEid? t = none := by
  cases t with
  | iri i => simp only [termHasStmtIRI] at h; simp [stmtEid?, h]
  | _ => rfl

theorem nodeOf_nodeTerm {n : Node} (h : nodeHasStmtIRI n = false) : nodeOf (nodeTerm n) = n := by
  cases n with
  | term t => simp only [nodeHasStmtIRI] at h; simp [nodeOf, nodeTerm, stmtEid?_none h]
  | eid e => simp [nodeOf, nodeTerm, stmtEid?_stmtIRI]

theorem litInt?_intLit (n : Int) : litInt? (intLit n) = some n := by
  simp [litInt?, intLit, Xsd.parseInteger_canonical]

theorem litNat?_intLit (n : Nat) : litNat? (intLit n) = some n := by
  simp [litNat?, litInt?_intLit, natOf?]

/-! ## Sorted sets of eids -/

/-- Insert into a strictly increasing list, keeping it strictly increasing. -/
def insertSorted (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x < y then x :: y :: ys else if x = y then y :: ys else y :: insertSorted x ys

/-- The distinct elements of a list, increasing. -/
def sortedSet (l : List Nat) : List Nat := l.foldr insertSorted []

theorem mem_insertSorted {x z : Nat} : ∀ {l : List Nat}, z ∈ insertSorted x l ↔ z = x ∨ z ∈ l
  | [] => by simp [insertSorted]
  | y :: ys => by
    unfold insertSorted
    split
    · simp
    · split
      · rename_i h; subst h; simp
      · rw [List.mem_cons, mem_insertSorted, List.mem_cons]; exact or_left_comm

theorem pairwise_insertSorted {x : Nat} : ∀ {l : List Nat}, l.Pairwise (· < ·) →
    (insertSorted x l).Pairwise (· < ·)
  | [], _ => by simp [insertSorted]
  | y :: ys, h => by
    unfold insertSorted
    split
    · rename_i hxy
      exact List.pairwise_cons.2 ⟨fun z hz => by
        rcases List.mem_cons.1 hz with rfl | hz
        · exact hxy
        · exact Nat.lt_trans hxy ((List.pairwise_cons.1 h).1 z hz), h⟩
    · split
      · exact h
      · rename_i h1 h2
        refine List.pairwise_cons.2 ⟨fun z hz => ?_, pairwise_insertSorted (List.pairwise_cons.1 h).2⟩
        rcases mem_insertSorted.1 hz with rfl | hz
        · omega
        · exact (List.pairwise_cons.1 h).1 z hz

theorem mem_sortedSet {z : Nat} {l : List Nat} : z ∈ sortedSet l ↔ z ∈ l := by
  induction l with
  | nil => simp [sortedSet]
  | cons x l ih => simp only [sortedSet, List.foldr_cons] at ih ⊢; rw [mem_insertSorted, ih]; simp

theorem pairwise_sortedSet (l : List Nat) : (sortedSet l).Pairwise (· < ·) := by
  induction l with
  | nil => simp [sortedSet]
  | cons x l ih => exact pairwise_insertSorted ih

/-- Two strictly increasing lists with the same elements are equal. -/
theorem eq_of_pairwise_mem : ∀ {l₁ l₂ : List Nat}, l₁.Pairwise (· < ·) → l₂.Pairwise (· < ·) →
    (∀ x, x ∈ l₁ ↔ x ∈ l₂) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], y :: _, _, _, h => absurd ((h y).2 (List.mem_cons_self ..)) (by simp)
  | x :: _, [], _, _, h => absurd ((h x).1 (List.mem_cons_self ..)) (by simp)
  | x :: xs, y :: ys, h₁, h₂, h => by
    have hxy : x = y := by
      rcases List.mem_cons.1 ((h x).1 (List.mem_cons_self ..)) with e | hx'
      · exact e
      · rcases List.mem_cons.1 ((h y).2 (List.mem_cons_self ..)) with e | hy'
        · exact e.symm
        · have a := (List.pairwise_cons.1 h₂).1 x hx'
          have b := (List.pairwise_cons.1 h₁).1 y hy'
          omega
    subst hxy
    refine congrArg _ (eq_of_pairwise_mem (List.pairwise_cons.1 h₁).2 (List.pairwise_cons.1 h₂).2
      fun z => ⟨fun hz => ?_, fun hz => ?_⟩)
    · have a := (List.pairwise_cons.1 h₁).1 z hz
      rcases List.mem_cons.1 ((h z).1 (List.mem_cons_of_mem _ hz)) with e | h'
      · omega
      · exact h'
    · have a := (List.pairwise_cons.1 h₂).1 z hz
      rcases List.mem_cons.1 ((h z).2 (List.mem_cons_of_mem _ hz)) with e | h'
      · omega
      · exact h'

/-! ## The decoder -/

/-- A predicate of the export's own. -/
def isMeta : Term → Bool
  | .iri i => metaPreds.contains i
  | _ => false

/-- The eids named by the export's own triples, increasing. -/
def eidsOf (ts : List Triple) : List Nat :=
  sortedSet (ts.filterMap fun t => if isMeta t.p then stmtEid? t.s else none)

/-- The triple with subject `stmt:e` and predicate `P`, if any. -/
def findMeta (ts : List Triple) (e : Nat) (P : IRI) : Option Triple :=
  ts.find? fun t => t.s == .iri (stmtIRI e) && t.p == .iri P

/-- The record that the export's own triples describe for `e`. -/
def recordAt (ts : List Triple) (e : Nat) : Option Record := do
  let rt ← findMeta ts e rdf.reifies
  let (s', p', o') ← match rt.o with | .triple s p o => some (s, p, o) | _ => none
  let p ← match p' with | .iri i => some i | _ => none
  let tx ← (findMeta ts e tm.txAdded).bind (litNat? ·.o)
  some { eid := e, s := nodeOf s', p, o := nodeOf o', txAdded := tx
         txRetracted := (findMeta ts e tm.txRetracted).bind (litNat? ·.o)
         validFrom := (findMeta ts e tm.validFrom).bind (litInt? ·.o)
         validTo := (findMeta ts e tm.validTo).bind (litInt? ·.o) }

/-- Why `g` is not the export of `sg`: a triple of `g` it lacks, or one of its own `g` lacks. -/
def mismatch (v : View) (sg : StatementGraph) (g : Graph) : String :=
  let ex := sg.toRDF v
  match g.toList.find? (fun t => !decide (t ∈ ex)) with
  | some t => s!"triple {t.s.toNTriples} {t.p.toNTriples} {t.o.toNTriples} is not part of the export"
  | none =>
    match ex.toList.find? (fun t => !decide (t ∈ g)) with
    | some t =>
      let owner := (sg.records.find? fun r => decide (t ∈ r.triples v)).map (·.eid)
      s!"statement {owner.getD 0}: triple {t.s.toNTriples} {t.p.toNTriples} {t.o.toNTriples} is missing"
    | none => "the export differs"

-- @tg: implements:: [[openspec:statement-graphs#Exact decoding]]
/-- Read a statement graph back from its export in a view, or say why `g` is not an export. -/
def decode (v : View) (g : Graph) : Except String StatementGraph := do
  let ts := g.toList
  let rs ← (eidsOf ts).mapM fun e =>
    match recordAt ts e with
    | some r => .ok r
    | none => .error s!"statement {e}: no complete rdf:reifies and tm:txAdded triples"
  if h : rs.Pairwise (·.eid < ·.eid) then
    let sg : StatementGraph := ⟨rs, h⟩
    if sg.WellFormed then
      if (sg.toRDF v).toList == ts then return sg
      else throw (mismatch v sg g)
    else
      throw s!"statement {((sg.check.head?).map (·.1)).getD 0} breaks {((sg.check.head?).map (·.2.name)).getD ""}"
  else throw "statements are not in increasing eid order"

/-! ## Soundness -/

theorem toList_beq {g h : Graph} (e : (g.toList == h.toList) = true) : ∀ t, t ∈ g ↔ t ∈ h := by
  have := beq_iff_eq.1 e
  intro t; rw [← Graph.mem_toList, this, Graph.mem_toList]

-- @tg: implements:: [[openspec:statement-graphs#Exact decoding]]
/-- Soundness: whatever `decode` accepts is well formed and exports to exactly `g`. -/
theorem toRDF_decode {v : View} {g : Graph} {sg : StatementGraph} (h : decode v g = .ok sg) :
    sg.WellFormed ∧ ∀ t, t ∈ sg.toRDF v ↔ t ∈ g := by
  unfold decode at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  rename_i rs _
  split at h
  · rename_i hp
    split at h
    · rename_i hw
      split at h
      · rename_i he; cases h; exact ⟨hw, toList_beq he⟩
      · cases h
    · cases h
  · cases h

/-! ## Completeness -/

section
variable {v : View} {sg : StatementGraph}

private theorem mem_stmt {r : Record} : r.stmt = .iri (stmtIRI r.eid) := rfl

/-- A triple of the export with subject `stmt:e` and one of the export's predicates belongs to
the record `e`, as its reifying triple or a clock. -/
private theorem meta_owner (hw : sg.WellFormed) {t : Triple} (ht : t ∈ sg.toRDF v) {e : Nat}
    (hs : t.s = .iri (stmtIRI e)) (hm : isMeta t.p = true) :
    ∃ r ∈ sg.records, r.eid = e ∧ (t = r.reifying ∨ t ∈ r.clocks) := by
  obtain ⟨r, hr, ht⟩ := StatementGraph.mem_toRDF.1 ht
  rcases Record.mem_triples.1 ht with rfl | hc | ⟨-, rfl⟩
  · exact ⟨r, hr, stmtIRI_inj (by injection hs), .inl rfl⟩
  · obtain ⟨hcs, -⟩ := Record.mem_clocks hc
    rw [hcs] at hs
    exact ⟨r, hr, stmtIRI_inj (by injection hs), .inr hc⟩
  · obtain ⟨-, -, -, -, hpred⟩ := Record.ok_of_violations_nil (hw r hr)
    simp only [Record.predOk, Bool.not_eq_true'] at hpred
    simp only [Record.base, isMeta] at hm
    rw [hm] at hpred; cases hpred

/-- Records with the same eid are the same record. -/
private theorem eid_unique {r r' : Record} (hr : r ∈ sg.records) (hr' : r' ∈ sg.records)
    (h : r.eid = r'.eid) : r = r' := by
  have a := StatementGraph.find?_of_mem hr
  have b := StatementGraph.find?_of_mem hr'
  rw [h, b] at a; exact (Option.some.inj a).symm

/-- `find?` with a predicate that exactly one member satisfies. -/
private theorem find?_unique {l : List Triple} {p : Triple → Bool} {y : Triple} (hy : y ∈ l)
    (hp : p y = true) (hu : ∀ x ∈ l, p x = true → x = y) : l.find? p = some y := by
  cases hf : l.find? p with
  | none => have := List.find?_eq_none.1 hf y hy; simp [hp] at this
  | some x => rw [hu x (List.mem_of_find?_eq_some hf) (List.find?_some hf)]

/-- `find?` with a predicate no member satisfies. -/
private theorem find?_none' {l : List Triple} {p : Triple → Bool} (hu : ∀ x ∈ l, p x = false) :
    l.find? p = none := List.find?_eq_none.2 fun x hx => by simp [hu x hx]

private theorem metaPreds_iri {P : IRI} (h : P ∈ metaPreds) : isMeta (.iri P) = true := by
  simp [isMeta, h]

/-- The clock triples of a record, by predicate. -/
private theorem clock_pred {r : Record} {t : Triple} (hc : t ∈ r.clocks) :
    (t.p = .iri tm.txAdded → t = ⟨r.stmt, .iri tm.txAdded, intLit r.txAdded⟩) ∧
    (t.p = .iri tm.txRetracted → ∃ d, r.txRetracted = some d ∧ t = ⟨r.stmt, .iri tm.txRetracted, intLit d⟩) ∧
    (t.p = .iri tm.validFrom → ∃ d, r.validFrom = some d ∧ t = ⟨r.stmt, .iri tm.validFrom, intLit d⟩) ∧
    (t.p = .iri tm.validTo → ∃ d, r.validTo = some d ∧ t = ⟨r.stmt, .iri tm.validTo, intLit d⟩) ∧
    t.p ≠ .iri rdf.reifies := by
  simp only [Record.clocks, List.mem_cons, List.mem_append, List.mem_map, Option.mem_toList] at hc
  rcases hc with ((rfl | ⟨d, hd, rfl⟩) | ⟨d, hd, rfl⟩) | ⟨d, hd, rfl⟩ <;>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;>
    first | rfl | exact ⟨d, hd, rfl⟩ | (simp only [Term.iri.injEq] at h; exact absurd h (by decide))

/-- `findMeta` on an export finds the record's own triple with predicate `P`, if it has one. -/
private theorem findMeta_eq (hw : sg.WellFormed) {r : Record} (hr : r ∈ sg.records) {P : IRI}
    (hP : P ∈ metaPreds) (y? : Option Triple)
    (hy : ∀ x, (x = r.reifying ∨ x ∈ r.clocks) → x.p = .iri P → y? = some x)
    (hy2 : ∀ y, y? = some y → (y = r.reifying ∨ y ∈ r.clocks) ∧ y.p = .iri P) :
    findMeta (sg.toRDF v).toList r.eid P = y? := by
  have own : ∀ x, (x = r.reifying ∨ x ∈ r.clocks) → x ∈ (sg.toRDF v).toList := fun x hx =>
    Graph.mem_toList.2 (StatementGraph.mem_toRDF.2 ⟨r, hr, Record.mem_triples.2 (by
      rcases hx with rfl | hx
      · exact .inl rfl
      · exact .inr (.inl hx))⟩)
  have subj : ∀ x, (x = r.reifying ∨ x ∈ r.clocks) → x.s = .iri (stmtIRI r.eid) := fun x hx => by
    rcases hx with rfl | hx
    · rfl
    · exact (Record.mem_clocks hx).1
  have pick : ∀ x ∈ (sg.toRDF v).toList,
      (x.s == .iri (stmtIRI r.eid) && x.p == .iri P) = true → x = r.reifying ∨ x ∈ r.clocks := by
    intro x hx hp
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨r', hr', he, hcase⟩ := meta_owner hw (Graph.mem_toList.1 hx) hp.1
      (by rw [hp.2]; exact metaPreds_iri hP)
    rw [← eid_unique hr' hr he]
    exact hcase
  cases hq : y? with
  | none =>
    refine find?_none' fun x hx => ?_
    cases hb : (x.s == .iri (stmtIRI r.eid) && x.p == .iri P)
    · rfl
    · have hx' := pick x hx hb
      simp only [Bool.and_eq_true, beq_iff_eq] at hb
      rw [hy x hx' hb.2] at hq; cases hq
  | some y =>
    obtain ⟨hy', hyp⟩ := hy2 y hq
    refine find?_unique (own y hy') (by simp [subj y hy', hyp]) fun x hx hp => ?_
    have hx' := pick x hx hp
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    have := hy x hx' hp.2
    rw [hq] at this; exact (Option.some.inj this).symm

private theorem reifying_p (r : Record) : r.reifying.p = .iri rdf.reifies := rfl

private theorem recordAt_toRDF (hw : sg.WellFormed) {r : Record} (hr : r ∈ sg.records) :
    recordAt (sg.toRDF v).toList r.eid = some r := by
  obtain ⟨-, -, -, hiri, -⟩ := Record.ok_of_violations_nil (hw r hr)
  simp only [Record.iriOk, Bool.not_eq_true', Bool.or_eq_false_iff] at hiri
  obtain ⟨⟨hs, -⟩, ho⟩ := hiri
  have hre : findMeta (sg.toRDF v).toList r.eid rdf.reifies = some r.reifying :=
    findMeta_eq hw hr (by decide) _ (fun x hx hp => by
      rcases hx with rfl | hx
      · rfl
      · exact absurd hp (clock_pred hx).2.2.2.2)
      (fun y hy => by cases hy; exact ⟨.inl rfl, rfl⟩)
  have htx : findMeta (sg.toRDF v).toList r.eid tm.txAdded =
      some ⟨r.stmt, .iri tm.txAdded, intLit r.txAdded⟩ :=
    findMeta_eq hw hr (by decide) _ (fun x hx hp => by
      rcases hx with rfl | hx
      · exact absurd hp (by rw [reifying_p]; decide)
      · rw [(clock_pred hx).1 hp])
      (fun y hy => by cases hy; exact ⟨.inr (by simp [Record.clocks]), rfl⟩)
  have hret : findMeta (sg.toRDF v).toList r.eid tm.txRetracted =
      r.txRetracted.map fun d => ⟨r.stmt, .iri tm.txRetracted, intLit d⟩ :=
    findMeta_eq hw hr (by decide) _ (fun x hx hp => by
      rcases hx with rfl | hx
      · exact absurd hp (by rw [reifying_p]; decide)
      · obtain ⟨d, hd, rfl⟩ := (clock_pred hx).2.1 hp; simp [hd])
      (fun y hy => by
        cases hd : r.txRetracted with
        | none => rw [hd] at hy; cases hy
        | some d =>
          rw [hd] at hy; cases hy
          exact ⟨.inr (by simp [Record.clocks, hd]), rfl⟩)
  have hvf : findMeta (sg.toRDF v).toList r.eid tm.validFrom =
      r.validFrom.map fun d => ⟨r.stmt, .iri tm.validFrom, intLit d⟩ :=
    findMeta_eq hw hr (by decide) _ (fun x hx hp => by
      rcases hx with rfl | hx
      · exact absurd hp (by rw [reifying_p]; decide)
      · obtain ⟨d, hd, rfl⟩ := (clock_pred hx).2.2.1 hp; simp [hd])
      (fun y hy => by
        cases hd : r.validFrom with
        | none => rw [hd] at hy; cases hy
        | some d =>
          rw [hd] at hy; cases hy
          exact ⟨.inr (by simp [Record.clocks, hd]), rfl⟩)
  have hvt : findMeta (sg.toRDF v).toList r.eid tm.validTo =
      r.validTo.map fun d => ⟨r.stmt, .iri tm.validTo, intLit d⟩ :=
    findMeta_eq hw hr (by decide) _ (fun x hx hp => by
      rcases hx with rfl | hx
      · exact absurd hp (by rw [reifying_p]; decide)
      · obtain ⟨d, hd, rfl⟩ := (clock_pred hx).2.2.2.1 hp; simp [hd])
      (fun y hy => by
        cases hd : r.validTo with
        | none => rw [hd] at hy; cases hy
        | some d =>
          rw [hd] at hy; cases hy
          exact ⟨.inr (by simp [Record.clocks, hd]), rfl⟩)
  unfold recordAt
  rw [hre, htx, hret, hvf, hvt]
  simp only [Record.reifying, Record.base, Triple.toTerm, Option.bind_some, litNat?_intLit,
    nodeOf_nodeTerm hs, nodeOf_nodeTerm ho]
  cases hR : r.txRetracted <;> cases hF : r.validFrom <;> cases hT : r.validTo <;>
    simp [Option.map, litNat?_intLit, litInt?_intLit] <;> cases r <;> simp_all [nodeOf_nodeTerm]

private theorem eidsOf_toRDF (hw : sg.WellFormed) : eidsOf (sg.toRDF v).toList = sg.eids := by
  refine eq_of_pairwise_mem (pairwise_sortedSet _) (List.pairwise_map.2 sg.sorted) fun x => ?_
  rw [eidsOf, mem_sortedSet, StatementGraph.mem_eids, List.mem_filterMap]
  constructor
  · rintro ⟨t, ht, hx⟩
    split at hx
    · rename_i hm
      obtain ⟨r, hr, ht⟩ := StatementGraph.mem_toRDF.1 (Graph.mem_toList.1 ht)
      rcases Record.mem_triples.1 ht with rfl | hc | ⟨-, rfl⟩
      · rw [show r.reifying.s = .iri (stmtIRI r.eid) from rfl, stmtEid?_stmtIRI] at hx
        exact ⟨r, hr, Option.some.inj hx⟩
      · rw [(Record.mem_clocks hc).1, mem_stmt, stmtEid?_stmtIRI] at hx
        exact ⟨r, hr, Option.some.inj hx⟩
      · obtain ⟨-, -, -, -, hpred⟩ := Record.ok_of_violations_nil (hw r hr)
        simp only [Record.predOk, Bool.not_eq_true'] at hpred
        simp only [Record.base, isMeta] at hm
        rw [hm] at hpred; cases hpred
    · cases hx
  · rintro ⟨r, hr, rfl⟩
    refine ⟨r.reifying, Graph.mem_toList.2 (StatementGraph.mem_toRDF.2
      ⟨r, hr, Record.mem_triples.2 (.inl rfl)⟩), ?_⟩
    simp [reifying_p, isMeta, metaPreds, Record.reifying, Record.stmt, stmtEid?_stmtIRI]

private theorem mapM_ok {f : Nat → Except String Record} :
    ∀ l : List Record, (∀ r ∈ l, f r.eid = .ok r) → (l.map (·.eid)).mapM f = .ok l
  | [], _ => rfl
  | r :: l, h => by
    simp only [List.map_cons, List.mapM_cons, h r (List.mem_cons_self ..),
      mapM_ok l (fun r' hr' => h r' (List.mem_cons_of_mem _ hr'))]
    rfl

-- @tg: implements:: [[openspec:statement-graphs#Exact decoding]]
/-- Completeness: every well-formed statement graph is read back from its own export. -/
theorem decode_toRDF (hw : sg.WellFormed) : decode v (sg.toRDF v) = .ok sg := by
  unfold decode
  simp only [eidsOf_toRDF hw, StatementGraph.eids]
  rw [mapM_ok sg.records (fun r hr => by simp [recordAt_toRDF hw hr])]
  simp only [bind, Except.bind, sg.sorted, dite_true]
  rw [ite_eq_left_iff.2 (fun h => absurd hw h)]
  simp only [beq_self_eq_true, ite_true]
  rfl

end

end LeanRDF.Statements
