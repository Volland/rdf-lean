import LeanRDF
import LeanRDFStatements.Abstract.Kernel
import LeanRDFStatements.Abstract.Export

/-!
# Statement records

tiramemsu's statement records over LeanRDF terms: an eid, a subject and an object that are each
a term or a reference to another record's eid, a predicate IRI, a transaction interval and a
valid-time interval. A statement graph is a finite set of records, kept as a list sorted by eid,
so that equal graphs are equal values. Dangling references and reference cycles are allowed;
`WellFormed` forbids self-reference, keeps strict RDF 1.2 positions, and keeps the export's
reserved names out of the content.
-/

namespace LeanRDF.Statements

open StatementExport Vocab

/-- A subject or object: a term, or a reference to an eid (the paper's `Node T E`). -/
abbrev Node := StatementExport.Node Term Nat

instance : Repr Node where
  reprPrec n _ := match n with
    | .term t => "term " ++ repr t
    | .eid e => "eid " ++ repr e

-- @tg: implements:: [[openspec:statement-graphs#Statement records]]
/-- A bitemporal statement record (tiramemsu): live in transaction time on
`[txAdded, txRetracted)` and in valid time on `[validFrom, validTo)`, epoch milliseconds, an
absent bound being unbounded. -/
structure Record where
  eid : Nat
  s : Node
  p : IRI
  o : Node
  txAdded : Nat
  txRetracted : Option Nat := none
  validFrom : Option Int := none
  validTo : Option Int := none
  deriving DecidableEq, Repr

namespace Record

/-- The eids a record references, in subject then object. -/
def refs (r : Record) : List Nat := r.s.refs ++ r.o.refs

/-- The record's content, in the paper's form, with the predicate as a term. -/
def content (r : Record) : Content Term Nat := ⟨r.s, .iri r.p, r.o⟩

end Record

/-- A statement graph: records sorted by strictly increasing eid, so eids are distinct and two
graphs with the same records are equal. -/
structure StatementGraph where
  records : List Record
  sorted : records.Pairwise (·.eid < ·.eid)

namespace StatementGraph

@[ext] theorem ext {g h : StatementGraph} (e : g.records = h.records) : g = h := by
  cases g; cases h; cases e; rfl

instance : DecidableEq StatementGraph := fun g h =>
  if e : g.records = h.records then isTrue (ext e) else isFalse fun h' => e (h' ▸ rfl)

instance : Repr StatementGraph := ⟨fun g _ => repr g.records⟩

/-- The empty statement graph. -/
def empty : StatementGraph := ⟨[], .nil⟩

/-- The eids of the graph, increasing. -/
def eids (g : StatementGraph) : List Nat := g.records.map (·.eid)

/-- The record with an eid. -/
def find? (g : StatementGraph) (e : Nat) : Option Record := g.records.find? (·.eid == e)

/-- Membership of an eid, as the paper's record set `S`. -/
def S (g : StatementGraph) (e : Nat) : Prop := e ∈ g.eids

/-- The content of each eid, in the paper's form; eids outside the graph get a placeholder. -/
def content (g : StatementGraph) (e : Nat) : Content Term Nat :=
  match g.find? e with
  | some r => r.content
  | none => ⟨.term default, default, .term default⟩

private theorem find?_sorted {l : List Record} (hs : l.Pairwise (·.eid < ·.eid)) {r : Record}
    (h : r ∈ l) : l.find? (·.eid == r.eid) = some r := by
  induction l with
  | nil => cases h
  | cons a l ih =>
    rcases List.mem_cons.1 h with rfl | hl
    · simp
    · have hne : a.eid ≠ r.eid := Nat.ne_of_lt ((List.pairwise_cons.1 hs).1 r hl)
      rw [List.find?_cons_of_neg (by simpa using hne)]
      exact ih (List.pairwise_cons.1 hs).2 hl

theorem find?_of_mem {g : StatementGraph} {r : Record} (h : r ∈ g.records) :
    g.find? r.eid = some r :=
  find?_sorted g.sorted h

theorem mem_of_find? {g : StatementGraph} {e : Nat} {r : Record} (h : g.find? e = some r) :
    r ∈ g.records ∧ r.eid = e := by
  unfold find? at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem mem_eids {g : StatementGraph} {e : Nat} : e ∈ g.eids ↔ ∃ r ∈ g.records, r.eid = e := by
  simp [eids]

theorem content_of_mem {g : StatementGraph} {r : Record} (h : r ∈ g.records) :
    g.content r.eid = r.content := by
  simp [content, find?_of_mem h]

/-- The eids referenced by the record with eid `e` (the paper's `crefs`). -/
theorem crefs_of_mem {g : StatementGraph} {r : Record} (h : r ∈ g.records) :
    crefs g.content r.eid = r.refs := by
  simp [crefs, content_of_mem h, Record.content, Record.refs]

/-- The graph is finite: its eid list covers it. -/
theorem covered (g : StatementGraph) : Covered g.S := ⟨g.eids, fun _ h => h⟩

/-- Build a statement graph from records in any order; an eid used twice is an error. -/
def ofList? (rs : List Record) : Except String StatementGraph :=
  let sorted := rs.mergeSort (fun a b => a.eid ≤ b.eid)
  if h : sorted.Pairwise (·.eid < ·.eid) then .ok ⟨sorted, h⟩
  else
    let dup := (sorted.zip sorted.tail).find? (fun (a, b) => a.eid == b.eid)
    .error s!"eid {(dup.map (·.1.eid)).getD 0} is used twice"

end StatementGraph

/-! ## Reserved names -/

/-- The namespace of statement IRIs, `urn:tiramemsu:stmt:N`. -/
def stmtNS : String := "urn:tiramemsu:stmt:"

/-- The namespace of tiramemsu's time vocabulary. -/
def tmNS : String := "urn:tiramemsu:tm:"

namespace tm
/-- `tm:txAdded`: the transaction that added the record. -/
def txAdded : IRI := ⟨tmNS ++ "txAdded"⟩
/-- `tm:txRetracted`: the transaction that retracted the record. -/
def txRetracted : IRI := ⟨tmNS ++ "txRetracted"⟩
/-- `tm:validFrom`: the start of the valid-time interval, epoch milliseconds. -/
def validFrom : IRI := ⟨tmNS ++ "validFrom"⟩
/-- `tm:validTo`: the end of the valid-time interval, epoch milliseconds. -/
def validTo : IRI := ⟨tmNS ++ "validTo"⟩
end tm

/-- The predicates the export uses for its own triples. -/
def metaPreds : List IRI := [rdf.reifies, tm.txAdded, tm.txRetracted, tm.validFrom, tm.validTo]

/-- An IRI in the statement namespace. -/
def isStmtIRI (i : IRI) : Bool := i.val.toList.take stmtNS.length == stmtNS.toList

/-- Whether a statement IRI occurs in a term, inside triple terms too. -/
def termHasStmtIRI : Term → Bool
  | .iri i => isStmtIRI i
  | .triple s p o => termHasStmtIRI s || termHasStmtIRI p || termHasStmtIRI o
  | _ => false

/-- Whether a statement IRI occurs in a node's term. -/
def nodeHasStmtIRI : Node → Bool
  | .term t => termHasStmtIRI t
  | .eid _ => false

/-! ## Well-formedness -/

/-- A rule a record can break. -/
inductive Violation where
  | subjectPosition
  | objectPosition
  | selfReference
  | txInterval
  | validInterval
  | reservedIRI
  | reservedPredicate
  deriving DecidableEq, Repr

/-- The rule's name, as `leanrdf-sg check` reports it. -/
def Violation.name : Violation → String
  | .subjectPosition => "subject-position"
  | .objectPosition => "object-position"
  | .selfReference => "self-reference"
  | .txInterval => "tx-interval"
  | .validInterval => "valid-interval"
  | .reservedIRI => "reserved-iri"
  | .reservedPredicate => "reserved-predicate"

namespace Record

/-- The subject is an IRI, a blank node or a reference (RDF 1.2 Concepts §3.1). -/
def subjOk (r : Record) : Bool := match r.s with | .term t => t.isSubject | .eid _ => true

/-- The object is a strict RDF 1.2 object or a reference. -/
def objOk (r : Record) : Bool := match r.o with | .term t => t.isObject | .eid _ => true

/-- The record does not reference its own eid. -/
def selfOk (r : Record) : Bool := r.s != .eid r.eid && r.o != .eid r.eid

/-- No statement IRI occurs in the content. -/
def iriOk (r : Record) : Bool := !(nodeHasStmtIRI r.s || isStmtIRI r.p || nodeHasStmtIRI r.o)

/-- The predicate is none of the export's own. -/
def predOk (r : Record) : Bool := !metaPreds.contains r.p

/-- Each check with the rule it enforces. -/
def checks (r : Record) : List (Bool × Violation) :=
  let txOk := r.txRetracted.all (r.txAdded < ·)
  let validOk := match r.validFrom, r.validTo with
    | some a, some b => decide (a < b)
    | _, _ => true
  [(r.subjOk, .subjectPosition), (r.objOk, .objectPosition), (r.selfOk, .selfReference),
    (txOk, .txInterval), (validOk, .validInterval), (r.iriOk, .reservedIRI),
    (r.predOk, .reservedPredicate)]

/-- The rules a record breaks. -/
def violations (r : Record) : List Violation :=
  r.checks.filterMap fun (ok, v) => if ok then none else some v

private theorem passes {r : Record} (h : r.violations = []) {ok : Bool} {v : Violation}
    (hm : (ok, v) ∈ r.checks) : ok = true := by
  have := List.filterMap_eq_nil_iff.1 h (ok, v) hm
  cases ok <;> simp_all

/-- A record without violations passes the checks the export relies on. -/
theorem ok_of_violations_nil {r : Record} (h : r.violations = []) :
    r.subjOk = true ∧ r.objOk = true ∧ r.selfOk = true ∧ r.iriOk = true ∧ r.predOk = true :=
  ⟨passes h (v := .subjectPosition) (by simp [checks]),
   passes h (v := .objectPosition) (by simp [checks]),
   passes h (v := .selfReference) (by simp [checks]),
   passes h (v := .reservedIRI) (by simp [checks]),
   passes h (v := .reservedPredicate) (by simp [checks])⟩

end Record

namespace StatementGraph

-- @tg: implements:: [[openspec:statement-graphs#Statement graph well-formedness]]
/-- Every record keeps strict RDF 1.2 positions, references no own eid, has sane intervals, and
uses none of the export's reserved names. -/
def WellFormed (g : StatementGraph) : Prop := ∀ r ∈ g.records, r.violations = []

instance (g : StatementGraph) : Decidable g.WellFormed :=
  inferInstanceAs (Decidable (∀ r ∈ g.records, r.violations = []))

/-- Every violation, with the eid of the record that breaks it. -/
def check (g : StatementGraph) : List (Nat × Violation) :=
  g.records.flatMap fun r => r.violations.map (r.eid, ·)

theorem check_nil_iff {g : StatementGraph} : g.check = [] ↔ g.WellFormed := by
  simp [check, WellFormed, List.flatMap_eq_nil_iff]

end StatementGraph

end LeanRDF.Statements
