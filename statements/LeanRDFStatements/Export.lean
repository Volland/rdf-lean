import LeanRDFStatements.View

/-!
# The reifier export

A statement graph as an RDF 1.2 graph. Each record `e` becomes:
- `<urn:tiramemsu:stmt:e> rdf:reifies <<( s' p o' )>>`, where an eid reference `x` in subject
  or object becomes `<urn:tiramemsu:stmt:x>`;
- its clocks, `tm:txAdded` always and `tm:txRetracted`, `tm:validFromMs`, `tm:validToMs` when
  present, as `xsd:integer` literals (valid times in epoch milliseconds);
- the base triple `s' p o'` exactly when the record is live in the view.

References are names, so the export needs neither closure nor acyclicity, and it is strict
RDF 1.2 for every well-formed statement graph (`export_wellFormed`).
-/

namespace LeanRDF.Statements

open Vocab

/-- `xsd:integer`. -/
def xsdInteger : IRI := ⟨Xsd.ns ++ "integer"⟩

/-- The statement IRI of an eid, `urn:tiramemsu:stmt:e`. -/
def stmtIRI (e : Nat) : IRI := ⟨stmtNS ++ Xsd.canonicalInteger e⟩

/-- The term of a node: the term itself, or the statement IRI of the referenced eid. -/
def nodeTerm : Node → Term
  | .term t => t
  | .eid e => .iri (stmtIRI e)

/-- An integer as an `xsd:integer` literal in canonical form. -/
def intLit (n : Int) : Term := .lit (.typed (Xsd.canonicalInteger n) xsdInteger)

namespace Record

/-- The record's statement IRI as a term. -/
def stmt (r : Record) : Term := .iri (stmtIRI r.eid)

/-- The triple of the record's content, with references as statement IRIs. -/
def base (r : Record) : Triple := ⟨nodeTerm r.s, .iri r.p, nodeTerm r.o⟩

/-- `stmt:e rdf:reifies <<( s' p o' )>>`. -/
def reifying (r : Record) : Triple := ⟨r.stmt, .iri rdf.reifies, r.base.toTerm⟩

/-- The clock triples: `tm:txAdded` always, the others when present. -/
def clocks (r : Record) : List Triple :=
  ⟨r.stmt, .iri tm.txAdded, intLit r.txAdded⟩ ::
    (r.txRetracted.toList.map fun d => ⟨r.stmt, .iri tm.txRetracted, intLit d⟩) ++
    (r.validFrom.toList.map fun d => ⟨r.stmt, .iri tm.validFromMs, intLit d⟩) ++
    (r.validTo.toList.map fun d => ⟨r.stmt, .iri tm.validToMs, intLit d⟩)

/-- The triples the export writes for one record in a view. -/
def triples (v : View) (r : Record) : List Triple :=
  r.reifying :: r.clocks ++ (if r.live v then [r.base] else [])

theorem mem_triples {v : View} {r : Record} {t : Triple} :
    t ∈ r.triples v ↔ t = r.reifying ∨ t ∈ r.clocks ∨ (r.live v = true ∧ t = r.base) := by
  unfold triples
  by_cases hl : r.live v = true <;> simp [hl, or_assoc]

/-- A clock triple has the record's statement IRI as subject, a time predicate and an integer
literal as object. -/
theorem mem_clocks {r : Record} {t : Triple} (h : t ∈ r.clocks) :
    t.s = r.stmt ∧ ∃ (P : IRI) (n : Int), P ∈ [tm.txAdded, tm.txRetracted, tm.validFromMs, tm.validToMs] ∧
      t.p = .iri P ∧ t.o = intLit n := by
  simp only [clocks, List.mem_cons, List.mem_append, List.mem_map, Option.mem_toList] at h
  rcases h with ((rfl | ⟨d, -, rfl⟩) | ⟨d, -, rfl⟩) | ⟨d, -, rfl⟩
  · exact ⟨rfl, _, _, by simp, rfl, rfl⟩
  · exact ⟨rfl, _, _, by simp, rfl, rfl⟩
  · exact ⟨rfl, _, _, by simp, rfl, rfl⟩
  · exact ⟨rfl, _, _, by simp, rfl, rfl⟩

end Record

namespace StatementGraph

-- @tg: implements:: [[openspec:statement-graphs#Reifier export]]
/-- The export: the RDF 1.2 graph of a statement graph in a view. -/
def toRDF (v : View) (g : StatementGraph) : Graph :=
  Graph.ofList (g.records.flatMap (·.triples v))

theorem mem_toRDF {v : View} {g : StatementGraph} {t : Triple} :
    t ∈ g.toRDF v ↔ ∃ r ∈ g.records, t ∈ r.triples v := by
  simp [toRDF, Graph.mem_ofList, List.mem_flatMap]

end StatementGraph

/-! ## Strictness -/

private theorem nodeTerm_isSubject {r : Record} (h : r.subjOk = true) :
    (nodeTerm r.s).isSubject = true := by
  unfold Record.subjOk at h; cases hs : r.s <;> simp_all [nodeTerm, Term.isSubject]

private theorem nodeTerm_isObject {r : Record} (h : r.objOk = true) :
    (nodeTerm r.o).isObject = true := by
  unfold Record.objOk at h; cases ho : r.o <;> simp_all [nodeTerm, Term.isObject]

-- @tg: implements:: [[openspec:statement-graphs#Reifier export]]
/-- The export of a well-formed statement graph is strict RDF 1.2. -/
theorem StatementGraph.toRDF_wellFormed {v : View} {g : StatementGraph} (hw : g.WellFormed) :
    ∀ t ∈ g.toRDF v, t.WellFormed := by
  intro t ht
  obtain ⟨r, hr, ht⟩ := StatementGraph.mem_toRDF.1 ht
  obtain ⟨hs, ho, -⟩ := Record.ok_of_violations_nil (hw r hr)
  have hs' := nodeTerm_isSubject hs
  have ho' := nodeTerm_isObject ho
  have hb : r.base.WellFormed := by
    simp [Triple.WellFormed, Record.base, hs', ho', Term.isPredicate]
  rcases Record.mem_triples.1 ht with rfl | hc | ⟨-, rfl⟩
  · show ((Term.iri (stmtIRI r.eid)).isSubject && (Term.iri rdf.reifies).isPredicate &&
      ((nodeTerm r.s).isSubject && (Term.iri r.p).isPredicate && (nodeTerm r.o).isObject)) = true
    rw [hs', ho']; rfl
  · obtain ⟨hs, P, n, -, hp, ho⟩ := Record.mem_clocks hc
    simp [Triple.WellFormed, hs, hp, ho, Record.stmt, Term.isSubject, Term.isPredicate, intLit,
      Term.isObject]
  · exact hb

end LeanRDF.Statements
