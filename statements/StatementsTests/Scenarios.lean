import LeanRDFStatements

/-! Scenarios of `statement-graphs`: records, well-formedness, views, the export, the exact
decoder, the kernel, the criterion, history closure and quoting. -/

namespace LeanRDF.Statements.Tests

open StatementExport Vocab StatementGraph

private def ex (n : String) : IRI := ⟨"http://example.org/" ++ n⟩
private def T (n : String) : Node := .term (.iri (ex n))
private def int (n : Int) : Node := .term (.lit (.typed (toString n) xsdInteger))

private def rec (e : Nat) (s : Node) (p : String) (o : Node) (tx : Nat := e)
    (ret : Option Nat := none) (vf vt : Option Int := none) : Record :=
  { eid := e, s, p := ex p, o, txAdded := tx, txRetracted := ret, validFrom := vf, validTo := vt }

private def sg! (rs : List Record) : StatementGraph := (StatementGraph.ofList? rs).toOption.getD .empty

private def e1 : Record := rec 1 (T "FRA") "route" (T "LHR")
private def e2 : Record := rec 2 (.eid 1) "distance" (int 655)
private def routes : StatementGraph := sg! [e1, e2]

/-! ## Statement records -/

-- @tg: verifies:: [[openspec:statement-graphs#Statement records#A record about a record]] {level: unit}
#guard e2.refs == [1] && e1.refs == [] && routes.find? 1 == some e1

-- @tg: verifies:: [[openspec:statement-graphs#Statement records#Duplicate eids are rejected]] {level: unit}
#guard match StatementGraph.ofList? [e1, { e2 with eid := 1 }] with
  | .error msg => msg == "eid 1 is used twice"
  | .ok _ => false

-- @tg: verifies:: [[openspec:statement-graphs#Statement records#Dangling references are representable]] {level: unit}
#guard match StatementGraph.ofList? [e2] with
  | .ok g => g.eids == [2] && g.isClosed == false
  | .error _ => false

/-! ## Well-formedness -/

private def violations (r : Record) : List (Nat × Violation) := (sg! [r]).check

-- @tg: verifies:: [[openspec:statement-graphs#Statement graph well-formedness#A reserved statement IRI in content]] {level: unit}
#guard violations (rec 7 (T "s") "p" (.term (.iri ⟨"urn:tiramemsu:stmt:5"⟩))) == [(7, .reservedIRI)]

-- @tg: verifies:: [[openspec:statement-graphs#Statement graph well-formedness#A reserved predicate]] {level: unit}
#guard violations { rec 7 (T "s") "p" (T "o") with p := tm.txAdded } == [(7, .reservedPredicate)]

-- @tg: verifies:: [[openspec:statement-graphs#Statement graph well-formedness#Self-reference]] {level: unit}
#guard violations (rec 3 (.eid 3) "p" (T "o")) == [(3, .selfReference)]

-- @tg: verifies:: [[openspec:statement-graphs#Statement graph well-formedness#Literal subject]] {level: unit}
#guard violations (rec 4 (.term (.lit (Literal.str "x"))) "p" (T "o")) == [(4, .subjectPosition)]

/-! ## Views -/

private def retracted : Record := rec 1 (T "s") "p" (T "o") 10 (some 20)

-- @tg: verifies:: [[openspec:statement-graphs#Views#Retraction is seen only after it happens]] {level: unit}
#guard retracted.live { tx := .asOf 15 } && !retracted.live { tx := .asOf 20 } &&
  !retracted.live { tx := .now } && retracted.live { tx := .history }

private def valid : Record := rec 1 (T "s") "p" (T "o") 1 none (some 0) (some 1000)

-- @tg: verifies:: [[openspec:statement-graphs#Views#Valid time is half-open]] {level: unit}
#guard valid.live { valid := .at 0 } && valid.live { valid := .at 999 } && !valid.live { valid := .at 1000 }

/-! ## The export -/

private def stmt (e : Nat) : Term := .iri (stmtIRI e)
private def tr (s p o : Term) : Triple := ⟨s, p, o⟩

-- @tg: verifies:: [[openspec:statement-graphs#Reifier export#A route and its distance]] {level: unit}
#guard (routes.toRDF {}).toList == (Graph.ofList
  [tr (stmt 1) (.iri rdf.reifies) (.triple (.iri (ex "FRA")) (.iri (ex "route")) (.iri (ex "LHR"))),
   tr (stmt 2) (.iri rdf.reifies) (.triple (stmt 1) (.iri (ex "distance")) (nodeTerm (int 655))),
   tr (stmt 1) (.iri tm.txAdded) (intLit 1), tr (stmt 2) (.iri tm.txAdded) (intLit 2),
   tr (.iri (ex "FRA")) (.iri (ex "route")) (.iri (ex "LHR")),
   tr (stmt 1) (.iri (ex "distance")) (nodeTerm (int 655))]).toList

private def r5 : Record := rec 1 (T "s") "p" (T "o") 1 (some 5)

-- @tg: verifies:: [[openspec:statement-graphs#Reifier export#A retracted record is reified but not asserted]] {level: unit}
#guard
  let g := sg! [r5]
  let has (v : View) (t : Triple) := decide (t ∈ g.toRDF v)
  [({ tx := .now } : View), { tx := .asOf 4 }].all (fun v => has v r5.reifying &&
      has v (tr (stmt 1) (.iri tm.txRetracted) (intLit 5))) &&
    !has { tx := .now } r5.base && has { tx := .asOf 4 } r5.base

-- @tg: verifies:: [[openspec:statement-graphs#Reifier export#Export is strict RDF 1.2]] {level: unit}
example (g : StatementGraph) (v : View) (hw : g.WellFormed) : ∀ t ∈ g.toRDF v, t.WellFormed :=
  toRDF_wellFormed hw

/-! ## The exact decoder -/

private def supersede : StatementGraph := sg!
  [rec 1 (T "FRA") "route" (T "LHR") 1 (some 3), rec 2 (.eid 1) "distance" (int 650) 2 (some 3),
   rec 3 (T "FRA") "route" (T "LHR") 3, rec 4 (.eid 3) "distance" (int 655) 3,
   rec 5 (.eid 3) "supersedes" (.eid 1) 3]

-- @tg: verifies:: [[openspec:statement-graphs#Exact decoding#Round trip]] {level: unit}
#guard match decode { tx := .history } (supersede.toRDF { tx := .history }) with
  | .ok g => g == supersede && supersede.records.length == 5
  | .error _ => false

private def stray : Triple := tr (stmt 1) (.iri (ex "confidence")) (.lit (.typed "0.9" ⟨Xsd.ns ++ "decimal"⟩))

-- @tg: verifies:: [[openspec:statement-graphs#Exact decoding#A stray triple is rejected]] {level: unit}
#guard match decode {} ((routes.toRDF {}).insert stray) with
  | .error msg => msg.startsWith s!"triple {stray.s.toNTriples} {stray.p.toNTriples}"
  | .ok _ => false

-- @tg: verifies:: [[openspec:statement-graphs#Exact decoding#A missing assertion is rejected]] {level: unit}
#guard match decode {} (Graph.ofList ((routes.toRDF {}).toList.filter (· != e1.base))) with
  | .error msg => msg.startsWith "statement 1:"
  | .ok _ => false

-- @tg: verifies:: [[openspec:statement-graphs#Exact decoding#Decoding theorems]] {level: unit}
/-- info: 'LeanRDF.Statements.decode_toRDF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms decode_toRDF

/-- info: 'LeanRDF.Statements.toRDF_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms toRDF_decode

/-! ## The kernel -/

-- @tg: verifies:: [[openspec:statement-graphs#Export kernel#Dangling references are peeled]] {level: unit}
#guard (sg! [rec 2 (.eid 1) "distance" (int 655), rec 3 (.eid 2) "source" (T "x")]).kernel == []

-- @tg: verifies:: [[openspec:statement-graphs#Export kernel#A two-cycle is peeled]] {level: unit}
#guard (sg! [rec 1 (.eid 2) "p" (T "a"), rec 2 (.eid 1) "p" (T "b"), rec 3 (T "c") "p" (T "d")]).kernel == [3]

/-! ## The criterion -/

-- @tg: verifies:: [[openspec:statement-graphs#Statement Graph criterion#The criterion on LeanRDF types]] {level: unit}
example (g : StatementGraph) :
    (∃ G : SGraph Nat Term, G.IsSG ∧ DirectExport g.content id g.S G) ↔
      g.isClosed = true ∧ g.isAcyclic = true := criterion g

/-- info: 'LeanRDF.Statements.StatementGraph.criterion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms criterion

private def snapshot : StatementGraph := sg!
  [rec 3 (T "FRA") "route" (T "LHR") 3, rec 4 (.eid 3) "distance" (int 655) 3,
   rec 5 (.eid 3) "supersedes" (.eid 1) 3]

-- @tg: verifies:: [[openspec:statement-graphs#Statement Graph criterion#A dangling snapshot has no Statement Graph export]] {level: unit}
theorem snapshot_no_export : ¬ ∃ G : SGraph Nat Term, G.IsSG ∧ DirectExport snapshot.content id snapshot.S G :=
  fun h => absurd ((criterion snapshot).1 h).1 (by native_decide)

/-! ## History -/

-- @tg: verifies:: [[openspec:statement-graphs#History closure#The supersede example]] {level: unit}
theorem supersede_history : Closed (crefs supersede.content) supersede.S ∧ supersede.isAcyclic = true ∧
    snapshot.isClosed = false :=
  ⟨history_closed (by
    intro r hr x hx
    have : supersede.records.all (fun r => r.refs.all fun x =>
      supersede.records.any fun r' => r'.eid == x && decide (r'.txAdded ≤ r.txAdded)) = true := by
      native_decide
    obtain ⟨r', hr', h⟩ := List.any_eq_true.1
      (List.all_eq_true.1 (List.all_eq_true.1 this r hr) x hx)
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    exact ⟨r', hr', h⟩), by native_decide, by native_decide⟩

private def replay : StatementGraph := sg! [rec 1 (.eid 2) "p" (T "a") 5, rec 2 (.eid 1) "p" (T "b") 5]

-- @tg: verifies:: [[openspec:statement-graphs#History closure#A correction replay can cycle]] {level: unit}
#guard replay.isClosed && !replay.isAcyclic && replay.txOf 1 == replay.txOf 2

/-! ## Quoting -/

-- @tg: verifies:: [[openspec:statement-graphs#Quoting view#Quoting a nested record]] {level: unit}
#guard match routes.quote 2 with
  | .ok t => t == .triple (.triple (.iri (ex "FRA")) (.iri (ex "route")) (.iri (ex "LHR")))
      (.iri (ex "distance")) (nodeTerm (int 655)) &&
      !decide (Triple.WellFormed ⟨(t.asTriple?.map (·.s)).getD t, .iri (ex "p"), .iri (ex "o")⟩)
  | .error _ => false

-- @tg: verifies:: [[openspec:statement-graphs#Quoting view#Quoting a non-kernel record fails]] {level: unit}
#guard match (sg! [rec 2 (.eid 1) "distance" (int 655)]).quote 2 with
  | .error msg => msg.startsWith "statement 2 is outside the kernel"
  | .ok _ => false

end LeanRDF.Statements.Tests
