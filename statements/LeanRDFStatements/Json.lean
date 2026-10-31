import LeanRDFStatements.Decode
import Lean.Data.Json

/-!
# Records as JSON lines

The input of `leanrdf-sg`: one record per line, with `eid`, `s`, `p`, `o`, `txAdded` and
optionally `txRetracted`, `validFrom` and `validTo`. A subject or object is a term in N-Triples
1.2 syntax, or `{"eid": n}` for a reference; the predicate is an IRI in N-Triples syntax; times
are integers (transaction numbers, epoch milliseconds). The same form is written back by
`leanrdf-sg decode`. Untrusted input code: what it reads is checked by `WellFormed`.
-/

namespace LeanRDF.Statements

open Lean (Json)

private def nodeOfJson (j : Json) : Except String Node := do
  match j with
  | .str s => return .term (← (NTriples.parseTerm s).mapError toString)
  | _ => return .eid (← j.getObjValAs? Nat "eid")

private def optField {α : Type} [Lean.FromJson α] (j : Json) (k : String) : Except String (Option α) :=
  match j.getObjVal? k with
  | .ok .null | .error _ => .ok none
  | .ok v => (Lean.fromJson? v).map some

/-- One record from its JSON object. -/
def Record.ofJson (j : Json) : Except String Record := do
  let p ← match ← (NTriples.parseTerm (← j.getObjValAs? String "p")).mapError toString with
    | .iri i => pure i
    | _ => throw "the predicate must be an IRI"
  return { eid := ← j.getObjValAs? Nat "eid", s := ← nodeOfJson (← j.getObjVal? "s"), p
           o := ← nodeOfJson (← j.getObjVal? "o"), txAdded := ← j.getObjValAs? Nat "txAdded"
           txRetracted := ← optField j "txRetracted", validFrom := ← optField j "validFrom"
           validTo := ← optField j "validTo" }

/-- Read JSON lines; blank lines are skipped, errors carry the line number. -/
def readRecords (src : String) : Except String (List Record) := do
  let lines := (src.splitOn "\n").zipIdx.filter fun (l, _) => !l.trimAscii.isEmpty
  lines.mapM fun (l, i) =>
    match Json.parse l >>= Record.ofJson with
    | .ok r => .ok r
    | .error e => .error s!"line {i + 1}: {e}"

private def nodeToJson : Node → Json
  | .term t => .str t.toNTriples
  | .eid e => Json.mkObj [("eid", (e : Json))]

/-- A record as one compact JSON line. -/
def Record.toJsonLine (r : Record) : String :=
  let opt {α : Type} [Lean.ToJson α] (k : String) (v : Option α) : List (String × Json) :=
    v.toList.map fun x => (k, Lean.toJson x)
  (Json.mkObj ([("eid", (r.eid : Json)), ("s", nodeToJson r.s), ("p", .str (Term.iri r.p).toNTriples),
    ("o", nodeToJson r.o), ("txAdded", (r.txAdded : Json))] ++ opt "txRetracted" r.txRetracted ++
    opt "validFrom" r.validFrom ++ opt "validTo" r.validTo)).compress

end LeanRDF.Statements
