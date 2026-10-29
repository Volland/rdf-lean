import Lean.Data.Json
import LeanRDF.Cert.Check
import LeanRDF.Parse.NTriples.Parser
import LeanRDF.Parse.NTriples.Serializer

/-!
# Certificate JSON

Certificates as JSON, with every term written in N-Triples syntax (generalized: a literal may
be a subject), so a certificate is readable by itself and reuses the N-Triples parser:

```json
{"version": 1,
 "mapping": [["_:who", "<http://example.org/x>"]],
 "goals": [2],
 "nodes": [{"id": 0, "conclusion": ["<a>", "<p>", "<b>"], "rule": "fact", "premises": []}]}
```

Reading JSON is untrusted: a malformed certificate is an error, a wrong one fails the checker.
-/

namespace LeanRDF.Cert

open Lean (Json)

private def tripleJson (t : Triple) : Json :=
  Json.arr #[Json.str t.s.toNTriples, Json.str t.p.toNTriples, Json.str t.o.toNTriples]

/-- A node as JSON. -/
def Node.toJson (n : Node) : Json :=
  Json.mkObj [("id", Lean.toJson n.id), ("conclusion", tripleJson n.conclusion),
    ("rule", Json.str n.rule), ("premises", Lean.toJson n.premises)]

-- @tg: implements:: [[openspec:certificates#Certificate format]]
/-- A certificate as JSON. -/
def Certificate.toJson (c : Certificate) : Json :=
  Json.mkObj [("version", Lean.toJson c.version),
    ("mapping", Json.arr (c.mapping.toArray.map fun (b, t) =>
      Json.arr #[Json.str (Term.bnode b).toNTriples, Json.str t.toNTriples])),
    ("goals", Lean.toJson c.goals), ("nodes", Json.arr (c.nodes.toArray.map Node.toJson))]

/-- A certificate as indented JSON text. -/
def Certificate.render (c : Certificate) : String := c.toJson.pretty

private def termOf (j : Json) : Except String Term := do
  (NTriples.parseTerm (← j.getStr?)).mapError toString

private def tripleOf (j : Json) : Except String Triple := do
  match (← j.getArr?).toList with
  | [s, p, o] => return ⟨← termOf s, ← termOf p, ← termOf o⟩
  | _ => throw "a triple must have three terms"

private def natsOf (j : Json) : Except String (List Nat) := do
  (← j.getArr?).toList.mapM Json.getNat?

private def nodeOf (j : Json) : Except String Node := do
  return { id := ← (← j.getObjVal? "id").getNat?
           conclusion := ← tripleOf (← j.getObjVal? "conclusion")
           rule := ← (← j.getObjVal? "rule").getStr?
           premises := ← natsOf (← j.getObjVal? "premises") }

private def mappingOf (j : Json) : Except String (BlankNode × Term) := do
  match (← j.getArr?).toList with
  | [b, t] =>
    match ← termOf b with
    | .bnode bn => return (bn, ← termOf t)
    | _ => throw "a mapping must start with a blank node"
  | _ => throw "a mapping entry must have two terms"

/-- Read a certificate from JSON. -/
def Certificate.ofJson (j : Json) : Except String Certificate := do
  let version ← (← j.getObjVal? "version").getNat?
  unless version == 1 do throw s!"unsupported certificate version {version}"
  let mapping ← match j.getObjVal? "mapping" with
    | .ok m => (← m.getArr?).toList.mapM mappingOf
    | .error _ => pure []
  return { version
           nodes := ← (← (← j.getObjVal? "nodes").getArr?).toList.mapM nodeOf
           goals := ← natsOf (← j.getObjVal? "goals")
           mapping }

/-- Parse a certificate from JSON text. -/
def Certificate.parse (s : String) : Except String Certificate := do
  Certificate.ofJson (← Json.parse s)

end LeanRDF.Cert
