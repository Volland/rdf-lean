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

Version 2 adds an `envelope` object (`LeanRDF.Cert.Envelope`):

```json
"envelope": {"graph": "sha256:…", "query": "sha256:…",
             "rules": {"id": "rdfs", "digest": "sha256:…"}, "regime": "rdfs",
             "checker": "leanrdf-elpi 0.4.0", "toolchain": "leanprover/lean4:v4.35.0",
             "theorem": "checkQuery_sound"}
```

Reading accepts versions 1 and 2. Reading JSON is untrusted: a malformed certificate is an
error, a wrong one fails the checker, and a wrong envelope fails envelope verification.
-/

namespace LeanRDF.Cert

open Lean (Json)

private def tripleJson (t : Triple) : Json :=
  Json.arr #[Json.str t.s.toNTriples, Json.str t.p.toNTriples, Json.str t.o.toNTriples]

/-- A node as JSON. -/
def Node.toJson (n : Node) : Json :=
  Json.mkObj [("id", Lean.toJson n.id), ("conclusion", tripleJson n.conclusion),
    ("rule", Json.str n.rule), ("premises", Lean.toJson n.premises)]

/-- An envelope as JSON. -/
def Envelope.toJson (e : Envelope) : Json :=
  Json.mkObj [("graph", Json.str e.graph), ("query", Json.str e.query),
    ("rules", Json.mkObj [("id", Json.str e.rules.id), ("digest", Json.str e.rules.digest)]),
    ("regime", Json.str e.regime), ("checker", Json.str e.checker),
    ("toolchain", Json.str e.toolchain), ("theorem", Json.str e.thm)]

-- @tg: implements:: [[openspec:certificates#Certificate format]]
/-- A certificate as JSON: version 2 with its envelope when it has one, version 1 otherwise. -/
def Certificate.toJson (c : Certificate) : Json :=
  Json.mkObj <| [("version", Lean.toJson (if c.envelope.isSome || c.clash.isSome then 2 else 1)),
    ("mapping", Json.arr (c.mapping.toArray.map fun (b, t) =>
      Json.arr #[Json.str (Term.bnode b).toNTriples, Json.str t.toNTriples])),
    ("goals", Lean.toJson c.goals), ("nodes", Json.arr (c.nodes.toArray.map Node.toJson))]
    ++ (match c.envelope with | some e => [("envelope", e.toJson)] | none => [])
    ++ (match c.clash with
        | some k => [("clash", Json.mkObj [("rule", Json.str k.rule), ("premises", Lean.toJson k.premises)])]
        | none => [])

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

private def strField (j : Json) (k : String) : Except String String := do
  match j.getObjVal? k with
  | .ok v => v.getStr?
  | .error _ => throw s!"envelope: missing field {k}"

/-- Read an envelope from JSON; every field is required. -/
def Envelope.ofJson (j : Json) : Except String Envelope := do
  let rules ← match j.getObjVal? "rules" with
    | .ok r => pure r
    | .error _ => throw "envelope: missing field rules"
  return { graph := ← strField j "graph", query := ← strField j "query",
           rules := { id := ← strField rules "id", digest := ← strField rules "digest" },
           regime := ← strField j "regime", checker := ← strField j "checker",
           toolchain := ← strField j "toolchain", thm := ← strField j "theorem" }

/-- Read a certificate from JSON: version 1, or version 2 with its envelope. -/
def Certificate.ofJson (j : Json) : Except String Certificate := do
  let version ← (← j.getObjVal? "version").getNat?
  unless version == 1 || version == 2 do
    -- a number of many digits is not written out: that takes time quadratic in its length
    let shown := if version < 10 ^ 20 then toString version else s!"of {version.log2 + 1} bits"
    throw s!"unsupported certificate version {shown}"
  let envelope ← if version == 2 then
      match j.getObjVal? "envelope" with
      | .ok e => some <$> Envelope.ofJson e
      | .error _ => throw "a version-2 certificate needs an envelope"
    else pure none
  let clash ← match j.getObjVal? "clash" with
    | .error _ => pure none
    | .ok k =>
      if version != 2 then throw "only a version-2 certificate can carry a clash"
      pure (some { rule := ← (← k.getObjVal? "rule").getStr?,
                   premises := ← natsOf (← k.getObjVal? "premises") })
  let mapping ← match j.getObjVal? "mapping" with
    | .ok m => (← m.getArr?).toList.mapM mappingOf
    | .error _ => pure []
  return { version
           nodes := ← (← (← j.getObjVal? "nodes").getArr?).toList.mapM nodeOf
           goals := ← natsOf (← j.getObjVal? "goals")
           mapping, envelope, clash }

/-- Parse a certificate from JSON text. -/
def Certificate.parse (s : String) : Except String Certificate := do
  Certificate.ofJson (← Json.parse s)

end LeanRDF.Cert
