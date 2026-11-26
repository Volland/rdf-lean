import Lean.Data.Json
import LeanRDFCheck.Regime

/-!
# Verdicts

One verdict vocabulary for every LeanRDF tool, with fixed exit codes. `leanrdf-check` produces
`proven`, `rejected` and `inputError`; `unknown`, `inconsistent` and `refuted` belong to tools
that search (`add-inconsistency-certificates`, `add-countermodels`), and are fixed here so that
no later change renames a verdict.
-/

namespace LeanRDF.Check

open Lean (Json)

/-- A verdict. -/
inductive Verdict where
  | proven | unknown | rejected | inputError | inconsistent | refuted
  deriving Repr, DecidableEq, Inhabited

namespace Verdict

/-- The exit code: `0` proven, `1` unknown (not derived), `2` certificate rejected, `3` input
error, `4` inconsistent, `5` refuted. -/
def exitCode : Verdict → UInt32
  | .proven => 0 | .unknown => 1 | .rejected => 2 | .inputError => 3
  | .inconsistent => 4 | .refuted => 5

/-- The name in JSON verdicts. -/
def name : Verdict → String
  | .proven => "proven" | .unknown => "unknown" | .rejected => "rejected"
  | .inputError => "input-error" | .inconsistent => "inconsistent" | .refuted => "refuted"

end Verdict

/-! ## Echoing untrusted values

A report repeats values read from the certificate (goal numbers, the reason of a rejection, which
may quote a term). They are bounded, so that a hostile certificate cannot make the output as
large as itself: every word longer than `maxWord` characters is cut, and at most `maxGoals`
goals are listed. The command line clips the reasons that come from a certificate or a
countermodel (`LeanRDF.Check.Cli`); paths and messages of its own are not clipped. -/

/-- The longest word of untrusted text a report repeats in full. -/
def maxWord : Nat := 200

/-- The most goals a report lists. -/
def maxGoals : Nat := 100

/-- A word cut to `maxWord` characters, with the number of characters left out. -/
def clipWord (w : String) : String :=
  if w.length ≤ maxWord then w
  else String.ofList (w.toList.take maxWord) ++ s!"…({w.length - maxWord} more characters)"

/-- Untrusted text with every overlong word cut (`clipWord`). -/
def clip (s : String) : String :=
  if s.length ≤ maxWord then s else " ".intercalate ((s.splitOn " ").map clipWord)

/-- A number as it is repeated: in full below `10 ^ maxWord`, otherwise its size only, since
writing a number in decimal takes time quadratic in its length. -/
def numberText (n : Nat) : String :=
  if n < 10 ^ maxWord then toString n else s!"…(a {n.log2 + 1}-bit number)"

/-- The goals of a certificate as text, bounded. -/
def goalsText (goals : List Nat) : String :=
  let shown := goals.take maxGoals |>.map numberText
  let more := if goals.length > maxGoals then s!", …({goals.length - maxGoals} more)" else ""
  "[" ++ ", ".intercalate shown ++ more ++ "]"

/-- The goals of a certificate as JSON: numbers, except that a number too long to repeat is a
string giving its size (`numberText`), and at most `maxGoals` of them. -/
def goalsJson (goals : List Nat) : Json :=
  Json.arr (goals.take maxGoals |>.map (fun g =>
    if g < 10 ^ maxWord then Lean.toJson g else Json.str (numberText g))).toArray

/-- What a check reports, as text or JSON. -/
structure Report where
  verdict : Verdict
  regime : Option Regime := none
  dataTriples : Option Nat := none
  queryTriples : Option Nat := none
  nodes : Option Nat := none
  goals : List Nat := []
  mapping : List (BlankNode × Term) := []
  reason : Option String := none
  /-- The digests of the data and the query that were read. -/
  graphDigest : Option String := none
  queryDigest : Option String := none
  /-- `true` when the envelope was verified, `false` for a version-1 certificate (no envelope),
  absent when the envelope did not match. -/
  bound : Option Bool := none
  /-- Where `--emit-envelope` wrote the version-2 certificate. -/
  emitted : Option String := none
  /-- The clash rule of a clash certificate. -/
  clash : Option String := none
  /-- For a countermodel: the number of sorts and the theorem of its regime. -/
  sorts : Option Nat := none
  deriving Inhabited

-- @tg: implements:: [[openspec:certificate-check#JSON verdict]]
/-- The report as one JSON object. -/
def Report.toJson (r : Report) : Json :=
  let opt (k : String) (v : Option Json) : List (String × Json) :=
    match v with | some j => [(k, j)] | none => []
  Json.mkObj <|
    [("verdict", Json.str r.verdict.name), ("exit", Lean.toJson r.verdict.exitCode.toNat)]
    ++ opt "regime" (r.regime.map (Json.str ·.name))
    ++ opt "theorem" (match r.verdict with
        | .proven => r.regime.map (Json.str ·.theoremName)
        | .inconsistent => r.regime.map (Json.str ·.clashTheoremName)
        | .refuted => (r.regime.bind (·.countermodel?)).map (Json.str ·.theoremName)
        | _ => none)
    ++ (if r.verdict == .refuted then [("datatypes", Json.str datatypesNote)] else [])
    ++ opt "sorts" (r.sorts.map Lean.toJson)
    ++ opt "clash" (r.clash.map Json.str)
    ++ opt "dataTriples" (r.dataTriples.map Lean.toJson)
    ++ opt "queryTriples" (r.queryTriples.map Lean.toJson)
    ++ opt "nodes" (r.nodes.map Lean.toJson)
    ++ (if r.nodes.isSome then [("goals", goalsJson r.goals)] else [])
    ++ (if r.mapping.isEmpty then [] else
        [("mapping", Json.mkObj (r.mapping.map fun (b, t) =>
          ((Term.bnode b).toNTriples, Json.str t.toNTriples)))])
    ++ opt "graph" (r.graphDigest.map Json.str)
    ++ opt "query" (r.queryDigest.map Json.str)
    ++ opt "bound" (r.bound.map Json.bool)
    ++ opt "emitted" (r.emitted.map Json.str)
    ++ opt "reason" (r.reason.map Json.str)

/-- The report as text. -/
def Report.toText (r : Report) : String := Id.run do
  let mut out := ""
  match r.dataTriples, r.queryTriples, r.clash with
  | some d, some q, _ =>
    out := out ++ s!"LeanRDF check: {d} data triples, {q} query triples\n"
  | some d, none, some _ => out := out ++ s!"LeanRDF check: {d} data triples, a clash certificate\n"
  | _, _, _ => pure ()
  if let some n := r.sorts then out := out ++ s!"Countermodel: {n} sorts\n"
  if let some n := r.nodes then
    out := out ++ (if r.clash.isSome then s!"Certificate: {n} nodes\n"
      else s!"Certificate: {n} nodes, goals {goalsText r.goals}\n")
  if let some d := r.graphDigest then out := out ++ s!"Data digest: {d}\n"
  if let some d := r.queryDigest then out := out ++ s!"Query digest: {d}\n"
  match r.bound with
  | some true => out := out ++ "Envelope: verified (data, query, rules and regime match)\n"
  | some false => out := out ++ "Envelope: none; a version-1 certificate is unbound to its data\n"
  | none => pure ()
  for (b, t) in r.mapping do
    out := out ++ s!"Query instance: {(Term.bnode b).toNTriples} ↦ {t.toNTriples}\n"
  if let some p := r.emitted then out := out ++ s!"Wrote the version-2 certificate to {p}\n"
  match r.verdict, r.regime with
  | .proven, some rg =>
    out := out ++ s!"Verdict: PROVEN. The verified checker accepted the certificate under {rg.name}: by {rg.theoremName}, the data {rg.entailsName} the query."
  | .inconsistent, some rg =>
    out := out ++ s!"Clash: {r.clash.getD ""}\n"
    let model := if rg == .rdfs then "RDFS model with well-typed strings" else "OWL model"
    out := out ++ s!"Verdict: INCONSISTENT. The verified checker accepted the clash certificate under {rg.name}: by {rg.clashTheoremName}, the data has no {model}, so every query follows from it."
  | .refuted, some rg =>
    let thm := (rg.countermodel?.map (·.theoremName)).getD ""
    out := out ++ s!"Verdict: REFUTED. The verified model checker accepted the countermodel under {rg.name}, with {datatypesNote}: by {thm}, the data does not entail the query: ¬ {rg.entailsName}."
  | .rejected, _ =>
    let what := if r.sorts.isSome then "COUNTERMODEL" else "CERTIFICATE"
    out := out ++ s!"Verdict: {what} REJECTED: {r.reason.getD ""}"
  | _, _ =>
    out := out ++ (r.reason.getD r.verdict.name)
  return out

end LeanRDF.Check
