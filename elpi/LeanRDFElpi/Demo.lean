import LeanRDFElpi.Certify
import LeanRDFElpi.Countermodel
import LeanRDFOwl

/-!
# The demo

`lake exe leanrdf-demo DATA.nt QUERY.nt [--profile rdfs|owl] [--cert OUT.json] [--datalog OUT.json]
[--countermodel OUT.json] [--total-fuel STEPS]`:
saturate the data in Elpi, look for a clash, certify the query, check the certificate with the
verified checker and report. "Entailed" is printed only after the checker accepts; a failed
search is reported as "not derived", never as "not entailed", because completeness is not
proven.

A clash comes first: when the data has a checked clash certificate it has no model, every query
follows from it, and the demo reports INCONSISTENT instead of any entailment.

When no instance is derived under the RDFS profile, the demo builds a candidate countermodel
from the closure. REFUTED is printed only when the verified model checker accepts it; otherwise
the verdict stays NOT DERIVED, with the condition the candidate failed.

Exit codes: `0` entailed and checked, `1` not derived (also when the search stops at its step
budget, which is reported as such), `2` certificate rejected or search failed (a bug on the
untrusted side), `3` usage, input or parse error, `4` inconsistent, `5` refuted.
-/

namespace LeanRDF.Demo

open Cert Bridge

/-- The rules the demo reasons with. -/
inductive Profile
  | rdfs
  | owl
  deriving BEq, Repr

def Profile.name : Profile → String | .rdfs => "rdfs" | .owl => "owl"

def Profile.rules : Profile → List Rule
  | .rdfs => RDFS.rdfsRules
  | .owl => Owl.owlRules

def Profile.clashRules : Profile → List ClashRule
  | .rdfs => rdfsClashRules
  | .owl => Owl.owlClashRules

/-- The theorem an accepted query certificate stands for. -/
def Profile.theorem : Profile → String
  | .rdfs => "checkQuery_sound"
  | .owl => "Derives.owl_sound_graph"

/-- The theorem an accepted clash certificate stands for. -/
def Profile.clashTheorem : Profile → String
  | .rdfs => "checkClash_sound_rdfs"
  | .owl => "checkClash_sound_owl"

/-- Command-line arguments. -/
structure Args where
  data : System.FilePath
  query : System.FilePath
  profile : Profile := .rdfs
  certOut : Option System.FilePath := none
  datalogOut : Option System.FilePath := none
  countermodelOut : Option System.FilePath := none
  /-- The Elpi step budget of the saturation. -/
  totalFuel : Nat := defaultTotalFuel

-- @tg: implements:: [[openspec:demo#Example ontology]]
/-- The example ontology and its queries, in `elpi/examples/`. -/
def examples : List String :=
  ["pets.nt", "query-mammal-owner.nt", "query-tom-animal.nt", "query-tom-dog.nt"]

/-- The usage line. -/
def usage : String :=
  "usage: leanrdf-demo DATA.nt QUERY.nt [--profile rdfs|owl] [--cert OUT.json] [--datalog OUT.json] [--countermodel OUT.json] [--total-fuel STEPS]"

/-- Read the arguments. -/
def parseArgs : List String → Option Args
  | data :: query :: rest => go { data, query } rest
  | _ => none
where
  go (a : Args) : List String → Option Args
    | [] => some a
    | "--cert" :: p :: rest => go { a with certOut := some p } rest
    | "--datalog" :: p :: rest => go { a with datalogOut := some p } rest
    | "--countermodel" :: p :: rest => go { a with countermodelOut := some p } rest
    | "--profile" :: "rdfs" :: rest => go { a with profile := .rdfs } rest
    | "--profile" :: "owl" :: rest => go { a with profile := .owl } rest
    | "--total-fuel" :: n :: rest => n.toNat?.bind fun k => go { a with totalFuel := k } rest
    | _ => none

private def nodeLine (n : Node) : String :=
  let premises := if n.premises.isEmpty then "" else s!" {n.premises}"
  s!"  [{n.id}] {n.conclusion.s.toNTriples} {n.conclusion.p.toNTriples} {n.conclusion.o.toNTriples}  ({n.rule}{premises})"

private def readGraph (what : String) (path : System.FilePath) : ExceptT (UInt32 × String) IO Graph := do
  let src ← match ← (IO.FS.readFile path).toBaseIO with
    | .ok src => pure src
    | .error e => throw (3, s!"cannot read {what} {path}: {e}")
  match NTriples.parse src with
  | .ok g => return g
  | .error e => throw (3, s!"{what} {path}:{e}")

-- @tg: implements:: [[openspec:demo#Exit codes and verdicts]]
/-- The verdict of the verified checker on a certificate: exit code `0` if it accepts, `2` with
the reason if it rejects. -/
def verdict (g q : Graph) (c : Certificate) (rules : List Rule := RDFS.rdfsRules) : UInt32 × String :=
  match checkQuery rules g q c with
  | .ok () => (0, "")
  | .error e => (2, s!"Verdict: CERTIFICATE REJECTED: {e}")

/-- Bind a certificate to its data, query and rules (version 2). -/
private def bind (g q : Graph) (a : Args) (thm : String) (c : Certificate) :
    ExceptT (UInt32 × String) IO Certificate := do
  match Envelope.build g q a.profile.name a.profile.rules a.profile.name thm ("leanrdf-elpi " ++ release) with
  | .ok e => return { c with version := 2, envelope := some e }
  | .error e => throw (3, s!"cannot digest the input: {e}")

-- @tg: implements:: [[openspec:inconsistency#Inconsistent verdict]]
/-- Look for a clash in the closure. `some` is the report of a checked clash (exit 4) or of a
rejected clash certificate (exit 2); `none` means no clash was found, which is no claim of
consistency. -/
def clashVerdict (g : Graph) (a : Args) (closure : Closure) (out : String) :
    ExceptT (UInt32 × String) IO (Option (UInt32 × String)) := do
  let cert ← match clashCertificate closure a.profile.clashRules with
    | .ok none => return none
    | .ok (some c) => pure c
    | .error e => throw (2, out ++ s!"clash search failed: {e}")
  match checkClash a.profile.rules a.profile.clashRules g cert with
  | .error e => return some (2, out ++ s!"Verdict: CLASH CERTIFICATE REJECTED: {e}")
  | .ok () =>
    let mut out := out
    let some k := cert.clash | return none
    out := out ++ s!"Clash: {k.rule} on nodes {k.premises}\n"
    out := out ++ s!"Certificate: {cert.nodes.length} nodes\n"
    out := out ++ "\n".intercalate (cert.nodes.map nodeLine) ++ "\n"
    if let some p := a.certOut then
      let c2 ← bind g (Graph.ofList []) a a.profile.clashTheorem cert
      IO.FS.writeFile p c2.render
      out := out ++ s!"Clash certificate written to {p}\n"
    let model := if a.profile == .owl then "OWL model" else "RDFS model with well-typed strings"
    out := out ++ s!"Verdict: INCONSISTENT. The verified checker accepted the clash: by {a.profile.clashTheorem}, the data has no {model}, so every query follows from it. No entailment is reported."
    return some (4, out)

/-- No instance is derived: try a countermodel (RDFS profile only). REFUTED (exit 5) when the
verified model checker accepts it, NOT DERIVED (exit 1) with the failed condition otherwise. -/
def refuteOrNotDerived (g q : Graph) (a : Args) (e : Engine) (closure : Closure) (out why : String) :
    IO (UInt32 × String) := do
  let notDerived (reason : String) : UInt32 × String :=
    (1, out ++ s!"Verdict: NOT DERIVED ({why}).\n{reason}\nThis is not a claim of non-entailment: completeness is not proven.")
  if a.profile != .rdfs then
    return notDerived "No countermodel was tried: countermodels are for simple, RDF and RDFS entailment."
  -- the closure of the data under the RDFS rules continues with the representatives
  match findCountermodelFrom e closure q with
  | .error e => return notDerived s!"The countermodel finder failed: {e}"
  | .ok P =>
    match Model.checkCountermodel .rdfs g q P with
    | .error e => return notDerived s!"The candidate countermodel was rejected: {e}"
    | .ok () =>
      let mut out := out ++ s!"No instance is derived. Countermodel: {P.n} sorts, {P.ext.length} IEXT entries.\n"
      if let some p := a.countermodelOut then
        match Envelope.build g q "rdfs" RDFS.rdfsRules "rdfs" Model.CRegime.rdfs.theoremName
            ("leanrdf-elpi " ++ release) with
        | .ok e =>
          IO.FS.writeFile p ({ regime := .rdfs, model := P, envelope := some e } : Model.Countermodel).render
          out := out ++ s!"Countermodel written to {p}\n"
        | .error e => return (3, out ++ s!"cannot digest the input: {e}")
      return (5, out ++ "Verdict: REFUTED. The verified model checker accepted the countermodel under RDFS, with D = {xsd:string, rdf:langString, rdf:dirLangString}: by checkCountermodel_sound_rdfs, the data does not RDFS-entail the query.")

-- @tg: implements:: [[openspec:demo#Demo command]]
-- @tg: implements:: [[openspec:demo#Exit codes and verdicts]] {since: "0.5.0"}
/-- Run the demo: the exit code and the report. Files are written only on success. -/
def run (a : Args) : IO (UInt32 × String) := do
  let r ← (do
    let g ← readGraph "data" a.data
    let q ← readGraph "query" a.query
    let rules := a.profile.rules
    let mut out := s!"LeanRDF: {g.size} data triples, {q.size} query triples\n"
    let engine ← match program rules with
      | .ok e => pure e
      | .error e => throw (2, out ++ s!"search failed: {e}")
    let closure ← match saturateWith engine g (totalFuel := a.totalFuel) with
      | .ok c => pure c
      | .error e =>
        if isBudgetExhausted e then
          throw (1, out ++ s!"{e}.\nVerdict: NOT DERIVED (the search stopped at its budget). This is not a claim of non-entailment: completeness is not proven.")
        else throw (2, out ++ s!"search failed: {e}")
    let implicit := if closure.mode == .implicit then
      " (the rdfs5 and rdfs11 pairs are left implicit and derived for the query)" else ""
    out := out ++ s!"Elpi closure under {rules.length} rules: {closure.size} triples{implicit}\n"
    if let some (code, report) ← clashVerdict g a closure out then throw (code, report)
    let cert ← match certify closure q with
      | .ok c => pure c
      | .error e =>
        if isBudgetExhausted e then
          throw (1, out ++ s!"{e}.\nVerdict: NOT DERIVED (the search stopped at its budget). This is not a claim of non-entailment: completeness is not proven.")
        throw (← refuteOrNotDerived g q a engine closure out e)
    let (code, why) := verdict g q cert rules
    if code != 0 then throw (code, out ++ why)
    for (b, t) in cert.mapping do
      out := out ++ s!"Query instance: {(Term.bnode b).toNTriples} ↦ {t.toNTriples}\n"
    out := out ++ s!"Certificate: {cert.nodes.length} nodes, goals {cert.goals}\n"
    out := out ++ "\n".intercalate (cert.nodes.map nodeLine) ++ "\n"
    if let some p := a.certOut then
      -- A version-2 certificate: the envelope binds it to this data, query and rule set.
      let c2 ← bind g q a a.profile.theorem cert
      IO.FS.writeFile p c2.render
      out := out ++ s!"Certificate written to {p} (version 2, data digest {c2.envelope.map (·.graph) |>.getD ""})\n"
    if let some p := a.datalogOut then
      IO.FS.writeFile p (toDatalog rules g cert).pretty
      out := out ++ s!"CertifyingDatalog problem written to {p}\n"
    out := out ++ "Verdict: ENTAILED. The certificate was accepted by the verified checker (compiled)."
    return out : ExceptT (UInt32 × String) IO String).run
  return match r with
    | .ok out => (0, out)
    | .error (code, out) => (code, out)

end LeanRDF.Demo
