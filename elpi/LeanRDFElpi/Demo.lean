import LeanRDFElpi.Certify

/-!
# The demo

`lake exe leanrdf-demo DATA.nt QUERY.nt [--cert OUT.json] [--datalog OUT.json]`: saturate the
data in Elpi, certify the query, check the certificate with the verified checker and report.
"Entailed" is printed only after the checker accepts; a failed search is reported as "not
derived", never as "not entailed", because completeness is not proven.

Exit codes: `0` entailed and checked, `1` not derived, `2` certificate rejected or search failed
(a bug on the untrusted side), `3` usage, input or parse error.
-/

namespace LeanRDF.Demo

open Cert Bridge

/-- Command-line arguments. -/
structure Args where
  data : System.FilePath
  query : System.FilePath
  certOut : Option System.FilePath := none
  datalogOut : Option System.FilePath := none

-- @tg: implements:: [[openspec:demo#Example ontology]]
/-- The example ontology and its queries, in `elpi/examples/`. -/
def examples : List String :=
  ["pets.nt", "query-mammal-owner.nt", "query-tom-animal.nt", "query-tom-dog.nt"]

/-- The usage line. -/
def usage : String :=
  "usage: leanrdf-demo DATA.nt QUERY.nt [--cert OUT.json] [--datalog OUT.json]"

/-- Read the arguments. -/
def parseArgs : List String → Option Args
  | data :: query :: rest => go { data, query } rest
  | _ => none
where
  go (a : Args) : List String → Option Args
    | [] => some a
    | "--cert" :: p :: rest => go { a with certOut := some p } rest
    | "--datalog" :: p :: rest => go { a with datalogOut := some p } rest
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
def verdict (g q : Graph) (c : Certificate) : UInt32 × String :=
  match checkQuery RDFS.rdfsRules g q c with
  | .ok () => (0, "")
  | .error e => (2, s!"Verdict: CERTIFICATE REJECTED: {e}")

-- @tg: implements:: [[openspec:demo#Demo command]]
/-- Run the demo: the exit code and the report. Files are written only on success. -/
def run (a : Args) : IO (UInt32 × String) := do
  let r ← (do
    let g ← readGraph "data" a.data
    let q ← readGraph "query" a.query
    let mut out := s!"LeanRDF: {g.size} data triples, {q.size} query triples\n"
    let closure ← match saturate RDFS.rdfsRules g with
      | .ok c => pure c
      | .error e => throw (2, out ++ s!"search failed: {e}")
    out := out ++ s!"Elpi closure under {RDFS.rdfsRules.length} rules: {closure.size} triples\n"
    let cert ← match certify closure q with
      | .ok c => pure c
      | .error e =>
        throw (1, out ++ s!"Verdict: NOT DERIVED ({e}).\nThis is not a claim of non-entailment: completeness is not proven.")
    let (code, why) := verdict g q cert
    if code != 0 then throw (code, out ++ why)
    for (b, t) in cert.mapping do
      out := out ++ s!"Query instance: {(Term.bnode b).toNTriples} ↦ {t.toNTriples}\n"
    out := out ++ s!"Certificate: {cert.nodes.length} nodes, goals {cert.goals}\n"
    out := out ++ "\n".intercalate (cert.nodes.map nodeLine) ++ "\n"
    if let some p := a.certOut then
      IO.FS.writeFile p cert.render
      out := out ++ s!"Certificate written to {p}\n"
    if let some p := a.datalogOut then
      IO.FS.writeFile p (toDatalog RDFS.rdfsRules g cert).pretty
      out := out ++ s!"CertifyingDatalog problem written to {p}\n"
    out := out ++ "Verdict: ENTAILED. The certificate was accepted by the verified checker (compiled)."
    return out : ExceptT (UInt32 × String) IO String).run
  return match r with
    | .ok out => (0, out)
    | .error (code, out) => (code, out)

end LeanRDF.Demo
