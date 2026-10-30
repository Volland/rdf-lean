import LeanRDFShacl
import Lean.Data.Json

/-! The comparison with oxilite: the SHACL results that `oxilite check --json` recorded for the
samples in `ShaclTests/data/oxilite/` (`scripts/shacl-oxilite-fixtures.sh`, reasoning off) and
LeanRDF's reports agree on focus node, path and constraint component, result for result. -/

namespace LeanRDF.Shacl.Tests.Oxilite

open LeanRDF Shacl Lean

/-- The constraint component an oxilite (rudof) message names, as the local name without
`ConstraintComponent`. -/
def componentOfMessage (m : String) : Option String :=
  if m.startsWith sh.ns then some ((m.drop sh.ns.length).toString.replace "ConstraintComponent" "")
  else
    let table := [("Expected Datatype", "Datatype"), ("MaxInclusive(", "MaxInclusive"),
      ("MinInclusive(", "MinInclusive"), ("MaxExclusive(", "MaxExclusive"),
      ("MinExclusive(", "MinExclusive"), ("MinCount(", "MinCount"), ("MaxCount(", "MaxCount"),
      ("MinLength(", "MinLength"), ("MaxLength(", "MaxLength"), ("In constraint", "In"),
      ("Pattern(", "Pattern"), ("Unique lang", "UniqueLang"), ("OR not satisfied", "Or"),
      ("LanguageIn constraint", "LanguageIn"), ("NodeKind", "NodeKind"), ("Class", "Class")]
    (table.find? fun (pfx, _) => m.startsWith pfx).map (·.2)

/-- oxilite's violations as `focus path component` keys. -/
def oxiliteKeys (j : Json) : Except String (List String) := do
  let vs ← j.getObjValAs? (Array Json) "violations"
  vs.toList.mapM fun v => do
    let focus ← v.getObjValAs? String "focus"
    let path := (v.getObjValAs? String "path").toOption.getD ""
    let msg ← v.getObjValAs? String "message"
    let some c := componentOfMessage msg | throw s!"unknown oxilite message: {msg}"
    return s!"{focus} {path} {c}"

/-- LeanRDF's results as the same keys. -/
def leanKeys (rep : Report) : List String :=
  rep.results.map fun r =>
    let focus := match r.focus with
      | .iri i => i.val
      | t => t.toNTriples
    let path := match r.path with
      | some (.pred p) => p.val
      | _ => ""
    s!"{focus} {path} {(r.component.val.drop sh.ns.length).toString.replace "ConstraintComponent" ""}"

/-- Compare one sample: `none` when they agree. -/
def compare (dir : System.FilePath) : IO (Option String) := do
  let G ← IO.ofExcept (← loadGraph (dir / "data.ttl"))
  let SG ← IO.ofExcept (← loadGraph (dir / "shapes.ttl"))
  let shapes ← IO.ofExcept (readShapes (renameShapes SG))
  let rep := validate G shapes
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile (dir / "oxilite.json")))
  let ox ← IO.ofExcept (oxiliteKeys j)
  let sort (l : List String) := l.mergeSort (· ≤ ·)
  if sort ox == sort (leanKeys rep) then return none
  return some s!"{dir}: oxilite {sort ox}\nLeanRDF {sort (leanKeys rep)}"

-- @tg: verifies:: [[openspec:shacl-core#SHACL command line and oxilite comparison#Agreement with oxilite]] {level: integration}
#eval show IO Unit from do
  for s in ["people", "products"] do
    if let some d ← compare ("ShaclTests/data/oxilite" / s) then throw (IO.userError d)

end LeanRDF.Shacl.Tests.Oxilite
