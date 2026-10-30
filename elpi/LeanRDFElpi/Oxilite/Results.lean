import LeanRDF
import Lean.Data.Json

/-!
# SPARQL results from oxilite

Read SPARQL 1.1 Query Results JSON (W3C Recommendation, 2013), the format of
`oxilite query --results-format json`, into solution mappings. Terms are built with the Core
smart constructors. Untrusted: a misread answer can only fail certification.
-/

namespace LeanRDF.Oxilite

open Lean (Json)

/-- A solution: the bound variables and their terms. -/
abbrev Solution := List (String × Term)

/-- A results document: the variables of the head and the solutions. -/
structure Results where
  vars : List String
  solutions : List Solution
  deriving Inhabited

/-- One RDF term binding (`uri`, `bnode`, `literal` with `xml:lang` or `datatype`, or the older
`typed-literal`). -/
def termOfBinding (j : Json) : Except String Term := do
  let ty ← j.getObjValAs? String "type"
  let v ← j.getObjValAs? String "value"
  match ty with
  | "uri" => return .iri ⟨v⟩
  | "bnode" => return .bnode ⟨v⟩
  | "literal" | "typed-literal" =>
    match j.getObjValAs? String "xml:lang" with
    | .ok tag => return .lit (Literal.lang' v tag)
    | .error _ =>
      match j.getObjValAs? String "datatype" with
      | .ok dt =>
        match Literal.mk? v ⟨dt⟩ none with
        | some l => return .lit l
        | none => throw s!"literal \"{v}\" has datatype rdf:langString but no language"
      | .error _ => return .lit (Literal.str v)
  | t => throw s!"unknown binding type '{t}'"

-- @tg: implements:: [[openspec:oxilite-bridge#Results reading]]
/-- Parse a SPARQL 1.1 Query Results JSON document. -/
def parseResults (s : String) : Except String Results := do
  let j ← Json.parse s
  let vars ← (← j.getObjVal? "head").getObjValAs? (Array String) "vars"
  let bindings ← (← j.getObjVal? "results").getObjValAs? (Array Json) "bindings"
  let solutions ← bindings.toList.mapM fun b => do
    let obj ← b.getObj?
    obj.toList.mapM fun (k, v) => return (k, ← termOfBinding v)
  return { vars := vars.toList, solutions }

end LeanRDF.Oxilite
