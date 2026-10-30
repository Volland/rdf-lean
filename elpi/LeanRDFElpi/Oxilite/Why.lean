import LeanRDF
import Lean.Data.Json

/-!
# oxilite's `why` trees

oxilite's `why` tool (MCP, `crates/oxilite-cli/src/studio/why.rs`) explains a triple as a tree:
each node has a `triple` with RDF/JS terms and a `status` (`asserted`, `inferred` or `absent`);
an inferred node names the OWL 2 RL or RDFS template that derives it and its `premises`, or
carries a `note` when no template matched or the depth limit was reached.
-/

namespace LeanRDF.Oxilite

open Lean (Json)

/-- A node of a `why` tree. -/
inductive WhyNode where
  | mk (triple : Triple) (status : String) (rule : Option String) (premises : List WhyNode)
      (note : Option String)
  deriving Inhabited, Repr

namespace WhyNode

def triple : WhyNode → Triple | mk t .. => t
def status : WhyNode → String | mk _ s .. => s
def rule : WhyNode → Option String | mk _ _ r .. => r
def premises : WhyNode → List WhyNode | mk _ _ _ ps _ => ps
def note : WhyNode → Option String | mk _ _ _ _ n => n

end WhyNode

/-- An RDF/JS term (`termType` `NamedNode`, `BlankNode` or `Literal`). -/
def termOfRdfJs (j : Json) : Except String Term := do
  let tt ← j.getObjValAs? String "termType"
  let v ← j.getObjValAs? String "value"
  match tt with
  | "NamedNode" => return .iri ⟨v⟩
  | "BlankNode" => return .bnode ⟨v⟩
  | "Literal" =>
    let lang := (j.getObjValAs? String "language").toOption.getD ""
    if !lang.isEmpty then return .lit (Literal.lang' v lang)
    let dt ← (← j.getObjVal? "datatype").getObjValAs? String "value"
    match Literal.mk? v ⟨dt⟩ none with
    | some l => return .lit l
    | none => throw s!"literal \"{v}\" is rdf:langString without a language"
  | t => throw s!"unsupported term type '{t}'"

/-- Read a `why` tree from its JSON. -/
partial def WhyNode.ofJson (j : Json) : Except String WhyNode := do
  let tj ← j.getObjVal? "triple"
  let t : Triple := ⟨← termOfRdfJs (← tj.getObjVal? "s"), ← termOfRdfJs (← tj.getObjVal? "p"),
    ← termOfRdfJs (← tj.getObjVal? "o")⟩
  let status ← j.getObjValAs? String "status"
  let rule := (j.getObjValAs? String "rule").toOption
  let note := (j.getObjValAs? String "note").toOption
  let ps := ((j.getObjValAs? (Array Json) "premises").toOption.getD #[]).toList
  return .mk t status rule (← ps.mapM WhyNode.ofJson) note

/-- Read a `why` tree from a string. -/
def WhyNode.parse (s : String) : Except String WhyNode := do WhyNode.ofJson (← Json.parse s)

end LeanRDF.Oxilite
