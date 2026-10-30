import LeanRDF.Core.Dataset
import LeanRDF.Parse.NTriples.Serializer

/-!
# Canonical N-Quads serializer

Writes datasets as N-Quads (RDF 1.1 N-Quads §5): one quad per line in `Dataset.toList` order,
terms in canonical N-Triples form, the graph label after the object for named graphs.
-/

namespace LeanRDF

open NTriples

/-- One quad as an N-Quads line, or why it cannot be written. -/
def Quad.toNQuads (q : Quad) : Except String String := do
  let line ← q.triple.toNTriples
  match q.g with
  | none => return line
  | some g =>
    match g with
    | .iri _ | .bnode _ =>
      -- The label is writable exactly when it is writable as the subject of a triple.
      discard <| (Triple.mk g (.iri ⟨"urn:x"⟩) g).toNTriples
      return s!"{q.s.toNTriples} {q.p.toNTriples} {q.o.toNTriples} {g.toNTriples} .\n"
    | .lit _ => throw s!"a literal cannot name a graph: {g.toNTriples}"

-- @tg: implements:: [[openspec:datasets#N-Quads]]
/-- A dataset as an N-Quads document, quads in `Dataset.toList` order. Fails on a quad that is
not well-formed or would not re-parse. -/
def Dataset.toNQuads (d : Dataset) : Except String String :=
  d.toList.foldlM (fun acc q => return acc ++ (← q.toNQuads)) ""

end LeanRDF
