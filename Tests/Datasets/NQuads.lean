import LeanRDF

/-! Scenarios of `datasets › N-Quads`. -/

namespace LeanRDF.Tests.NQuadsParse

private def ex (n : String) : Term := .iri ⟨"http://example.org/" ++ n⟩
private def T (s p o : Term) : Triple := ⟨s, p, o⟩

private def dataset (src : String) : Dataset := (NQuads.parse src).toOption.getD ∅

-- @tg: verifies:: [[openspec:datasets#N-Quads#Graph labels]] {level: unit}
#guard
  let d := dataset "<http://example.org/s> <http://example.org/p> <http://example.org/o> <http://example.org/g> .\n<http://example.org/s> <http://example.org/p> <http://example.org/o> .\n"
  d.size == 2 && (d.namedGraph (ex "g")).toList == [T (ex "s") (ex "p") (ex "o")] &&
    d.defaultGraph.toList == [T (ex "s") (ex "p") (ex "o")]

-- @tg: verifies:: [[openspec:datasets#N-Quads#Triple term in a named graph]] {level: unit}
#guard
  let line := "_:r <http://www.w3.org/1999/02/22-rdf-syntax-ns#reifies> <<( <http://example.org/a> <http://example.org/p> <http://example.org/b> )>> <http://example.org/g> .\n"
  let d := dataset line
  (d.namedGraph (ex "g")).toList ==
      [T (.bnode ⟨"r"⟩) (.iri Vocab.rdf.reifies) (.triple (ex "a") (ex "p") (ex "b"))] &&
    d.toNQuads.toOption == some line

-- @tg: verifies:: [[openspec:datasets#N-Quads#Triple term as graph label is rejected]] {level: unit}
#guard (NQuads.parse "<http://e/s> <http://e/p> <http://e/o> <<( <http://e/a> <http://e/p> <http://e/b> )>> .").toOption.isNone

-- A literal cannot name a graph, and N-Triples still rejects graph labels.
#guard (NQuads.parse "<http://e/s> <http://e/p> <http://e/o> \"g\" .").toOption.isNone
#guard (NTriples.parse "<http://e/s> <http://e/p> <http://e/o> <http://e/g> .").toOption.isNone

private def sample : Dataset := Dataset.ofList
  [⟨ex "s", ex "p", .lit (.lang "hi" "en"), none⟩,
   ⟨.bnode ⟨"b1"⟩, ex "p", .lit (Literal.str "a \"q\"\n"), some (ex "g")⟩,
   ⟨ex "s", ex "p", ex "o", some (.bnode ⟨"g2"⟩)⟩]

-- @tg: verifies:: [[openspec:datasets#N-Quads#Round trip]] {level: unit}
#guard match sample.toNQuads with
  | .ok src => (NQuads.parse src).toOption.map (·.toList) == some sample.toList
  | .error _ => false

end LeanRDF.Tests.NQuadsParse
