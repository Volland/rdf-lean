import LeanRDF

/-! Scenarios of `datasets › TriG`. -/

namespace LeanRDF.Tests.TriGParse

private def ex (n : String) : Term := .iri ⟨"http://example.org/" ++ n⟩
private def T (s p o : Term) : Triple := ⟨s, p, o⟩

private def quads? (src : String) : Option (List Quad) :=
  (Turtle.parseTriG src "http://example.org/").toOption.map (·.toList)

-- @tg: verifies:: [[openspec:datasets#TriG#Graph blocks]] {level: unit}
#guard quads? "{ <a> <p> <b> } GRAPH <g> { <c> <p> <d> } _:h { <e> <p> <f> }" ==
  some [⟨ex "a", ex "p", ex "b", none⟩, ⟨ex "c", ex "p", ex "d", some (ex "g")⟩,
        ⟨ex "e", ex "p", ex "f", some (.bnode ⟨"h"⟩)⟩]

-- Bare triples go to the default graph; `[]` can name a graph; the last '.' in a block is optional.
#guard quads? "<s> <p> <o> . [] { <a> <p> <b> . <a> <p> <c> }" ==
  some [⟨ex "s", ex "p", ex "o", none⟩, ⟨ex "a", ex "p", ex "b", some (.bnode ⟨"genid1"⟩)⟩,
        ⟨ex "a", ex "p", ex "c", some (.bnode ⟨"genid1"⟩)⟩]

-- @tg: verifies:: [[openspec:datasets#TriG#Directives only at the top level]] {level: unit}
#guard (TriG.parse "{ @prefix ex: <http://example.org/> . ex:a ex:p ex:b }" "http://example.org/").toOption.isNone

-- Turtle still has no graph blocks.
#guard (Turtle.parse "{ <a> <p> <b> }" "http://example.org/").toOption.isNone

end LeanRDF.Tests.TriGParse
