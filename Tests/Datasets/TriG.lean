import Tests.Turtle.Iso

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

-- @tg: verifies:: [[openspec:datasets#TriG#Reification inside a graph block]] {level: unit}
#guard match TriG.parse "PREFIX : <http://example.org/>\nGRAPH :g { :a :b :c ~ :r {| :q :d |} . << :e :f :h >> :p :o }" "http://example.org/" with
  | .ok d =>
    let reifies : Term := .iri Vocab.rdf.reifies
    d.defaultGraph.size == 0 && d.size == 5 &&
      Tests.Iso.isomorphic (d.namedGraph (ex "g")) (Graph.ofList
        [T (ex "a") (ex "b") (ex "c"), T (ex "r") reifies (.triple (ex "a") (ex "b") (ex "c")),
         T (ex "r") (ex "q") (ex "d"), T (.bnode ⟨"x"⟩) reifies (.triple (ex "e") (ex "f") (ex "h")),
         T (.bnode ⟨"x"⟩) (ex "p") (ex "o")])
  | .error _ => false

-- @tg: verifies:: [[openspec:datasets#TriG#Version directive only at the top level]] {level: unit}
#guard (TriG.parse "VERSION \"1.2\"\nGRAPH <g> { <a> <p> <b> }" "http://example.org/").toOption.isSome &&
  (TriG.parse "GRAPH <g> { VERSION \"1.2\" <a> <p> <b> }" "http://example.org/").toOption.isNone

-- Turtle still has no graph blocks.
#guard (Turtle.parse "{ <a> <p> <b> }" "http://example.org/").toOption.isNone

end LeanRDF.Tests.TriGParse
