import LeanRDF.Parse.NTriples.Parser

/-!
# N-Quads parser

RDF 1.1 N-Quads §5: N-Triples statements with an optional graph label. The statement parser is
shared with N-Triples (`NTriples.parseQuads`), so the term rules are the same.
-/

namespace LeanRDF.NQuads

export NTriples (ParseError)

-- @tg: implements:: [[openspec:datasets#Dataset W3C conformance]]
/-- Parse an N-Quads document (RDF 1.1 N-Quads §5) into a dataset. -/
def parse (src : String) : Except ParseError Dataset :=
  (NTriples.parseQuads src).map (fun qs => Dataset.ofList qs.toList)

end LeanRDF.NQuads
