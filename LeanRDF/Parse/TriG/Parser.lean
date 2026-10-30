import LeanRDF.Parse.Turtle.Parser

/-!
# TriG parser

RDF 1.1 TriG §5 and §6: Turtle statements in graph blocks. The parser shares the Turtle statement
parser (`Turtle.parseTriG`), so terms, prefixes, IRI resolution and generated blank nodes follow
the same rules.
-/

namespace LeanRDF.TriG

export NTriples (ParseError)

-- @tg: implements:: [[openspec:datasets#Dataset W3C conformance]]
/-- Parse a TriG document into a dataset, relative IRIs resolved against `base`. -/
def parse (src : String) (base : String := "") : Except ParseError Dataset :=
  (Turtle.parseTriG src base).map (fun qs => Dataset.ofList qs.toList)

end LeanRDF.TriG
