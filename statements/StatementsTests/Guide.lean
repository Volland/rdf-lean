import LeanRDFStatements

/-! The example of the documentation page "Statement graphs" (`site/content/docs/statements.md`),
compiled with the tests so the page stays true. -/

namespace LeanRDF.Statements.Guide

open LeanRDF LeanRDF.Statements

def ex (n : String) : IRI := ⟨"http://example.org/" ++ n⟩
def e1 : Record := { eid := 1, s := .term (.iri (ex "FRA")), p := ex "route",
                     o := .term (.iri (ex "LHR")), txAdded := 1 }
def e2 : Record := { eid := 2, s := .eid 1, p := ex "distance",
                     o := .term (.lit (.typed "655" xsdInteger)), txAdded := 2 }

def sg : StatementGraph := (StatementGraph.ofList? [e1, e2]).toOption.getD .empty

#guard sg.check == []                               -- well formed
#guard (sg.toRDF {}).size == 6                      -- the view `now`: 2 reifiers, 2 clocks, 2 base triples
#guard sg.kernel == [1, 2]
#guard (sg.quote 2).toOption.map (·.toNTriples) == some
  "<<( <<( <http://example.org/FRA> <http://example.org/route> <http://example.org/LHR> )>> <http://example.org/distance> \"655\"^^<http://www.w3.org/2001/XMLSchema#integer> )>>"
#guard decode {} (sg.toRDF {}) matches .ok _

end LeanRDF.Statements.Guide
