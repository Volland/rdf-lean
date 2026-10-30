import LeanRDFSparql

/-! Worked examples for the documentation: a SPARQL query from text to answers, and the theorems
that make the answers correct. The examples page and the SPARQL guide quote this file. -/

namespace LeanRDF.Sparql.Examples

open LeanRDF Sparql

private def data : Graph := (Turtle.parse "@prefix : <http://example.org/> .
  :ada :knows :alan, :grace . :alan :knows :grace .
  :grace :name \"Grace\" . :alan :name \"Alan\" .").toOption.getD ∅

private def D : Dataset := Dataset.ofGraph data

/-- Parse a query and run it with the proven evaluator. -/
private def ask (q : String) : Except String Answer := do
  execute D (← (parseQuery q).mapError toString)

/- Whom does Ada know, by name, and does anybody she knows know somebody she knows? -/
#guard (ask "PREFIX : <http://example.org/>
  SELECT ?n WHERE { :ada :knows ?f . ?f :name ?n } ORDER BY ?n").toOption.map (·.toTsv)
  == some "?n\n\"Alan\"\n\"Grace\"\n"

#guard (ask "PREFIX : <http://example.org/>
  ASK { :ada :knows ?x . ?x :knows ?y . :ada :knows ?y }").toOption.map (·.toTsv)
  == some "true\n"

/- A property path: everyone reachable from Ada by one or more `:knows`. -/
#guard match ask "PREFIX : <http://example.org/> SELECT DISTINCT ?x WHERE { :ada :knows+ ?x }" with
  | .ok (.solutions _ rows) => rows.length == 2
  | _ => false

/-! The same query as algebra, built by hand. -/

private def ex (n : String) : Term := .iri ⟨"http://example.org/" ++ n⟩

private def friendsNamed : Pattern :=
  .bgp [⟨.term (ex "ada"), .term (ex "knows"), .var "f"⟩, ⟨.var "f", .term (ex "name"), .var "n"⟩]

/- The evaluator and the declarative semantics agree on it (here by running both). -/
#guard (Eval.eval D friendsNamed).length == (Spec.eval D friendsNamed).length

/-- And on every pattern, as a theorem: the evaluator's solutions are a permutation of the
semantics' solutions (`evalN_perm`), so a query's answer is a correct answer (`runQuery_answer`). -/
example : Spec.Answer D { pattern := friendsNamed } (Eval.runQuery D { pattern := friendsNamed }) :=
  runQuery_answer D _

end LeanRDF.Sparql.Examples
