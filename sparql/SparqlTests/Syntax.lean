import LeanRDFSparql

/-! Scenarios of `sparql-syntax`: parsing, the §19.8 restrictions, translation, result formats
and the command line. -/

namespace LeanRDF.Sparql.SyntaxTests

open LeanRDF Sparql

private def ex (n : String) : Term := .iri ⟨"http://example.org/" ++ n⟩

private def parses (q : String) : Bool := (parseQuery q "http://example.org/").toOption.isSome

-- @tg: verifies:: [[openspec:sparql-syntax#SPARQL parsing#A full SELECT query]] {level: unit}
#guard match parseQuery "PREFIX ex: <http://example.org/>
SELECT DISTINCT ?s (COUNT(?o) AS ?n) FROM NAMED ex:g
WHERE { ?s ex:p ?o OPTIONAL { ?s ex:q ?r } FILTER(?o > 1) }
GROUP BY ?s HAVING (COUNT(?o) > 0) ORDER BY DESC(?n) LIMIT 5" "" with
  | .ok q => q.dataset.length == 1 && q.groupBy.length == 1 && q.having.length == 1 &&
      q.orderBy.length == 1 && q.limit == some 5 &&
      (match q.form with | .select true false (some items) => items.length == 2 | _ => false)
  | .error _ => false

-- @tg: verifies:: [[openspec:sparql-syntax#SPARQL parsing#Scope restrictions]] {level: unit}
#guard !parses "SELECT ?x WHERE { ?s ?p ?o } GROUP BY ?s" && !parses "SELECT * { ?s ?p ?o } GROUP BY ?s" &&
  !parses "SELECT * { ?s ?p ?o BIND(1 AS ?o) }" && !parses "SELECT (1 AS ?x) (2 AS ?x) {}" &&
  !parses "SELECT * { FILTER(COUNT(*) > 1) }" && parses "SELECT ?s (COUNT(*) AS ?c) { ?s ?p ?o } GROUP BY ?s"

-- @tg: verifies:: [[openspec:sparql-syntax#Translation to the algebra#Filters scope over the group]] {level: unit}
#guard match (parseQuery "SELECT * { ?s <http://e/p> ?o . FILTER(?o > 1) OPTIONAL { ?s <http://e/q> ?r } }" "").toOption.bind (·.toAlgebra.toOption) with
  | some q => match q.pattern with
    | .filter _ (.leftJoin (.bgp [_]) (.bgp [_]) _) => true
    | _ => false
  | none => false

private def chain : Dataset := Dataset.ofGraph (Graph.ofList
  [⟨ex "a", ex "knows", ex "b"⟩, ⟨ex "b", ex "knows", ex "c"⟩, ⟨ex "c", ex "p", ex "d"⟩])

private def rows (q : String) : List Mapping :=
  match (parseQuery q "").toOption.bind fun sq => (execute chain sq).toOption with
  | some (.solutions _ r) => r
  | _ => []

-- @tg: verifies:: [[openspec:sparql-syntax#Translation to the algebra#Property paths]] {level: unit}
#guard (rows "SELECT * { ?x <http://example.org/knows>+ ?y }").length == 3 &&
  (rows "SELECT * { <http://example.org/a> <http://example.org/knows>* ?y }").length == 3 &&
  (rows "SELECT * { ?x <http://example.org/knows>/<http://example.org/knows> ?y }").length == 1

-- @tg: verifies:: [[openspec:sparql-syntax#Translation to the algebra#Aggregates]] {level: unit}
#guard
  let r := rows "SELECT ?s (COUNT(?o) AS ?n) { ?s ?p ?o } GROUP BY ?s"
  r.length == 3 && r.all (·.find? "n" == some (intTerm 1))

private def sample : Answer :=
  .solutions ["a", "b", "c", "d"]
    [(((Mapping.empty.insert "a" (ex "x")).insert "b" (.bnode ⟨"n1"⟩)).insert "c" (.lit (.lang "hi" "en"))),
     Mapping.empty.insert "a" (typed "2" "integer")]

private def sameRows (a b : Answer) : Bool :=
  match a, b with
  | .solutions va ra, .solutions vb rb => va == vb && (ra.map (·.toList)) == (rb.map (·.toList))
  | _, _ => false

-- @tg: verifies:: [[openspec:sparql-syntax#Result formats#Round trip through each readable format]] {level: unit}
#guard ((Answer.ofJson sample.toJson).toOption.map (sameRows sample)).getD false &&
  ((Answer.ofXml sample.toXml).toOption.map (sameRows sample)).getD false &&
  ((Answer.ofTsv sample.toTsv).toOption.map (sameRows sample)).getD false

private def tt : Term :=
  .triple (ex "a") (ex "p") (.triple (.bnode ⟨"b"⟩) (ex "q") (.lit (.dirLang "x" "en" .rtl)))
private def sample12 : Answer :=
  .solutions ["t", "d"] [Mapping.empty |>.insert "t" tt |>.insert "d" (.lit (.dirLang "مرحبا" "ar" .rtl))]

-- @tg: verifies:: [[openspec:sparql-syntax#Result formats#Triple terms round-trip through each readable format]] {level: unit}
#guard ((Answer.ofJson sample12.toJson).toOption.map (sameRows sample12)).getD false &&
  ((Answer.ofXml sample12.toXml).toOption.map (sameRows sample12)).getD false &&
  ((Answer.ofTsv sample12.toTsv).toOption.map (sameRows sample12)).getD false

private def reified : Dataset := Dataset.ofGraph (Graph.ofList
  [⟨ex "r", .iri Vocab.rdf.reifies, .triple (ex "a") (ex "p") (ex "b")⟩])

-- @tg: verifies:: [[openspec:sparql-algebra#Triple terms in evaluation#A variable binds a triple term]] {level: unit}
#guard
  match (parseQuery "SELECT ?t WHERE { ?r <http://www.w3.org/1999/02/22-rdf-syntax-ns#reifies> ?t }" "").toOption.bind
      fun sq => (execute reified sq).toOption with
  | some (.solutions _ r) => r.map (·.find? "t") == [some (.triple (ex "a") (ex "p") (ex "b"))]
  | _ => false

-- @tg: verifies:: [[openspec:sparql-algebra#Triple terms in evaluation#Term tests on a triple term]] {level: unit}
#guard
  let μ := Mapping.empty.insert "t" (.triple (ex "a") (ex "p") (ex "b"))
  let ev (f : String) := (Expr.eval (fun _ => false) μ (.call f [.var "t"])).toOption
  ev "ISIRI" == some (boolTerm false) && ev "ISLITERAL" == some (boolTerm false) && ev "STR" == none

-- @tg: verifies:: [[openspec:sparql-syntax#SPARQL command line#Same flags as oxilite]] {level: e2e}
#eval show IO Unit from do
  let (code, out) ← runCommand ["query", "--location", "../elpi/BridgeTests/data/oxilite/pets/data.ttl",
    "--query", "SELECT ?s WHERE { ?s a <http://example.org/Cat> }", "--results-format", "tsv"]
  unless code == 0 && out == "?s\n<http://example.org/tom>\n" do
    throw (IO.userError s!"exit {code}: {out}")
  let (code, _) ← runCommand ["query", "--location", "missing.ttl", "--query", "ASK {}"]
  unless code == 3 do throw (IO.userError s!"missing file: exit {code}")

end LeanRDF.Sparql.SyntaxTests

namespace LeanRDF.Sparql.SyntaxTests

-- @tg: verifies:: [[openspec:sparql-syntax#Differential run against oxilite#Report committed]] {level: manual}
#eval show IO Unit from do
  let r ← IO.FS.readFile "diff-report.md"
  unless (r.splitOn "| LeanRDF bug | 0 |").length > 1 && (r.splitOn "oxilite 0.").length > 1 do
    throw (IO.userError "diff-report.md must exist, name the oxilite version and list no LeanRDF bug")

end LeanRDF.Sparql.SyntaxTests
