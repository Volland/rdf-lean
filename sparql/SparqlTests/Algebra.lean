import LeanRDFSparql

/-! Scenarios of `sparql-algebra`: mappings, the semantics of OPTIONAL, MINUS and blank nodes,
expressions, and the evaluator against the specification. -/

namespace LeanRDF.Sparql.Tests

open LeanRDF Sparql

private def ex (n : String) : Term := .iri ⟨"http://example.org/" ++ n⟩
private def T (s p o : Term) : Triple := ⟨s, p, o⟩
private def ty : Term := .iri Vocab.rdf.type
private def v (x : String) : TermPat := .var x
private def c (t : Term) : TermPat := .term t
private def tp (s p o : TermPat) : TriplePattern := ⟨s, p, o⟩
private def M (l : List (Var × Term)) : Mapping := l.foldl (fun μ (x, t) => μ.insert x t) Mapping.empty

/-- Solutions as sorted lists of bindings, for comparing multisets in tests. -/
private def norm (Ω : List Mapping) : List (List (Var × Term)) :=
  (Ω.map (·.toList)).mergeSort (fun a b => toString (repr a) ≤ toString (repr b))

private def people : Graph := Graph.ofList
  [T (ex "a") ty (ex "P"), T (ex "b") ty (ex "P"), T (ex "a") (ex "name") (.lit (Literal.str "A")),
   T (ex "a") (ex "knows") (ex "b"), T (ex "a") (ex "knows") (ex "c")]

private def D : Dataset := Dataset.ofGraph people

/-- Run a pattern with both the evaluator and the specification. -/
private def both (P : Pattern) : List (List (Var × Term)) × List (List (Var × Term)) :=
  (norm (Eval.eval D P), norm (Spec.eval D P))

-- @tg: verifies:: [[openspec:sparql-algebra#Algebra#Mapping operations]] {level: unit}
#guard (M [("x", ex "a")]).compatible (M [("x", ex "a"), ("y", ex "b")]) &&
  ((M [("x", ex "a")]).merge (M [("x", ex "a"), ("y", ex "b")])) == M [("x", ex "a"), ("y", ex "b")] &&
  !(M [("x", ex "a")]).compatible (M [("x", ex "c")]) &&
  (M [("y", ex "b"), ("x", ex "a")]) == (M [("x", ex "a"), ("y", ex "b")])

private def optional : Pattern :=
  .leftJoin (.bgp [tp (v "x") (c ty) (c (ex "P"))]) (.bgp [tp (v "x") (c (ex "name")) (v "n")])
    (.term (boolTerm true))

-- @tg: verifies:: [[openspec:sparql-algebra#Algebra semantics#OPTIONAL keeps unmatched mappings]] {level: unit}
#guard (both optional).2 == norm [M [("x", ex "a"), ("n", .lit (Literal.str "A"))], M [("x", ex "b")]]

-- @tg: verifies:: [[openspec:sparql-algebra#Algebra semantics#MINUS without shared variables removes nothing]] {level: unit}
#guard
  let P := Pattern.minus (.bgp [tp (v "x") (c ty) (c (ex "P"))]) (.bgp [tp (v "y") (c (ex "knows")) (v "z")])
  (both P).2 == norm (Spec.eval D (.bgp [tp (v "x") (c ty) (c (ex "P"))]))

-- MINUS with a shared variable removes the compatible mappings.
#guard
  let P := Pattern.minus (.bgp [tp (v "x") (c ty) (c (ex "P"))]) (.bgp [tp (v "x") (c (ex "name")) (v "n")])
  (both P).2 == norm [M [("x", ex "b")]]

-- @tg: verifies:: [[openspec:sparql-algebra#Algebra semantics#Blank nodes in a BGP are hidden variables]] {level: unit}
#guard (both (.bgp [tp (v "x") (c (ex "knows")) (v "_:b")])).2 == norm [M [("x", ex "a")], M [("x", ex "a")]]

private def patterns : List Pattern :=
  [optional,
   .bgp [tp (v "x") (c ty) (c (ex "P")), tp (v "x") (c (ex "knows")) (v "y")],
   .join (.bgp [tp (v "x") (c ty) (c (ex "P"))]) (.bgp [tp (v "x") (c (ex "knows")) (v "_:k")]),
   .union (.bgp [tp (v "x") (c ty) (c (ex "P"))]) (.bgp [tp (v "x") (c (ex "name")) (v "n")]),
   .filter (.exists true (.bgp [tp (v "x") (c (ex "name")) (v "n")])) (.bgp [tp (v "x") (c ty) (c (ex "P"))]),
   .extend (.bgp [tp (v "x") (c ty) (c (ex "P"))]) "k" (.call "STR" [.var "x"]),
   .graph (v "g") (.bgp [tp (v "s") (v "p") (v "o")]),
   .table [M [("x", ex "a")], M [("x", ex "z")]]]

-- @tg: verifies:: [[openspec:sparql-algebra#Proven evaluator#Evaluator and specification agree on small graphs]] {level: integration}
#guard patterns.all fun P => (both P).1 == (both P).2

-- FILTER NOT EXISTS keeps b, the person without a name.
#guard (both (patterns.getD 4 optional)).2 == norm [M [("x", ex "b")]]

-- @tg: verifies:: [[openspec:sparql-algebra#Proven evaluator#Correctness theorem]] {level: unit}
/-- info: 'LeanRDF.Sparql.eval_perm_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms eval_perm_spec
/-- info: 'LeanRDF.Sparql.orderBy_sorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms orderBy_sorted
/-- info: 'LeanRDF.Sparql.runQuery_answer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms runQuery_answer

private def noEx : Pattern → Bool := fun _ => false
private def evalE (e : Expr) (μ : Mapping := Mapping.empty) : Option Term := (e.eval noEx μ).toOption

-- @tg: verifies:: [[openspec:sparql-algebra#Expressions#Errors in OR]] {level: unit}
#guard evalE (.or (.cmp .eq (.var "unbound") (.term (intTerm 1))) (.term (boolTerm true))) == some (boolTerm true) &&
  (evalE (.and (.cmp .eq (.var "unbound") (.term (intTerm 1))) (.term (boolTerm true)))).isNone &&
  evalE (.and (.cmp .eq (.var "unbound") (.term (intTerm 1))) (.term (boolTerm false))) == some (boolTerm false)

-- @tg: verifies:: [[openspec:sparql-algebra#Expressions#Numeric promotion in FILTER]] {level: unit}
#guard
  let gt (n : Term) := (evalE (.cmp .gt (.var "v") (.term (typed "1.5" "decimal"))) (M [("v", n)]))
  gt (intTerm 2) == some (boolTerm true) && gt (intTerm 1) == some (boolTerm false)

#guard evalE (.arith .add (.term (intTerm 1)) (.term (typed "0.5" "decimal"))) == some (typed "1.5" "decimal") &&
  evalE (.arith .div (.term (intTerm 1)) (.term (intTerm 4))) == some (typed "0.25" "decimal") &&
  evalE (.call "STRLEN" [.term (strTerm "abc")]) == some (intTerm 3) &&
  evalE (.call "UCASE" [.term (.lit (.lang "ab" "en"))]) == some (.lit (.lang "AB" "en")) &&
  evalE (.call "REGEX" [.term (strTerm "Alice"), .term (strTerm "^ali"), .term (strTerm "i")]) == some (boolTerm true) &&
  evalE (.call "SUBSTR" [.term (strTerm "foobar"), .term (intTerm 4)]) == some (strTerm "bar") &&
  evalE (.call "CONCAT" [.term (strTerm "a"), .term (strTerm "b")]) == some (strTerm "ab") &&
  evalE (.inList (.term (intTerm 2)) [.term (intTerm 1), .term (typed "2.0" "decimal")] false) == some (boolTerm true) &&
  evalE (.call (Xsd.ns ++ "integer") [.term (strTerm " 42 ")]) == some (intTerm 42)

-- ORDER BY and the modifiers.
#guard
  let q : Query := { pattern := .bgp [tp (v "x") (c (ex "knows")) (v "y")],
                     orderBy := [(.var "y", false)], project := some ["y"], limit := some 1 }
  Eval.runQuery D q == [M [("y", ex "c")]]

end LeanRDF.Sparql.Tests
