import LeanRDFElpi

/-! Scenarios of `elpi-bridge › Saturation`, `Golden closures` and `Reflection`: hand-computed
RDFS closures under the six basic rules (`rdfsBasicRules`). -/

namespace LeanRDF.BridgeTests.Saturate

open LeanRDF Bridge Vocab

private def ex (n : String) : Term := .iri ⟨"http://example.org/" ++ n⟩
private def sc : Term := .iri rdfs.subClassOf
private def sp : Term := .iri rdfs.subPropertyOf
private def ty : Term := .iri rdf.type
private def T (s p o : Term) : Triple := ⟨s, p, o⟩

/-- The closure of `facts`, or the empty array if saturation failed. -/
private def close (facts : List Triple) : Closure :=
  (saturate RDFS.rdfsBasicRules (Graph.ofList facts)).toOption.getD #[]

/-- The closure has exactly the expected triples. -/
private def closesTo (facts expected : List Triple) : Bool :=
  (close facts).triples.toList == (Graph.ofList (facts ++ expected)).toList

-- @tg: verifies:: [[openspec:elpi-bridge#Golden closures#Subclass chain]] {level: integration}
#guard closesTo [T (ex "A") sc (ex "B"), T (ex "B") sc (ex "C"), T (ex "x") ty (ex "A")]
  [T (ex "A") sc (ex "C"), T (ex "x") ty (ex "B"), T (ex "x") ty (ex "C")]

-- @tg: verifies:: [[openspec:elpi-bridge#Golden closures#Domain and range]] {level: integration}
#guard closesTo [T (ex "p") (.iri rdfs.domain) (ex "D"), T (ex "p") (.iri rdfs.range) (ex "R"),
    T (ex "x") (ex "p") (ex "y")]
  [T (ex "x") ty (ex "D"), T (ex "y") ty (ex "R")]

-- @tg: verifies:: [[openspec:elpi-bridge#Golden closures#Subproperty chain]] {level: integration}
#guard closesTo [T (ex "p") sp (ex "q"), T (ex "q") sp (ex "r"), T (ex "x") (ex "p") (ex "y")]
  [T (ex "p") sp (ex "r"), T (ex "x") (ex "q") (ex "y"), T (ex "x") (ex "r") (ex "y")]

-- @tg: verifies:: [[openspec:elpi-bridge#Saturation#Cycles terminate]] {level: integration}
#guard closesTo [T (ex "A") sc (ex "B"), T (ex "B") sc (ex "A"), T (ex "x") ty (ex "A")]
  [T (ex "A") sc (ex "A"), T (ex "B") sc (ex "B"), T (ex "x") ty (ex "B")]

/- Domain through a subproperty, and a literal subject from a range (generalized RDF). -/
#guard closesTo [T (ex "p") sp (ex "q"), T (ex "q") (.iri rdfs.domain) (ex "D"),
    T (ex "x") (ex "p") (.lit (Literal.str "v")), T (ex "q") (.iri rdfs.range) (ex "R")]
  [T (ex "x") (ex "q") (.lit (Literal.str "v")), T (ex "x") ty (ex "D"),
    T (.lit (Literal.str "v")) ty (ex "R")]

private def chain (n : Nat) : List Triple :=
  (List.range n).map fun i => T (ex s!"C{i}") sc (ex s!"C{i+1}")

-- @tg: verifies:: [[openspec:elpi-bridge#Saturation#Each triple once, premises first]] {level: integration}
#guard
  let c := close (T (ex "x") ty (ex "C0") :: chain 12)
  -- 12 links: 78 subClassOf triples (pairs i < j), 13 types for x, each triple once
  c.size == 78 + 13 && c.triples.size == c.size && c.wellOrdered

-- @tg: verifies:: [[openspec:elpi-bridge#Reflection#Derivations read back]] {level: integration}
#guard
  let c := close [T (ex "A") sc (ex "B"), T (ex "x") ty (ex "A")]
  match c.find? (T (ex "x") ty (ex "B")) with
  | some e => e.rule == "rdfs9" && e.premises == [T (ex "A") sc (ex "B"), T (ex "x") ty (ex "A")]
  | none => false

-- @tg: verifies:: [[openspec:elpi-bridge#Reflection#Input triples are facts]] {level: integration}
#guard
  let facts := [T (ex "A") sc (ex "B"), T (ex "x") ty (ex "A")]
  (close facts).toList.take 2 |>.all fun e => e.rule == "fact" && e.premises.isEmpty

end LeanRDF.BridgeTests.Saturate
