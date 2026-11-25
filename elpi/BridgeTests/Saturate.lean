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
  (saturate RDFS.rdfsBasicRules (Graph.ofList facts)).toOption.getD default

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

/- The search budget bounds each round: a round that needs more Elpi steps stops the
saturation with an error that says so, never with a partial closure. -/
#guard match saturate RDFS.rdfsBasicRules (Graph.ofList (T (ex "x") ty (ex "C0") :: chain 12)) 10 with
  | .error e => isBudgetExhausted e
  | .ok _ => false

/- Continuing a closure with more triples gives the closure of all of them, premises first. -/
#guard
  let facts := [T (ex "A") sc (ex "B"), T (ex "x") ty (ex "A")]
  let more := [T (ex "B") sc (ex "C"), T (ex "A") sc (ex "B")]
  match program RDFS.rdfsBasicRules with
  | .ok e =>
    match saturateWith e (Graph.ofList facts) >>= (·.extend e more) with
    | .ok c => c.triples.toList == (close (facts ++ more)).triples.toList && c.wellOrdered &&
        c.size == c.triples.size
    | .error _ => false
  | .error _ => false

/- Triple terms in rule heads are interned as they are built: a rule may produce a triple
term that is in no input triple, and later rounds match it. -/
private def wrap : Rule :=
  { name := "wrap", body := [⟨.var "x", .const (ex "p"), .var "y"⟩]
    head := ⟨.triple (.var "x") (.const (ex "p")) (.var "y"), .const (ex "q"), .var "y"⟩ }
private def unwrap : Rule :=
  { name := "unwrap", body := [⟨.triple (.var "x") (.var "r") (.var "y"), .const (ex "q"), .var "z"⟩]
    head := ⟨.var "x", .const (ex "seen"), .var "z"⟩ }
#guard
  let tp : Term := .triple (ex "a") (ex "p") (ex "b")
  match saturate [wrap, unwrap] (Graph.ofList [T (ex "a") (ex "p") (ex "b")]) with
  | .ok c => c.size == 3 && (c.find? (T tp (ex "q") (ex "b"))).isSome &&
      ((c.find? (T (ex "a") (ex "seen") (ex "b"))).map (·.rule)) == some "unwrap"
  | .error _ => false

/- A rule that builds a new triple term from every match nests without end; the budget of the
whole saturation stops it with a clear error. -/
private def nest : Rule :=
  { name := "nest", body := [⟨.var "x", .const (ex "p"), .var "y"⟩]
    head := ⟨.triple (.var "x") (.const (ex "p")) (.var "y"), .const (ex "p"), .var "y"⟩ }
#guard
  match program [nest] with
  | .ok e => match saturateFrom e (e.start (Graph.ofList [T (ex "a") (ex "p") (ex "b")])) 0 1000 20000 with
    | .error m => isBudgetExhausted m
    | .ok _ => false
  | .error _ => false

end LeanRDF.BridgeTests.Saturate
