import LeanRDFElpi

/-! Scenarios of `oxilite-bridge`, replayed from oxilite outputs recorded by
`scripts/oxilite-fixtures.sh` (`BridgeTests/data/oxilite/`), so `lake test` needs no oxilite. -/

namespace LeanRDF.BridgeTests.Oxilite

open LeanRDF Oxilite Cert

private def dir (s : String) : System.FilePath := "BridgeTests/data/oxilite" / s

private def expect (cond : Bool) (msg : String) : IO Unit := unless cond do throw (IO.userError msg)

private def contains (s sub : String) : Bool := (s.splitOn sub).length > 1

private def ex (n : String) : Term := .iri ⟨"http://example.org/" ++ n⟩

-- @tg: implements:: [[openspec:oxilite-bridge#oxilite reasoning scenarios]] {note: "replays the fixtures that scripts/oxilite-fixtures.sh records"}
/-- Replay a recorded scenario. -/
private def replay (s : String) (mode : Mode := .both) (results : Option System.FilePath := none) :
    IO (UInt32 × String) :=
  let a : Args :=
    { data := dir s / "data.ttl", pattern := dir s / "pattern.ttl", mode := mode
      results := some (results.getD (dir s / "results.json")), whyDir := some (dir s) }
  run RDFS.rdfsRules a

-- @tg: verifies:: [[openspec:oxilite-bridge#Results reading#Bindings become terms]] {level: unit}
#guard match parseResults "{\"head\":{\"vars\":[\"o\",\"n\",\"b\"]},\"results\":{\"bindings\":[{\"o\":{\"type\":\"uri\",\"value\":\"http://example.org/rex\"},\"n\":{\"type\":\"literal\",\"value\":\"Rex\",\"xml:lang\":\"EN\"},\"b\":{\"type\":\"bnode\",\"value\":\"b0\"}}]}}" with
  | .ok r => r.vars == ["o", "n", "b"] && r.solutions.length == 1 &&
      r.solutions.all fun sol => sol.lookup "o" == some (ex "rex") &&
        sol.lookup "n" == some (.lit (.lang "Rex" "en")) && sol.lookup "b" == some (.bnode ⟨"b0"⟩)
  | .error _ => false

-- @tg: verifies:: [[openspec:oxilite-bridge#Results reading#Malformed results are rejected]] {level: unit}
#guard (parseResults "{\"head\":{\"vars\":[]}}").toOption.isNone &&
  (parseResults "not json").toOption.isNone

private def petQuery : Graph := Graph.ofList
  [⟨.bnode ⟨"owner"⟩, .iri Vocab.rdf.type, ex "Person"⟩, ⟨.bnode ⟨"owner"⟩, ex "hasPet", .bnode ⟨"pet"⟩⟩,
   ⟨.bnode ⟨"pet"⟩, .iri Vocab.rdf.type, ex "Mammal"⟩]

-- @tg: verifies:: [[openspec:oxilite-bridge#Query patterns#Pattern to SPARQL and back]] {level: unit}
#guard contains (patternQuery petQuery) "?owner <http://example.org/hasPet> ?pet ." &&
  contains (patternQuery petQuery) "SELECT * WHERE {" &&
  (instantiate petQuery [("owner", ex "bob"), ("pet", ex "tom")]).toList ==
    (Graph.ofList [⟨ex "bob", .iri Vocab.rdf.type, ex "Person"⟩, ⟨ex "bob", ex "hasPet", ex "tom"⟩,
      ⟨ex "tom", .iri Vocab.rdf.type, ex "Mammal"⟩]).toList

-- @tg: verifies:: [[openspec:oxilite-bridge#Certification by Elpi#Every pet answer is certified]] {level: integration}
#eval show IO Unit from do
  let (code, out) ← replay "pets" .search
  expect (code == 0) s!"exit {code}\n{out}"
  expect ((out.splitOn "elpi: certified").length == 3) out

-- @tg: verifies:: [[openspec:oxilite-bridge#Certification by Elpi#A wrong answer is never certified]] {level: integration}
#eval show IO Unit from do
  IO.FS.withTempDir fun d => do
    let src ← IO.FS.readFile (dir "pets" / "results.json")
    -- bob's pet becomes rex: bob does not own rex, and the data does not say so
    let tampered := src.replace "\"http://example.org/tom\"" "\"http://example.org/rex\""
    IO.FS.writeFile (d / "results.json") tampered
    let (code, out) ← replay "pets" .search (results := some (d / "results.json"))
    expect (code == 1) s!"exit {code}\n{out}"
    expect (contains out "not derived" && contains out "not certified") out

/-- The recorded `why` trees of the pet answers. -/
private def petTrees (i : Nat) : IO (List WhyNode) := do
  let j ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile (dir "pets" / whyFile i)))
  IO.ofExcept ((← IO.ofExcept j.getArr?).toList.mapM WhyNode.ofJson)

private def petData : IO Graph := do
  IO.ofExcept ((Turtle.parse (← IO.FS.readFile (dir "pets" / "data.ttl"))).mapError toString)

-- @tg: verifies:: [[openspec:oxilite-bridge#Certification of why trees#oxilite's explanation is checked]] {level: integration}
#eval show IO Unit from do
  let g ← petData
  let trees ← petTrees 0
  let some t := trees.find? (·.triple == ⟨ex "rex", .iri Vocab.rdf.type, ex "Mammal"⟩)
    | throw (IO.userError "no tree for rex rdf:type Mammal")
  let c ← IO.ofExcept (certificateOfWhy RDFS.rdfsRules g [t])
  expect (c.nodes.any (·.rule == "rdfs9") && c.nodes.any (·.rule == "rdfs3")) s!"{repr c}"
  expect (checkB RDFS.rdfsRules g c t.triple) "the checker rejects the translated certificate"

/-- Replace the first asserted premise by a triple that is not in the data. -/
private partial def tamper : WhyNode → WhyNode
  | .mk t s r ps n =>
    if s == "asserted" then .mk ⟨ex "rex", ex "hasPet", ex "tom"⟩ s r ps n
    else .mk t s r (match ps with | p :: rest => tamper p :: rest | [] => []) n

-- @tg: verifies:: [[openspec:oxilite-bridge#Certification of why trees#A tampered tree is rejected]] {level: integration}
#eval show IO Unit from do
  let g ← petData
  let trees ← petTrees 0
  let inst := instantiate petQuery [("owner", ex "alice"), ("pet", ex "rex")]
  expect (certifyByWhy RDFS.rdfsRules g inst trees == .certified) "the untampered trees are not certified"
  expect (!(certifyByWhy RDFS.rdfsRules g inst (trees.map tamper)).isCertified) "a tampered tree is certified"

-- @tg: verifies:: [[openspec:oxilite-bridge#Certification of why trees#Untranslatable steps are reported]] {level: unit}
#guard
  let g := Graph.ofList [⟨ex "a", ex "hasChild", ex "b"⟩, ⟨ex "hasChild", .iri ⟨"http://www.w3.org/2002/07/owl#inverseOf"⟩, ex "hasParent"⟩]
  let leaf (t : Triple) := WhyNode.mk t "asserted" none [] none
  let tree := WhyNode.mk ⟨ex "b", ex "hasParent", ex "a"⟩ "inferred" (some "prp-inv (inverse)")
    [leaf ⟨ex "a", ex "hasChild", ex "b"⟩, leaf ⟨ex "hasChild", .iri ⟨"http://www.w3.org/2002/07/owl#inverseOf"⟩, ex "hasParent"⟩] none
  match certifyByWhy RDFS.rdfsRules g (Graph.singleton tree.triple) [tree] with
  | .untranslated _ => true
  | _ => false

-- @tg: verifies:: [[openspec:oxilite-bridge#Oxilite runner#Recorded run]] {level: e2e}
#eval show IO Unit from do
  let (code, out) ← replay "pets"
  expect (code == 0) s!"exit {code}\n{out}"
  expect ((out.splitOn "verdict: CERTIFIED").length == 3 && (out.splitOn "why:  certified").length == 3) out

-- @tg: verifies:: [[openspec:oxilite-bridge#Oxilite runner#Missing oxilite]] {level: e2e}
#eval show IO Unit from do
  let a : Args :=
    { data := dir "pets" / "data.ttl", pattern := dir "pets" / "pattern.ttl"
      oxilite := "/nonexistent/oxilite" }
  let (code, out) ← run RDFS.rdfsRules a
  expect (code == 3 && contains out "error") s!"exit {code}\n{out}"

-- @tg: verifies:: [[openspec:oxilite-bridge#oxilite reasoning scenarios#oxilite's RDFS scenarios are certified]] {level: integration}
#eval show IO Unit from do
  for s in ["subclass", "chain", "domain", "range", "subproperty"] do
    let (code, out) ← replay s
    expect (code == 0) s!"{s}: exit {code}\n{out}"
    expect (!contains out "not certified") s!"{s}:\n{out}"

end LeanRDF.BridgeTests.Oxilite
