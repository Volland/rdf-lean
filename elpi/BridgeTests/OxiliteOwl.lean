import LeanRDFElpi

/-! Scenarios of `oxilite-bridge` under the OWL profile, replayed from the recorded run of the
OWL 2 RL sample in `BridgeTests/data/oxilite/owl-family/`. -/

namespace LeanRDF.BridgeTests.OxiliteOwl

open LeanRDF Oxilite Cert

private def dir : System.FilePath := "BridgeTests/data/oxilite/owl-family"

private def expect (cond : Bool) (msg : String) : IO Unit := unless cond do throw (IO.userError msg)

private def contains (s sub : String) : Bool := (s.splitOn sub).length > 1

private def ex (n : String) : Term := .iri ⟨"http://example.org/" ++ n⟩

private def family : IO Graph := do
  IO.ofExcept ((Turtle.parse (← IO.FS.readFile (dir / "data.ttl"))).mapError toString)

/-- The recorded tree of `ex:bob ex:hasParent ex:alice`, which oxilite infers by prp-inv. -/
private def invTree : IO WhyNode := do
  let j ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile (dir / whyFile 0)))
  let trees ← IO.ofExcept ((← IO.ofExcept j.getArr?).toList.mapM WhyNode.ofJson)
  let some t := trees.find? (·.triple == ⟨ex "bob", ex "hasParent", ex "alice"⟩)
    | throw (IO.userError "no tree for bob hasParent alice")
  expect (t.rule == some "prp-inv (inverse)") s!"{repr t.rule}"
  return t

-- @tg: verifies:: [[openspec:oxilite-bridge#OWL profile#An inverse-property explanation is checked]] {level: integration}
#eval show IO Unit from do
  let g ← family
  let t ← invTree
  let c ← IO.ofExcept (certificateOfWhy Owl.owlRules g [t])
  expect (c.nodes.any fun n => n.rule == "prp-inv1" || n.rule == "prp-inv2") s!"{repr c}"
  expect (checkB Owl.owlRules g c t.triple) "the checker rejects the translated certificate"

-- @tg: verifies:: [[openspec:oxilite-bridge#OWL profile#RDFS profile still refuses OWL steps]] {level: integration}
#eval show IO Unit from do
  let g ← family
  let t ← invTree
  match certifyByWhy RDFS.rdfsRules g (Graph.singleton t.triple) [t] with
  | .untranslated _ => pure ()
  | v => throw (IO.userError s!"expected untranslated, got {v.describe}")

/- The recorded answers to `?child ex:hasParent ?parent` are certified under the OWL profile. -/
#eval show IO Unit from do
  let a : Args := { data := dir / "data.ttl", pattern := dir / "pattern.ttl", profile := .owl,
                    results := some (dir / "results.json"), whyDir := some dir }
  let (code, out) ← run Owl.owlRules a
  expect (code == 0) s!"exit {code}\n{out}"
  expect ((out.splitOn "verdict: CERTIFIED").length == 3) out

private def replayInferred (file : System.FilePath) : IO (UInt32 × String) :=
  runMaterialized Owl.owlRules
    { data := dir / "data.ttl", pattern := "", profile := .owl, materialized := true,
      inferred := some file }

-- @tg: verifies:: [[openspec:oxilite-bridge#Materialized inferences#oxilite's OWL 2 RL closure of a sample ontology]] {level: e2e}
#eval show IO Unit from do
  let (code, out) ← replayInferred (dir / "inferred.tsv")
  expect (code == 1) s!"exit {code}\n{out}"
  let infs ← IO.ofExcept (parseInferences (← IO.FS.readFile (dir / "inferred.tsv")))
  let vs ← IO.ofExcept (certifyInferences Owl.owlRules (← family) infs)
  -- what is not certified is oxilite typing a resource as owl:Thing, for which OWL 2 RL has no rule
  let thing : Term := .iri Owl.Thing
  for (i, v) in vs do
    if i.triple.p == .iri Vocab.rdf.type && i.triple.o == thing then
      expect (!v.isCertified && !v.isRejected) s!"{i.line}: {v.describe}"
    else expect v.isCertified s!"{i.line}: {v.describe}"
  expect (vs.any fun (i, _) => i.rule == "prp-trp (transitive)") "no transitive inference recorded"
  expect (contains out "oxilite: prp-inv (inverse)") out

-- @tg: verifies:: [[openspec:oxilite-bridge#Materialized inferences#A fabricated inference is never certified]] {level: e2e}
#eval show IO Unit from do
  IO.FS.withTempDir fun d => do
    let src ← IO.FS.readFile (dir / "inferred.tsv")
    let fake := "prp-inv (inverse)\t<http://example.org/alice> <http://example.org/hasParent> <http://example.org/bob> .\n"
    IO.FS.writeFile (d / "inferred.tsv") (src ++ fake)
    let (code, out) ← replayInferred (d / "inferred.tsv")
    expect (code == 1) s!"exit {code}\n{out}"
    let infs ← IO.ofExcept (parseInferences (src ++ fake))
    let vs ← IO.ofExcept (certifyInferences Owl.owlRules (← family) infs)
    match vs.getLast? with
    | some (_, .notDerived _) => pure ()
    | some (_, v) => throw (IO.userError s!"the fabricated inference is {v.describe}")
    | none => throw (IO.userError "no inferences")

end LeanRDF.BridgeTests.OxiliteOwl
