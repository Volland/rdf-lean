import LeanRDFCheck
import CheckTests
import Lean.Data.Json

/-! `lake test` for `leanrdf-check`: the recorded certificate corpus and the JSON verdicts, run
through the command line. The build-time scenarios are in `CheckTests/`. -/

open LeanRDF.Check Lean

def dataDir : System.FilePath := "CheckTests/data"

-- @tg: implements:: [[openspec:certificate-check#Certificate corpus]]
-- @tg: verifies:: [[openspec:certificate-check#Certificate corpus#The corpus passes]] {level: integration}
/-- Run every corpus line; return the failures and the count per regime. -/
def runCorpus : IO (List String × List (String × Nat)) := do
  let lines := (← IO.FS.readFile (dataDir / "corpus.tsv")).splitOn "\n"
    |>.filter (fun l => !l.isEmpty && !l.startsWith "#")
  let mut fails := []
  let mut counts : List (String × Nat) := []
  for l in lines do
    match l.splitOn "\t" with
    | [r, d, q, c, e] =>
      -- `-` as the query: a clash certificate, checked without --query
      let query := if q == "-" then [] else ["--query", (dataDir / q).toString]
      let (code, out) ← Cli.run (["--rules", r, "--data", (dataDir / d).toString] ++ query ++
        ["--cert", (dataDir / c).toString])
      if code.toNat.repr != e then fails := fails ++ [s!"{l}: exit {code}\n{out}"]
      counts := match counts.find? (·.1 == r) with
        | some _ => counts.map fun (k, n) => if k == r then (k, n + 1) else (k, n)
        | none => counts ++ [(r, 1)]
    | _ => fails := fails ++ [s!"bad corpus line: {l}"]
  return (fails, counts)

def jsonField (out : String) (k : String) : Option Json :=
  (Json.parse out).toOption.bind (·.getObjVal? k |>.toOption)

-- @tg: verifies:: [[openspec:certificate-check#Certificate check command#A demo certificate is accepted]] {level: e2e}
-- @tg: verifies:: [[openspec:certificate-check#JSON verdict#A proven verdict as JSON]] {level: integration}
def provenJson : IO (List String) := do
  let (code, out) ← Cli.run ["--data", (dataDir / "pets.nt").toString, "--query",
    (dataDir / "query-mammal-owner.nt").toString, "--cert", (dataDir / "pets-mammal-owner.json").toString, "--json"]
  let ok := code == 0 && jsonField out "verdict" == some (.str "proven") &&
    jsonField out "theorem" == some (.str "checkQuery_sound") && jsonField out "regime" == some (.str "rdfs") &&
    (jsonField out "mapping").bind (·.getObjVal? "_:pet" |>.toOption) == some (.str "<http://example.org/tom>") &&
    (jsonField out "mapping").bind (·.getObjVal? "_:owner" |>.toOption) == some (.str "<http://example.org/bob>")
  return if ok then [] else [s!"proven JSON verdict: {out}"]

-- @tg: verifies:: [[openspec:certificate-check#Certificate check command#A tampered certificate is rejected]] {level: e2e}
-- @tg: verifies:: [[openspec:certificate-check#JSON verdict#A rejected verdict as JSON]] {level: integration}
def rejectedJson : IO (List String) := do
  let (code, out) ← Cli.run ["--data", (dataDir / "pets.nt").toString, "--query",
    (dataDir / "query-mammal-owner.nt").toString, "--cert",
    (dataDir / "pets-mammal-owner-swapped.json").toString, "--json"]
  let reason := (jsonField out "reason").bind (·.getStr? |>.toOption)
  let ok := code == 2 && jsonField out "verdict" == some (.str "rejected") &&
    jsonField out "exit" == some (toJson 2) && reason.any (!·.isEmpty)
  return if ok then [] else [s!"rejected JSON verdict: {out}"]

-- @tg: verifies:: [[openspec:certificate-check#Certificate check command#Bad input exits 3]] {level: integration}
def badInput : IO (List String) := do
  let mut fails := []
  for args in [["--rules", "owl2", "--data", "x", "--query", "y", "--cert", "z"],
               ["--data", (dataDir / "simple.nt").toString, "--query", (dataDir / "simple-query.nt").toString],
               ["--data", (dataDir / "simple.nt").toString, "--query", (dataDir / "simple-query.nt").toString,
                "--cert", (dataDir / "bad-version.json").toString, "--json"]] do
    let (code, out) ← Cli.run args
    if code != 3 then fails := fails ++ [s!"{args}: exit {code}\n{out}"]
  return fails

private def args (data cert : String) (extra : List String := []) : List String :=
  ["--data", (dataDir / data).toString, "--query", (dataDir / "query-mammal-owner.nt").toString,
   "--cert", (dataDir / cert).toString, "--json"] ++ extra

private def envelopeGraph (cert : String) : IO (Option Json) := do
  let j := (Json.parse (← IO.FS.readFile (dataDir / cert))).toOption
  return j.bind fun j => (j.getObjVal? "envelope" >>= (·.getObjVal? "graph")).toOption

-- @tg: verifies:: [[openspec:certificate-check#Envelope verification#A bound certificate is accepted]] {level: e2e}
def boundAccepted : IO (List String) := do
  let (code, out) ← Cli.run (args "pets-bnode-relabeled.nt" "pets-bnode-mammal-owner.json")
  let ok := code == 0 && jsonField out "bound" == some (.bool true) &&
    jsonField out "graph" == (← envelopeGraph "pets-bnode-mammal-owner.json") &&
    (jsonField out "graph").isSome
  return if ok then [] else [s!"bound certificate on relabeled data: {out}"]

-- @tg: verifies:: [[openspec:certificate-check#Envelope verification#A certificate checked against other data is rejected]] {level: e2e}
def otherDataRejected : IO (List String) := do
  let (code, out) ← Cli.run (args "pets-extended.nt" "pets-mammal-owner.json")
  let (code1, _) ← Cli.run (args "pets-extended.nt" "pets-mammal-owner-v1.json")
  let ok := code == 2 && code1 == 0 &&
    jsonField out "reason" == some (.str "envelope: graph digest mismatch")
  return if ok then [] else [s!"bound certificate on extended data: {out}"]

-- @tg: verifies:: [[openspec:certificate-check#Envelope verification#Version 1 is upgraded]] {level: e2e}
def upgraded : IO (List String) := do
  let out2 : System.FilePath := ".lake/upgraded.json"
  IO.FS.createDirAll ".lake"
  let (code, out) ← Cli.run (args "pets.nt" "pets-mammal-owner-v1.json" ["--emit-envelope", out2.toString])
  let (code2, again) ← Cli.run ["--data", (dataDir / "pets.nt").toString, "--query",
    (dataDir / "query-mammal-owner.nt").toString, "--cert", out2.toString, "--json"]
  let v2 := (Json.parse (← IO.FS.readFile out2)).toOption.bind (·.getObjVal? "version" |>.toOption)
  let ok := code == 0 && jsonField out "bound" == some (.bool false) && code2 == 0 &&
    jsonField again "bound" == some (.bool true) && v2 == some (toJson 2)
  return if ok then [] else [s!"version-1 upgrade: {out}\n{again}"]

private def clashArgs (data cert : String) (rules : String := "owl") : List String :=
  ["--rules", rules, "--data", (dataDir / data).toString, "--cert", (dataDir / cert).toString, "--json"]

-- @tg: verifies:: [[openspec:certificate-check#Clash certificate checking#A clash certificate is verified]] {level: e2e}
-- @tg: verifies:: [[openspec:certificate-check#Clash certificate checking#JSON verdict for a clash]] {level: e2e}
def clashVerified : IO (List String) := do
  let (code, out) ← Cli.run (clashArgs "cats.nt" "cats-clash.json")
  let ok := code == 4 && jsonField out "verdict" == some (.str "inconsistent") &&
    jsonField out "exit" == some (toJson 4) && jsonField out "theorem" == some (.str "checkClash_sound_owl") &&
    jsonField out "clash" == some (.str "cax-dw")
  let (code2, text) ← Cli.run ["--rules", "owl", "--data", (dataDir / "cats.nt").toString,
    "--cert", (dataDir / "cats-clash.json").toString]
  let ok := ok && code2 == 4 && (text.splitOn "INCONSISTENT").length > 1
  -- a clash certificate given with --query is an input error
  let (code3, _) ← Cli.run ["--rules", "owl", "--data", (dataDir / "cats.nt").toString, "--query",
    (dataDir / "query-mammal-owner.nt").toString, "--cert", (dataDir / "cats-clash.json").toString]
  return if ok && code3 == 3 then [] else [s!"clash certificate: {out}\n{text}\nwith --query: exit {code3}"]

-- @tg: verifies:: [[openspec:certificate-check#Clash certificate checking#A tampered clash certificate is rejected]] {level: e2e}
def clashTampered : IO (List String) := do
  let (code, out) ← Cli.run (clashArgs "cats.nt" "cats-clash-reordered.json")
  let ok := code == 2 && jsonField out "verdict" == some (.str "rejected")
  return if ok then [] else [s!"tampered clash certificate: {out}"]

private def cmArgs (cm : String) (rules : String := "rdfs") : List String :=
  ["--rules", rules, "--data", (dataDir / "pets.nt").toString, "--query",
   (dataDir / "query-tom-dog.nt").toString, "--countermodel", (dataDir / cm).toString, "--json"]

-- @tg: verifies:: [[openspec:certificate-check#Countermodel input#An accepted countermodel exits 5]] {level: e2e}
def countermodelAccepted : IO (List String) := do
  let (code, out) ← Cli.run (cmArgs "pets-tom-dog-countermodel.json")
  let ok := code == 5 && jsonField out "verdict" == some (.str "refuted") &&
    jsonField out "theorem" == some (.str "checkCountermodel_sound_rdfs") &&
    jsonField out "datatypes" == some (.str "D = {xsd:string, rdf:langString, rdf:dirLangString}")
  let (code2, text) ← Cli.run ((cmArgs "pets-tom-dog-countermodel.json").filter (· != "--json"))
  let ok := ok && code2 == 5 && (text.splitOn "REFUTED").length > 1 && (text.splitOn "rdfs").length > 1
  return if ok then [] else [s!"countermodel: {out}\n{text}"]

-- @tg: verifies:: [[openspec:certificate-check#Countermodel input#A forged countermodel exits 2]] {level: e2e}
def countermodelForged : IO (List String) := do
  let (code, out) ← Cli.run (cmArgs "pets-tom-dog-countermodel-forged.json")
  let reason := ((jsonField out "reason").bind (·.getStr? |>.toOption)).getD ""
  let ok := code == 2 && (reason.splitOn "the query holds under the assignment").length > 1
  return if ok then [] else [s!"forged countermodel: {out}"]

-- @tg: verifies:: [[openspec:certificate-check#Countermodel input#OWL countermodels are an input error]] {level: e2e}
def countermodelOwl : IO (List String) := do
  let (code, out) ← Cli.run (cmArgs "pets-tom-dog-countermodel.json" "owl")
  return if code == 3 then [] else [s!"OWL countermodel: exit {code}\n{out}"]

/-- Write a scratch input under `.lake/robust/`. -/
private def scratch (name content : String) : IO System.FilePath := do
  let dir : System.FilePath := ".lake/robust"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / name) content
  return dir / name

/-- Values a certificate makes the checker repeat are bounded, and so is the time to repeat them:
a 100,000-digit goal or node id is given by its size in the text and the JSON verdicts (exit 2),
and so is a 100,000-digit version (exit 3). -/
def echoBounded : IO (List String) := do
  let big := String.ofList (List.replicate 100000 '9')
  let goal ← scratch "huge-goal.json" s!"\{\"version\": 1, \"nodes\": [], \"goals\": [{big}]}"
  let version ← scratch "huge-version.json" s!"\{\"version\": {big}, \"nodes\": [], \"goals\": []}"
  let id ← scratch "huge-id.json" (s!"\{\"version\": 1, \"goals\": [0], \"nodes\": [\{\"id\": {big}, " ++
    "\"conclusion\": [\"<http://example.org/tom>\", \"<http://example.org/p>\", " ++
    "\"<http://example.org/x>\"], \"rule\": \"fact\", \"premises\": []}]}")
  let base := ["--data", (dataDir / "pets.nt").toString, "--query",
    (dataDir / "query-mammal-owner.nt").toString, "--cert"]
  let (c1, t1) ← Cli.run (base ++ [goal.toString])
  let (c2, j2) ← Cli.run (base ++ [goal.toString, "--json"])
  let (c3, t3) ← Cli.run (base ++ [version.toString])
  let (c4, t4) ← Cli.run (base ++ [id.toString])
  let has (s t : String) := (s.splitOn t).length > 1
  let size := "…(a 332193-bit number)"
  let ok := c1 == 2 && t1.length < 2000 && has t1 size && c2 == 2 && j2.length < 2000 &&
    has j2 size && (Json.parse j2).toOption.isSome && c3 == 3 && t3.length < 2000 &&
    has t3 "unsupported certificate version of 332193 bits" && c4 == 2 && t4.length < 2000 &&
    has t4 s!"node {size}: an id or a premise of 200 digits or more names no node"
  return if ok then [] else
    [s!"bounded echo: exit {c1} {c2} {c3} {c4}\n{t1.take 500}\n{j2.take 500}\n{t3.take 500}\n{t4.take 500}"]

/-- Malformed input exits 3 with a positioned message: JSON nested past 10,000 levels, a triple
term nested past the parser's limit, an unterminated Turtle collection, bytes that are not
UTF-8. -/
def malformedInput : IO (List String) := do
  let deep ← scratch "deep.json" (String.ofList (List.replicate 20000 '['))
  let tt := Id.run do
    let mut t := "<http://e/o>"
    for _ in [0:2000] do t := "<<( <http://e/s> <http://e/p> " ++ t ++ " )>>"
    return "<http://e/s> <http://e/p> " ++ t ++ " .\n"
  let deepTT ← scratch "deep-tt.nt" tt
  let coll ← scratch "coll.ttl" "@prefix : <http://ex.org/> .\n:x :p ( :a :b .\n"
  let utf8 : System.FilePath := ".lake/robust/bad-utf8.nt"
  IO.FS.writeBinFile utf8 ⟨#[0x3C, 0xFF]⟩
  let run (data cert : String) := Cli.run ["--data", data, "--query",
    (dataDir / "query-mammal-owner.nt").toString, "--cert", cert]
  let pets := (dataDir / "pets.nt").toString
  let certOk := (dataDir / "pets-mammal-owner.json").toString
  let has (s t : String) := (s.splitOn t).length > 1
  let (c1, o1) ← run pets deep.toString
  let (c2, o2) ← run deepTT.toString certOk
  let (c3, o3) ← run coll.toString certOk
  let (c4, o4) ← run utf8.toString certOk
  let ok := c1 == 3 && has o1 "nesting deeper than 10000 levels" &&
    c2 == 3 && has o2 s!"{deepTT}:1:" && has o2 "triple term nested deeper than 1024" &&
    c3 == 3 && has o3 s!"{coll}:2:15: expected ')'" &&
    c4 == 3 && has o4 s!"{utf8}:1:2: not UTF-8: byte 0xff at byte offset 1"
  return if ok then [] else
    [s!"malformed input: {c1} {o1}\n{c2} {o2.take 300}\n{c3} {o3}\n{c4} {o4}"]

def main : IO UInt32 := do
  let (fails, counts) ← runCorpus
  let fails := fails ++ (← provenJson) ++ (← rejectedJson) ++ (← badInput) ++
    (← boundAccepted) ++ (← otherDataRejected) ++ (← upgraded) ++ (← clashVerified) ++ (← clashTampered) ++
    (← countermodelAccepted) ++ (← countermodelForged) ++ (← countermodelOwl) ++
    (← echoBounded) ++ (← malformedInput)
  for f in fails do IO.eprintln s!"FAIL {f}"
  IO.println s!"certificate corpus: {", ".intercalate (counts.map fun (r, n) => s!"{r} {n}")}"
  IO.println (if fails.isEmpty then "leanrdf-check tests: ok" else s!"leanrdf-check tests: {fails.length} failure(s)")
  return if fails.isEmpty then 0 else 1
