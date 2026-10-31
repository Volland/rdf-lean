import LeanRDFStatements

/-! The golden statement graphs (`StatementsTests/data/golden`), exported in each listed view
and compared byte for byte with the recorded N-Triples, and the command-line scenarios. Run at
build time: any mismatch throws, which fails `lake test`. -/

namespace LeanRDF.Statements.Tests.Golden

private def dir : System.FilePath := "StatementsTests/data/golden"

/-- Export every golden input in each of its views; the number compared, or throw. -/
def runGoldens : IO Nat := do
  let mut fails : Array String := #[]
  let mut n := 0
  for line in ← IO.FS.lines (dir / "index.txt") do
    match line.splitOn " " with
    | file :: name :: flags =>
      n := n + 1
      let (code, out) ← Cli.run ("export" :: (dir / file).toString :: flags)
      let expected ← IO.FS.readFile (dir / s!"{(file.dropEnd 6).toString}.{name}.nt")
      unless code == 0 && out ++ "\n" == expected do
        fails := fails.push s!"{file} {name}: exit {code}, output differs"
    | _ => pure ()
  unless fails.isEmpty do
    throw <| IO.userError s!"{fails.size} golden export(s) differ:\n{"\n".intercalate fails.toList}"
  return n

-- @tg: verifies:: [[openspec:statement-graphs#Statement graph test corpus#Goldens]] {level: integration}
/-- info: 8 -/
#guard_msgs in
#eval runGoldens

private def tmDir : System.FilePath := "StatementsTests/data/tm"

/-- tiramemsu's recorded `tm export --format sg-nt12` files (`StatementsTests/data/tm`, recorded by
`scripts/statements-tm-record.sh`): each must decode in its view and export back byte for byte.
The number checked, or throw. -/
def runTm : IO Nat := do
  let mut fails : Array String := #[]
  let mut n := 0
  for line in ← IO.FS.lines (tmDir / "index.txt") do
    match line.splitOn " " with
    | file :: flags =>
      n := n + 1
      let src ← IO.FS.readFile (tmDir / file)
      let some v := Cli.parseView flags {} | fails := fails.push s!"{file}: bad view {flags}"
      match NTriples.parse src with
      | .error e => fails := fails.push s!"{file}: does not parse: {e}"
      | .ok g =>
        match decode v g with
        | .error e => fails := fails.push s!"{file}: rejected: {e}"
        | .ok sg =>
          unless (sg.toRDF v).toNTriples.toOption == some src do
            fails := fails.push s!"{file}: decodes, but exports back differently"
    | _ => pure ()
  unless fails.isEmpty do
    throw <| IO.userError s!"{fails.size} tiramemsu export(s) fail:\n{"\n".intercalate fails.toList}"
  return n

-- @tg: verifies:: [[openspec:statement-graphs#Statement graph test corpus#tiramemsu exports round-trip]] {level: integration}
/-- info: 8 -/
#guard_msgs in
#eval runTm

-- @tg: verifies:: [[openspec:statement-graphs#Statement graph command line#Export from the command line]] {level: e2e}
/-- info: (0, 6) -/
#guard_msgs in
#eval do
  let (code, out) ← Cli.run ["export", (dir / "routes.jsonl").toString, "--now"]
  return (code, (out.splitOn "\n").length)

-- @tg: verifies:: [[openspec:statement-graphs#Statement graph command line#Check reports violations]] {level: e2e}
/-- info: (1, ["eid 3: self-reference", "warning: eid 4: dangling reference to eid 9"]) -/
#guard_msgs in
#eval do
  let (code, out) ← Cli.run ["check", "StatementsTests/data/check-bad.jsonl"]
  return (code, out.splitOn "\n")

end LeanRDF.Statements.Tests.Golden
