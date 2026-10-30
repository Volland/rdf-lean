import LeanRDFShacl.Report

/-!
# The command line

`leanrdf-shacl validate --data DATA --shapes SHAPES` reads both graphs (N-Triples or Turtle by
extension), validates, prints the report in Turtle, and exits with `0` when the data conforms,
`1` when it does not and `3` on an input error.
-/

namespace LeanRDF.Shacl

/-- Read an N-Triples (`.nt`) or Turtle file as a graph. -/
def loadGraph (path : System.FilePath) : IO (Except String Graph) := do
  let src ← match ← (IO.FS.readFile path).toBaseIO with
    | .ok s => pure s
    | .error e => return .error s!"cannot read {path}: {e}"
  return match path.extension with
    | some "nt" => (NTriples.parse src).mapError toString
    | _ => (Turtle.parse src ("file://" ++ path.toString)).mapError toString

/-- Give the blank nodes of the shapes graph their own names, apart from the data graph's. -/
def renameShapes (g : Graph) : Graph :=
  Graph.ofList (g.toList.map (·.renameBNodes fun b => ⟨"shapes_" ++ b.label⟩))

-- @tg: implements:: [[openspec:shacl-core#SHACL command line and oxilite comparison]]
/-- Run the command: the exit code and the output. -/
def runCommand (args : List String) : IO (UInt32 × String) := do
  let usage := "usage: leanrdf-shacl validate --data DATA --shapes SHAPES"
  match args with
  | ["validate", "--data", d, "--shapes", s] | ["validate", "--shapes", s, "--data", d] =>
    let G ← match ← loadGraph d with
      | .ok g => pure g
      | .error e => return (3, s!"error: {e}")
    let SG ← if s == d then pure G else match ← loadGraph s with
      | .ok g => pure (renameShapes g)
      | .error e => return (3, s!"error: {e}")
    match readShapes SG with
    | .error e => return (3, s!"error: shapes: {e}")
    | .ok shapes =>
      let rep := validate G shapes
      return (if rep.conforms then 0 else 1, rep.toTurtle)
  | _ => return (3, usage)

end LeanRDF.Shacl
