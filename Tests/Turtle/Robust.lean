import LeanRDF

/-! Robustness of the Turtle parser: precise messages for unterminated lists, the triple-term
nesting limit, and positions in non-ASCII input. -/

namespace LeanRDF.Tests.TurtleRobust

private def errorOf {α : Type} : Except NTriples.ParseError α → Option String
  | .error e => some (toString e)
  | .ok _ => none

-- an unterminated collection asks for `)`, where the next object would have started
#guard errorOf (Turtle.parse "@prefix : <http://ex.org/> .\n:x :p ( :a :b .\n") ==
  some "2:15: expected ')'"
#guard errorOf (Turtle.parse "@prefix : <http://ex.org/> .\n:x :p ( :a :b") ==
  some "2:14: expected ')'"
#guard errorOf (Turtle.parse "@prefix : <http://ex.org/> .\n:x :p ( :a ; :b ) .") ==
  some "2:12: expected ')'"
#guard errorOf (Turtle.parse "@prefix : <http://ex.org/> .\n:x :p [ :q :r .\n") ==
  some "2:15: expected ']'"
-- a decimal that starts with a dot is still an object
#guard (Turtle.parseTriples "@prefix : <http://ex.org/> .\n:x :p ( .5 ) .").toOption.map (·.size) ==
  some 3

/-- A triple whose object is a triple term nested `n` deep. -/
private def nested (n : Nat) : String := Id.run do
  let mut t := ":o"
  for _ in [0:n] do
    t := "<<( :s :p " ++ t ++ " )>>"
  return "@prefix : <http://ex.org/> .\n:s :p " ++ t ++ " .\n"

#guard (Turtle.parseTriples (nested NTriples.defaultMaxTermDepth)).toOption.map (·.size) == some 1
#guard (errorOf (Turtle.parse (nested (NTriples.defaultMaxTermDepth + 1)))).map
  (·.endsWith s!"triple term nested deeper than {NTriples.defaultMaxTermDepth}") == some true
#guard (errorOf (Turtle.parse (nested 3) (maxDepth := 2))).map
  (·.endsWith "triple term nested deeper than 2") == some true
#guard (errorOf (Turtle.parseTriG
  "@prefix : <http://ex.org/> .\n{ :s :p <<( :s :p <<( :s :p <<( :s :p :o )>> )>> )>> . }"
  (maxDepth := 2))).map (·.endsWith "triple term nested deeper than 2") == some true
-- sibling triple terms do not add up
#guard (Turtle.parseTriples "@prefix : <http://ex.org/> .\n:s :p <<( :s :p :o )>>, <<( :s :p :o )>> ."
  (maxDepth := 1)).toOption.map (·.size) == some 2

-- positions count characters in non-ASCII input
#guard errorOf (Turtle.parse "@prefix : <http://ex.org/> .\n:x :p \"été\" ; :q ( :a .") ==
  some "2:23: expected ')'"

end LeanRDF.Tests.TurtleRobust
