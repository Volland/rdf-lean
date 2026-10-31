import Tests.Turtle.Iso

/-! Scenarios of `turtle › Triple terms in Turtle`, `Reified triples`, `Annotations` and
`Version directives`. -/

namespace LeanRDF.Tests.TurtleRdf12

open Vocab

private def ex (n : String) : Term := .iri ⟨"http://example.org/" ++ n⟩
private def T (s p o : Term) : Triple := ⟨s, p, o⟩
private def reifies : Term := .iri rdf.reifies
private def tt (s p o : Term) : Term := .triple s p o
private def bn (l : String) : Term := .bnode ⟨l⟩

private def pre : String :=
  "@prefix : <http://example.org/> .\n@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .\n"

private def parse? (src : String) : Option Graph := (Turtle.parse (pre ++ src) "http://example.org/").toOption

/-- The document parses to a graph isomorphic to `expected`. -/
private def gives (src : String) (expected : List Triple) : Bool :=
  (parse? src).any (Iso.isomorphic · (Graph.ofList expected))

private def rejects (src : String) : Bool := (parse? src).isNone

-- @tg: verifies:: [[openspec:turtle#Triple terms in Turtle#Triple term as object]] {level: unit}
#guard gives ":r <http://www.w3.org/1999/02/22-rdf-syntax-ns#reifies> <<( :a :b \"c\"@en )>> ."
    [T (ex "r") reifies (tt (ex "a") (ex "b") (.lit (.lang "c" "en")))] &&
  (parse? ":r <http://www.w3.org/1999/02/22-rdf-syntax-ns#reifies> <<( :a :b \"c\"@en )>> .").any
    fun g => !decide (T (ex "a") (ex "b") (.lit (.lang "c" "en")) ∈ g)

-- @tg: verifies:: [[openspec:turtle#Triple terms in Turtle#Nested triple term]] {level: unit}
#guard gives ":s :p <<( :a :b <<( :c :d :e )>> )>> ."
  [T (ex "s") (ex "p") (tt (ex "a") (ex "b") (tt (ex "c") (ex "d") (ex "e")))]

-- @tg: verifies:: [[openspec:turtle#Triple terms in Turtle#Triple term subject is rejected]] {level: unit}
#guard rejects "<<( :a :b :c )>> :p :o ." && rejects ":s :p <<( <<( :a :b :c )>> :d :e )>> ."

-- @tg: verifies:: [[openspec:turtle#Triple terms in Turtle#Property list inside a triple term is rejected]] {level: unit}
#guard rejects ":s :p <<( [ :q :r ] :b :c )>> ."

-- @tg: verifies:: [[openspec:turtle#Reified triples#Reified triple as subject]] {level: unit}
#guard gives "<< :a :b :c >> :p :o ."
    [T (bn "x") reifies (tt (ex "a") (ex "b") (ex "c")), T (bn "x") (ex "p") (ex "o")] &&
  (parse? "<< :a :b :c >> :p :o .").any fun g => !decide (T (ex "a") (ex "b") (ex "c") ∈ g)

-- @tg: verifies:: [[openspec:turtle#Reified triples#Explicit reifier]] {level: unit}
#guard gives ":s :p << :a :b :c ~ :r >> ."
  [T (ex "r") reifies (tt (ex "a") (ex "b") (ex "c")), T (ex "s") (ex "p") (ex "r")]

-- @tg: verifies:: [[openspec:turtle#Reified triples#Nested reified triples]] {level: unit}
#guard gives "<< << :a :b :c ~ :r1 >> :q :d ~ :r2 >> :p :o ."
  [T (ex "r1") reifies (tt (ex "a") (ex "b") (ex "c")), T (ex "r2") reifies (tt (ex "r1") (ex "q") (ex "d")),
   T (ex "r2") (ex "p") (ex "o")]

-- @tg: verifies:: [[openspec:turtle#Reified triples#Empty reifier gives a fresh blank node]] {level: unit}
#guard gives "<< :a :b :c ~ >> :p :o ."
  [T (bn "x") reifies (tt (ex "a") (ex "b") (ex "c")), T (bn "x") (ex "p") (ex "o")]

-- @tg: verifies:: [[openspec:turtle#Reified triples#Literal subject in a reified triple is rejected]] {level: unit}
#guard rejects "<< \"a\" :b :c >> :p :o ."

-- @tg: verifies:: [[openspec:turtle#Annotations#Reifier and annotation block]] {level: unit}
#guard gives ":a :name \"Alice\" ~ :t {| :statedBy :bob ; :recorded \"2021-07-07\"^^xsd:date |} ."
  [T (ex "a") (ex "name") (.lit (Literal.str "Alice")),
   T (ex "t") reifies (tt (ex "a") (ex "name") (.lit (Literal.str "Alice"))),
   T (ex "t") (ex "statedBy") (ex "bob"),
   T (ex "t") (ex "recorded") (.lit (.typed "2021-07-07" ⟨"http://www.w3.org/2001/XMLSchema#date"⟩))]

-- @tg: verifies:: [[openspec:turtle#Annotations#Implicit reifiers, one per block]] {level: unit}
#guard gives ":a :b :c {| :q :d |} {| :q :e |} ."
  [T (ex "a") (ex "b") (ex "c"),
   T (bn "x") reifies (tt (ex "a") (ex "b") (ex "c")), T (bn "x") (ex "q") (ex "d"),
   T (bn "y") reifies (tt (ex "a") (ex "b") (ex "c")), T (bn "y") (ex "q") (ex "e")]

-- @tg: verifies:: [[openspec:turtle#Annotations#Several reifiers]] {level: unit}
#guard gives ":a :b :c ~ :r1 ~ :r2 ."
  [T (ex "a") (ex "b") (ex "c"), T (ex "r1") reifies (tt (ex "a") (ex "b") (ex "c")),
   T (ex "r2") reifies (tt (ex "a") (ex "b") (ex "c"))]

-- @tg: verifies:: [[openspec:turtle#Annotations#Annotations in object lists]] {level: unit}
#guard gives ":a :b :c ~ :r1, :d ~ :r2 ."
  [T (ex "a") (ex "b") (ex "c"), T (ex "a") (ex "b") (ex "d"),
   T (ex "r1") reifies (tt (ex "a") (ex "b") (ex "c")), T (ex "r2") reifies (tt (ex "a") (ex "b") (ex "d"))]

-- @tg: verifies:: [[openspec:turtle#Version directives#Both forms are accepted]] {level: unit}
#guard ["@version \"1.2\" .", "VERSION '1.2'", "version \"1.2-basic\""].all fun v =>
  gives (v ++ "\n:a :b :c .") [T (ex "a") (ex "b") (ex "c")]

-- @tg: verifies:: [[openspec:turtle#Version directives#Version is a hint]] {level: unit}
#guard gives "VERSION \"1.2-basic\"\n:s :p <<( :a :b :c )>> ."
  [T (ex "s") (ex "p") (tt (ex "a") (ex "b") (ex "c"))]

-- @tg: verifies:: [[openspec:turtle#Version directives#Malformed version directives are rejected]] {level: unit}
#guard rejects "@VERSION \"1.2\" .\n:a :b :c ." && rejects "@version \"1.2\"\n:a :b :c ." &&
  rejects "VERSION \"\"\"1.2\"\"\"\n:a :b :c ."

end LeanRDF.Tests.TurtleRdf12
