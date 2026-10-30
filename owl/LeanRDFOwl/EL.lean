import LeanRDFOwl.Rules

/-!
# The EL completion rules

Rules that classify OWL 2 EL ontologies (OWL 2 Profiles §2) over the RDF encoding of class
expressions: an intersection is a node with `owl:intersectionOf` and an `rdf:first`/`rdf:rest`
list, an existential a restriction node with `owl:onProperty` and `owl:someValuesFrom`. Lists
are matched by length, two or three classes, so every list a rule reads ends in `rdf:nil`.
`C ⊑ D` below is `C rdfs:subClassOf D`.
-/

namespace LeanRDF.Owl

open Vocab

private def v (n : String) : Pat := .var n
private def c (i : IRI) : Pat := .const (.iri i)
private def T (s p o : Pat) : TPat := ⟨s, p, o⟩
private def R (name : String) (body : List TPat) (head : TPat) : Rule := { name, body, head }
private def sub (a b : String) : TPat := T (v a) (c rdfs.subClassOf) (v b)

/-- `x` is the intersection of the list `a, b`. -/
private def int2 (x a b : String) : List TPat :=
  [T (v x) (c intersectionOf) (v "l"), T (v "l") (c rdf.first) (v a), T (v "l") (c rdf.rest) (v "l2"),
   T (v "l2") (c rdf.first) (v b), T (v "l2") (c rdf.rest) (c rdf.nil)]

/-- `x` is the intersection of the list `a, b, d`. -/
private def int3 (x a b d : String) : List TPat :=
  [T (v x) (c intersectionOf) (v "l"), T (v "l") (c rdf.first) (v a), T (v "l") (c rdf.rest) (v "l2"),
   T (v "l2") (c rdf.first) (v b), T (v "l2") (c rdf.rest) (v "l3"),
   T (v "l3") (c rdf.first) (v d), T (v "l3") (c rdf.rest) (c rdf.nil)]

/-- `r` is the existential restriction `∃p.d`. -/
private def ex (r p d : String) : List TPat :=
  [T (v r) (c someValuesFrom) (v d), T (v r) (c onProperty) (v p)]

/-- Intersection elimination: `C ⊑ A ⊓ B` gives `C ⊑ A` … -/
def elIntE1 := R "el-int-e1" (sub "c" "x" :: int2 "x" "a" "b") (sub "c" "a")
/-- … and `C ⊑ B`. -/
def elIntE2 := R "el-int-e2" (sub "c" "x" :: int2 "x" "a" "b") (sub "c" "b")
/-- For three conjuncts, the first … -/
def elIntE13 := R "el-int-e1-3" (sub "c" "x" :: int3 "x" "a" "b" "d") (sub "c" "a")
/-- … the second … -/
def elIntE23 := R "el-int-e2-3" (sub "c" "x" :: int3 "x" "a" "b" "d") (sub "c" "b")
/-- … and the third. -/
def elIntE3 := R "el-int-e3" (sub "c" "x" :: int3 "x" "a" "b" "d") (sub "c" "d")
/-- Intersection introduction: `C ⊑ A` and `C ⊑ B` give `C ⊑ A ⊓ B`. -/
def elIntI2 := R "el-int-i2" (sub "c" "a" :: sub "c" "b" :: int2 "x" "a" "b") (sub "c" "x")
/-- … and for three conjuncts. -/
def elIntI3 := R "el-int-i3" (sub "c" "a" :: sub "c" "b" :: sub "c" "d" :: int3 "x" "a" "b" "d")
  (sub "c" "x")
/-- Existential monotonicity: `C ⊑ ∃p.D` and `D ⊑ E` give `C ⊑ ∃p.E`. -/
def elEx := R "el-ex" (sub "c" "r" :: ex "r" "p" "d" ++ sub "d" "e" :: ex "s" "p" "e") (sub "c" "s")
/-- Existentials through subproperties: `C ⊑ ∃p.D` and `p ⊑ q` give `C ⊑ ∃q.D`. -/
def elExSub := R "el-ex-sub"
  (sub "c" "r" :: ex "r" "p" "d" ++ T (v "p") (c rdfs.subPropertyOf) (v "q") :: ex "s" "q" "d")
  (sub "c" "s")
/-- `owl:Nothing` through existentials: `C ⊑ ∃p.D` and `D ⊑ ⊥` give `C ⊑ ⊥`. -/
def elExBot := R "el-ex-bot" (sub "c" "r" :: ex "r" "p" "d" ++ [T (v "d") (c rdfs.subClassOf) (c Nothing)])
  (T (v "c") (c rdfs.subClassOf) (c Nothing))

-- @tg: implements:: [[openspec:owl-el#EL completion rules]]
/-- The EL completion rules. -/
def elRules : List Rule :=
  [elIntE1, elIntE2, elIntE13, elIntE23, elIntE3, elIntI2, elIntI3, elEx, elExSub, elExBot]

/-- The RDFS, OWL 2 RL and EL rules. -/
def owlELRules : List Rule := owlRules ++ elRules

end LeanRDF.Owl
