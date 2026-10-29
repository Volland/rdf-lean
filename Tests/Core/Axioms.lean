import LeanRDF

/-! The library is axiom-clean: its theorems use only `propext`, `Quot.sound` and
`Classical.choice` (tg.md decision "Axiom-clean library"). `#guard_msgs` fails the build when
the axioms of a theorem change. -/

/-- info: 'LeanRDF.Graph.mem_insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanRDF.Graph.mem_insert

/-- info: 'LeanRDF.Graph.mem_union' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanRDF.Graph.mem_union

/-- info: 'LeanRDF.Graph.mem_singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanRDF.Graph.mem_singleton

/-- info: 'LeanRDF.Graph.mem_ofList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanRDF.Graph.mem_ofList

/-- info: 'LeanRDF.Graph.mem_toList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanRDF.Graph.mem_toList

/-- info: 'LeanRDF.Graph.mem_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanRDF.Graph.mem_empty

/-- info: 'LeanRDF.Graph.Iso.refl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanRDF.Graph.Iso.refl

/-- info: 'LeanRDF.Literal.mk?_wellFormed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanRDF.Literal.mk?_wellFormed

/-- info: 'LeanRDF.Triple.mk?_wellFormed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanRDF.Triple.mk?_wellFormed

