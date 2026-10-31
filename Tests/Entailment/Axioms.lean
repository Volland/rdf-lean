import LeanRDF

/-! The soundness theorems are axiom-clean (tg.md decision "Axiom-clean library"). -/

-- @tg: verifies:: [[openspec:rdfs-entailment#Soundness#Soundness theorems are axiom-clean]] {level: unit}
/-- info: 'LeanRDF.Derives.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanRDF.Derives.sound

/-- info: 'LeanRDF.Derives.sound_graph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanRDF.Derives.sound_graph

/-- info: 'LeanRDF.rdfsRules_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanRDF.rdfsRules_sound

/-- info: 'LeanRDF.DInterp.IsRDFS.toCore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanRDF.DInterp.IsRDFS.toCore
