import OwlTests.Model

/-! The OWL theorems use only Lean's standard axioms. -/

-- @tg: verifies:: [[openspec:owl-rl#OWL conditions#sameAs is identity]] {level: unit}
/-- info: 'LeanRDF.Owl.sameAs_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanRDF.Owl.sameAs_iff

-- @tg: verifies:: [[openspec:owl-rl#OWL soundness#Soundness theorem]] {level: unit}
/-- info: 'LeanRDF.Owl.owlRules_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanRDF.Owl.owlRules_sound

/-- info: 'LeanRDF.Derives.owl_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanRDF.Derives.owl_sound

/-- info: 'LeanRDF.Owl.Tests.Model.inverse_not_equivalent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanRDF.Owl.Tests.Model.inverse_not_equivalent

/-- info: 'LeanRDF.Owl.Tests.Model.type_not_sameAs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanRDF.Owl.Tests.Model.type_not_sameAs

-- @tg: verifies:: [[openspec:owl-el#EL soundness#Soundness theorem]] {level: unit}
/-- info: 'LeanRDF.Owl.elRules_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanRDF.Owl.elRules_sound

/-- info: 'LeanRDF.Derives.el_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanRDF.Derives.el_sound
