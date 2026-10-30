import LeanRDFShacl

/-! The validator theorems use only Lean's standard axioms. -/

-- @tg: verifies:: [[openspec:shacl-core#Proven validator#Correctness theorems]] {level: unit}
/-- info: 'LeanRDF.Shacl.validate_conforms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanRDF.Shacl.validate_conforms

/-- info: 'LeanRDF.Shacl.validate_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanRDF.Shacl.validate_sound

/-- info: 'LeanRDF.Shacl.valueNodes_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanRDF.Shacl.valueNodes_iff

/-- info: 'LeanRDF.Shacl.results_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanRDF.Shacl.results_nil
