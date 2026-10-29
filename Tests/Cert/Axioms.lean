import LeanRDF

/-! The checker's soundness theorems are axiom-clean. -/

-- @tg: verifies:: [[openspec:certificates#Checker soundness#Checker theorems are axiom-clean]] {level: unit}
/-- info: 'LeanRDF.Cert.check_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanRDF.Cert.check_sound

/-- info: 'LeanRDF.Cert.checkQuery_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanRDF.Cert.checkQuery_sound
