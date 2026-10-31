import LeanRDF

/-! The checker's soundness theorems are axiom-clean. -/

-- @tg: verifies:: [[openspec:certificates#Checker soundness#Checker theorems are axiom-clean]] {level: unit}
/-- info: 'LeanRDF.Cert.check_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanRDF.Cert.check_sound

/-- info: 'LeanRDF.Cert.checkQuery_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanRDF.Cert.checkQuery_sound

/-! The regime theorems of RDF 1.2 (`add-rdf12-semantics`). -/

-- @tg: verifies:: [[openspec:certificates#Checker soundness#Regime certificates give their entailment]] {level: unit}
/-- info: 'LeanRDF.Cert.checkQuery_sound_rdf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanRDF.Cert.checkQuery_sound_rdf

/-- info: 'LeanRDF.Cert.checkQuery_sound_simple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanRDF.Cert.checkQuery_sound_simple

/-- info: 'LeanRDF.rdfRules_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanRDF.rdfRules_sound
