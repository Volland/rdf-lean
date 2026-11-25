import LeanRDF

/-! Scenarios of `countermodels` in the core, on countermodels recorded from the finder of
`leanrdf-elpi` (`Tests/data/model/`): presentations, their interpretations, the lifting lemmas,
the model checker and its soundness, and the JSON form. -/

namespace LeanRDF.Tests.Countermodels

open Vocab LeanRDF.Model Presentation

private def ex (n : String) : IRI := ⟨"http://example.org/" ++ n⟩
private def T (s p o : IRI) : Triple := ⟨.iri s, .iri p, .iri o⟩
private def load (src : String) : Presentation := ((Countermodel.parse src).toOption.map (·.model)).getD default

private def subclassM := load (include_str "../data/model/subclass-not-symmetric.json")
private def typeM := load (include_str "../data/model/type-not-transferred.json")
private def domainM := load (include_str "../data/model/domain-needs-property.json")
private def petsM := load (include_str "../data/model/pets-tom-dog.json")
private def membersSrc := include_str "../data/model/members.json"
private def membersM := load membersSrc

private def petsG : Graph := (NTriples.parse "
<http://example.org/Dog> <http://www.w3.org/2000/01/rdf-schema#subClassOf> <http://example.org/Mammal> .
<http://example.org/Cat> <http://www.w3.org/2000/01/rdf-schema#subClassOf> <http://example.org/Mammal> .
<http://example.org/Mammal> <http://www.w3.org/2000/01/rdf-schema#subClassOf> <http://example.org/Animal> .
<http://example.org/hasPet> <http://www.w3.org/2000/01/rdf-schema#domain> <http://example.org/Person> .
<http://example.org/hasPet> <http://www.w3.org/2000/01/rdf-schema#range> <http://example.org/Animal> .
<http://example.org/hasDog> <http://www.w3.org/2000/01/rdf-schema#subPropertyOf> <http://example.org/hasPet> .
<http://example.org/hasDog> <http://www.w3.org/2000/01/rdf-schema#range> <http://example.org/Dog> .
<http://example.org/alice> <http://example.org/hasDog> <http://example.org/rex> .
<http://example.org/bob> <http://example.org/hasPet> <http://example.org/tom> .
<http://example.org/tom> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://example.org/Cat> .
<http://example.org/rex> <http://www.w3.org/2000/01/rdf-schema#label> \"Rex\"@en .
").toOption.getD (Graph.ofList [])
private def tomDog : Graph := Graph.ofList [T (ex "tom") rdf.type (ex "Dog")]

private def failure (r : CRegime) (g q : Graph) (P : Presentation) (budget : Nat := 1000000) : String :=
  (countermodelFailure r g q P budget).getD "accepted"

/-! ## Presentations -/

-- @tg: verifies:: [[openspec:countermodels#Model presentations#A well-formed presentation is accepted]] {level: unit}
#guard failed? petsM.wfChecks == none
#guard decide petsM.WellFormed

-- @tg: verifies:: [[openspec:countermodels#Model presentations#Impure kinds are rejected]] {level: unit}
private def someOverride : Literal × Nat := (petsM.overrides.head?).getD default
#guard failed? { petsM with overrides := (someOverride.1, 0) :: petsM.overrides.tail }.wfChecks ==
  some "overrides are values in resource sorts of their kind"
#guard failed? { petsM with strSort := petsM.langSort }.wfChecks ==
  some "literal default sorts have their kinds and are resources"
private def extraStringSort : Presentation :=
  { petsM with kinds := petsM.kinds.push .string, ir := petsM.ir.push true, ip := petsM.ip.push false }
#guard failed? extraStringSort.wfChecks == some "every literal sort is a default or an override sort"

/-! ## Interpretations -/

-- @tg: verifies:: [[openspec:countermodels#Presentation interpretations#IT is injective by construction]] {level: unit}
example (P : Presentation) (hw : P.WellFormed) (x y z x' y' z' : CDom)
    (h : (P.interp hw).IT x y z = (P.interp hw).IT x' y' z') : x = x' ∧ y = y' ∧ z = z' := by
  cases h; exact ⟨rfl, rfl, rfl⟩

-- @tg: verifies:: [[openspec:countermodels#Presentation interpretations#Literal values are injective]] {level: unit}
example (P : Presentation) (hw : P.WellFormed) : ∀ s t s' t',
    (P.dinterp hw).langVal s t = (P.dinterp hw).langVal s' t' → s = s' ∧ t = t' :=
  (P.dinterp hw).langVal_inj

/-! ## Lifting -/

-- @tg: verifies:: [[openspec:countermodels#Lifting lemmas#The rdf:_n axioms lift]] {level: unit}
#guard membersM.iris.any (·.1 == rdf.member 1) && membersM.iris.any (·.1 == rdf.member 2)
#guard failed? membersM.rdfChecks == none

-- @tg: verifies:: [[openspec:countermodels#Lifting lemmas#Datatype classes lift through kind purity]] {level: unit}
-- The sort-level string_class holds on the pets model, so `isRDF_of` gives `string_class` for every
-- element; the pets model is accepted under `rdf` below.
#guard failed? petsM.rdfChecks == none

-- @tg: verifies:: [[openspec:countermodels#Lifting lemmas#A violated sort-level condition is detected]] {level: unit}
private def noRexMammal : Presentation :=
  { petsM with ext := petsM.ext.filter (· != (petsM.sI rdf.type, petsM.sI (ex "rex"), petsM.sI (ex "Mammal"))) }
#guard failed? noRexMammal.rdfsChecks == some "RDFS: rdfs:subClassOf includes class extensions"

/-! ## The model checker -/

-- @tg: verifies:: [[openspec:countermodels#Model checker#subClassOf is not symmetric]] {level: unit}
#guard failure .rdfs (Graph.ofList [T (ex "A") rdfs.subClassOf (ex "B")])
  (Graph.ofList [T (ex "B") rdfs.subClassOf (ex "A")]) subclassM == "accepted"

-- @tg: verifies:: [[openspec:countermodels#Model checker#A model of q is rejected]] {level: unit}
#guard (failure .rdfs petsG (Graph.ofList [⟨.bnode ⟨"x"⟩, .iri rdf.type, .iri (ex "Mammal")⟩]) petsM).startsWith
  "the query holds under the assignment [_:x↦"

-- @tg: verifies:: [[openspec:countermodels#Model checker#A model that misses g is rejected]] {level: unit}
private def noAliceRex : Presentation :=
  { petsM with ext := petsM.ext.filter (· != (petsM.sI (ex "hasDog"), petsM.sI (ex "alice"), petsM.sI (ex "rex"))) }
#guard failure .rdfs petsG tomDog noAliceRex ==
  "a data triple does not hold: <http://example.org/alice> <http://example.org/hasDog> <http://example.org/rex>"

-- @tg: verifies:: [[openspec:countermodels#Model checker#Budget exhaustion is not acceptance]] {level: unit}
#guard (failure .rdfs petsG (Graph.ofList [⟨.bnode ⟨"x"⟩, .iri rdf.type, .iri (ex "Dog")⟩]) petsM 3).startsWith
  "the query search needs"

/-! ## The indexed checker -/

/- `countermodelFailure` decides the conditions through hash indexes; it gives the result of
the list definitions, `countermodelFailureSpec`, on every model and regime here. -/
private def agrees (g q : Graph) (P : Presentation) (budget : Nat := 1000000) : Bool :=
  [CRegime.simple, .rdf, .rdfs].all fun r =>
    countermodelFailure r g q P budget == countermodelFailureSpec r g q P budget
#guard agrees petsG tomDog petsM && agrees petsG tomDog noAliceRex &&
  agrees petsG (Graph.ofList [⟨.bnode ⟨"x"⟩, .iri rdf.type, .iri (ex "Mammal")⟩]) petsM &&
  agrees petsG (Graph.ofList [⟨.bnode ⟨"x"⟩, .iri rdf.type, .iri (ex "Dog")⟩]) petsM 3 &&
  agrees (Graph.ofList [T (ex "A") rdfs.subClassOf (ex "B")])
    (Graph.ofList [T (ex "B") rdfs.subClassOf (ex "A")]) subclassM &&
  agrees petsG tomDog subclassM && agrees petsG tomDog typeM && agrees petsG tomDog domainM &&
  agrees petsG tomDog membersM

/- A rejection does not echo a deeply nested data term in full. -/
private def deepTerm : Nat → Term
  | 0 => .iri (ex "o")
  | n + 1 => .triple (.iri (ex "s")) (.iri (ex "p")) (deepTerm n)
#guard failure .rdfs (Graph.ofList [⟨.iri (ex "x"), .iri (ex "q"), deepTerm 100⟩]) tomDog petsM ==
  "a data triple does not hold: <http://example.org/x> <http://example.org/q> <<( … )>>"

/-- info: 'LeanRDF.Model.countermodelFailure_eq_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms countermodelFailure_eq_spec

/-! ## Soundness -/

-- @tg: verifies:: [[openspec:countermodels#Countermodel soundness#An accepted countermodel gives non-entailment]] {level: unit}
theorem pets_not_tom_dog : ¬ petsG.RDFSEntails tomDog :=
  checkCountermodel_sound_rdfs (P := petsM) (budget := 1000000) (checkCountermodelB_ok (by native_decide))

-- @tg: verifies:: [[openspec:countermodels#Countermodel soundness#Refuting RDFS refutes the weaker regimes]] {level: unit}
theorem pets_not_tom_dog_rdf : ¬ petsG.RDFEntails tomDog := fun h => pets_not_tom_dog h.toRDFS
theorem pets_not_tom_dog_simple : ¬ petsG.SimpleEntails tomDog :=
  fun h => pets_not_tom_dog h.toD.toRDF.toRDFS

-- @tg: verifies:: [[openspec:countermodels#Countermodel soundness#The hand-built vacuity countermodels are reproduced]] {level: unit}
theorem subClassOf_not_symmetric :
    ¬ (Graph.ofList [T (ex "A") rdfs.subClassOf (ex "B")]).RDFSEntails
      (Graph.ofList [T (ex "B") rdfs.subClassOf (ex "A")]) :=
  checkCountermodel_sound_rdfs (P := subclassM) (budget := 1000000) (checkCountermodelB_ok (by native_decide))

theorem type_not_transferred :
    ¬ (Graph.ofList [T (ex "x") rdf.type (ex "C")]).RDFSEntails
      (Graph.ofList [T (ex "x") rdf.type (ex "D")]) :=
  checkCountermodel_sound_rdfs (P := typeM) (budget := 1000000) (checkCountermodelB_ok (by native_decide))

theorem domain_needs_its_property :
    ¬ (Graph.ofList [T (ex "p") rdfs.domain (ex "C"), T (ex "x") (ex "q") (ex "y")]).RDFSEntails
      (Graph.ofList [T (ex "x") rdf.type (ex "C")]) :=
  checkCountermodel_sound_rdfs (P := domainM) (budget := 1000000) (checkCountermodelB_ok (by native_decide))

-- @tg: verifies:: [[openspec:countermodels#Countermodel soundness#Countermodel theorems are axiom-clean]] {level: unit}
/-- info: 'LeanRDF.Model.checkCountermodel_sound_rdfs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms checkCountermodel_sound_rdfs

/-- info: 'LeanRDF.Model.checkCountermodel_sound_rdf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms checkCountermodel_sound_rdf

/-- info: 'LeanRDF.Model.checkCountermodel_sound_simple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms checkCountermodel_sound_simple

/-- info: 'LeanRDF.Model.checkCountermodel_consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms checkCountermodel_consistent

/-! ## JSON -/

-- @tg: verifies:: [[openspec:countermodels#Countermodel format#Countermodel JSON round-trips]] {level: unit}
#guard match Countermodel.parse membersSrc with
  | .ok c => c.model.overrides.any (fun (l, _) => match l with | .dirLang _ _ _ => true | _ => false) &&
      !c.model.assign.isEmpty && (Countermodel.parse c.render).toOption == some c
  | .error _ => false

end LeanRDF.Tests.Countermodels
