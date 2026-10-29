import LeanRDF

/-! Scenarios of `rdfs-entailment › Guards` and of the rules added by `add-rdfs-full`, through
the checker: hand-written certificates for each kind of new rule. -/

namespace LeanRDF.Tests.FullRules

open Vocab LeanRDF.Cert RDFS

private def ex (n : String) : Term := .iri ⟨"http://example.org/" ++ n⟩
private def T (s p o : Term) : Triple := ⟨s, p, o⟩
private def ty : Term := .iri rdf.type

-- @tg: verifies:: [[openspec:rdfs-entailment#Guards#Container membership IRIs are recognized exactly]] {level: unit}
#guard containerIndex? (rdf.member 3) == some 3 && containerIndex? (rdf.member 12) == some 12 &&
  containerIndex? (rdf.member 0) == none && containerIndex? ⟨rdfNS ++ "_03"⟩ == none &&
  containerIndex? ⟨rdfNS ++ "_x"⟩ == none && containerIndex? rdfs.member == none

-- @tg: verifies:: [[openspec:rdfs-entailment#Guards#Literal guards test the datatype]] {level: unit}
#guard (Guard.stringLiteral "l").check (fun _ => .lit (Literal.str "a")) &&
  !(Guard.stringLiteral "l").check (fun _ => .lit (.typed "1" ⟨"http://www.w3.org/2001/XMLSchema#integer"⟩)) &&
  (Guard.langLiteral "l").check (fun _ => .lit (.lang "a" "en")) &&
  !(Guard.langLiteral "l").check (fun _ => .lit (Literal.str "a"))

private def g : Graph := Graph.ofList
  [T (ex "s") (ex "p") (.lit (Literal.str "v")), T (ex "seq") (.iri (rdf.member 1)) (ex "a")]

private def node (i : Nat) (t : Triple) (r : String) (ps : List Nat) : Node := ⟨i, t, r, ps⟩

/-- One certificate using rdfD2, rdfs4a, rdfs4b, GrdfD1, an axiom, the container rules, rdfs12
and rdfs7. -/
private def cert : Certificate :=
  { nodes :=
      [ node 0 (T (ex "s") (ex "p") (.lit (Literal.str "v"))) "fact" [],
        node 1 (T (ex "seq") (.iri (rdf.member 1)) (ex "a")) "fact" [],
        node 2 (T (ex "p") ty (.iri rdf.Property)) "rdfD2" [0],
        node 3 (T (ex "s") ty (.iri rdfs.Resource)) "rdfs4a" [0],
        node 4 (T (.lit (Literal.str "v")) ty (.iri rdfs.Resource)) "rdfs4b" [0],
        node 5 (T (.lit (Literal.str "v")) ty (.iri xsd.string)) "GrdfD1-string" [0],
        node 6 (T (.iri rdf.type) ty (.iri rdf.Property))
          s!"axiom <{rdf.type.val}> <{rdf.type.val}> <{rdf.Property.val}>" [],
        node 7 (T (.iri (rdf.member 1)) ty (.iri rdfs.ContainerMembershipProperty)) "rdfs-axiom-cmp-type" [1],
        node 8 (T (.iri (rdf.member 1)) (.iri rdfs.subPropertyOf) (.iri rdfs.member)) "rdfs12" [7],
        node 9 (T (ex "seq") (.iri rdfs.member) (ex "a")) "rdfs7" [8, 1] ]
    goals := [9] }

-- @tg: verifies:: [[openspec:rdfs-entailment#RDFS rule set#New rules check and derive]] {level: unit}
#guard (checkCert rdfsRules g cert).toOption.map (·.size) == some 10

theorem seq_member_a : Derives rdfsRules g (T (ex "seq") (.iri rdfs.member) (ex "a")) :=
  checkB_sound (c := cert) (by native_decide)

private def notString : Certificate :=
  { nodes := [node 0 (T (ex "s") (ex "q") (ex "o")) "fact" [],
              node 1 (T (ex "o") ty (.iri xsd.string)) "GrdfD1-string" [0]]
    goals := [1] }

-- @tg: verifies:: [[openspec:rdfs-entailment#Guards#A failing guard rejects the node]] {level: unit}
#guard (check rdfsRules (Graph.ofList [T (ex "s") (ex "q") (ex "o")]) notString).toOption.isNone

/- `rdf:_0` is not a container membership property, so the container rules do not apply. -/
private def zeroMember : Certificate :=
  { nodes := [node 0 (T (ex "seq") (.iri (rdf.member 0)) (ex "a")) "fact" [],
              node 1 (T (.iri (rdf.member 0)) ty (.iri rdfs.ContainerMembershipProperty))
                "rdfs-axiom-cmp-type" [0]]
    goals := [1] }

#guard (check rdfsRules (Graph.ofList [T (ex "seq") (.iri (rdf.member 0)) (ex "a")]) zeroMember).toOption.isNone

end LeanRDF.Tests.FullRules
