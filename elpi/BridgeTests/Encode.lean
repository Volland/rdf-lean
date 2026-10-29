import LeanRDFElpi

/-! Scenarios of `elpi-bridge › Term encoding` and `elpi-bridge › Rule clauses`. -/

namespace LeanRDF.BridgeTests.Encode

open LeanRDF Bridge

private def terms : List Term :=
  [.iri ⟨"http://example.org/a"⟩, .bnode ⟨"b0"⟩, .lit (Literal.str "say \"hi\" \\ there"),
    .lit (.typed "5" ⟨"http://www.w3.org/2001/XMLSchema#integer"⟩), .lit (.lang "chat" "fr")]

-- @tg: verifies:: [[openspec:elpi-bridge#Term encoding#Every term kind round-trips]] {level: unit}
#guard terms.all fun t => (decodeTerm (encodeTerm t)).toOption == some t

#guard terms.all fun t => (decodeTriple (encodeTriple ⟨t, .iri ⟨"http://example.org/p"⟩, t⟩)).toOption
  == some ⟨t, .iri ⟨"http://example.org/p"⟩, t⟩

-- @tg: verifies:: [[openspec:elpi-bridge#Term encoding#A malformed term is a decoding error]] {level: unit}
#guard (decodeTerm (.lit (.str "not a term"))).toOption.isNone

-- @tg: verifies:: [[openspec:elpi-bridge#Rule clauses#One clause per premise]] {level: unit}
#guard RDFS.rdfsRules.all fun r => (stepClauses r).toOption.map (·.length) == some r.body.length

-- @tg: verifies:: [[openspec:elpi-bridge#Rule clauses#Generated clauses load]] {level: unit}
#guard (program RDFS.rdfsRules).toOption.isSome

/- Rules the bridge cannot run yet are refused with a reason. -/
#guard (stepClauses { name := "axiom", body := [], head := ⟨.var "x", .var "x", .var "x"⟩ }).toOption.isNone

end LeanRDF.BridgeTests.Encode
