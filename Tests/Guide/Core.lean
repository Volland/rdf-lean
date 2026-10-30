import LeanRDF

/-! The snippets of the documentation page "The core library", compiled on every `lake test`. -/

namespace LeanRDF.Tests.Guide

open LeanRDF Vocab

/-! ## Terms -/

def alice : Term := .iri ⟨"http://example.org/alice"⟩
def someone : Term := .bnode ⟨"b0"⟩
def name : Term := .lit (Literal.str "Alice")            -- "Alice", an xsd:string
def nom : Term := .lit (Literal.lang' "Alice" "FR")      -- "Alice"@fr, the tag lowercased
def age : Term := .lit (.typed "36" ⟨Xsd.ns ++ "integer"⟩)

#guard (Literal.lang' "Alice" "FR").datatype == rdf.langString
-- the smart constructor refuses an rdf:langString literal without a tag
#guard (Literal.mk? "Alice" rdf.langString none).isNone

/-! ## Triples and graphs -/

def knows : Term := .iri ⟨"http://example.org/knows"⟩
def t : Triple := ⟨alice, knows, someone⟩

#guard decide t.WellFormed
-- a literal subject is a generalized triple, allowed in graphs but not well-formed RDF
#guard !decide (Triple.WellFormed ⟨name, knows, alice⟩)
#guard (Triple.mk? name knows alice).isNone

def g : Graph := Graph.ofList [t, ⟨alice, .iri rdf.type, .iri ⟨"http://example.org/Person"⟩⟩]

#guard g.size == 2 && decide (t ∈ g)
example (u : Triple) (h k : Graph) : u ∈ h.union k ↔ u ∈ h ∨ u ∈ k := Graph.mem_union

/-! ## Parsing and writing -/

def turtle : String := "@prefix : <http://example.org/> .
:alice :knows [ :name \"Bob\" ] ; a :Person ."

def parsed : Graph := (Turtle.parse turtle).toOption.getD ∅

#guard parsed.size == 3
-- errors carry a line and a column
#guard match NTriples.parse "<http://a> <http://b> .\n" with
  | .error e => (toString e).length > 0
  | .ok _ => false
-- canonical N-Triples: sorted, one triple per line
#guard (Graph.ofList [t]).toNTriples.toOption ==
  some "<http://example.org/alice> <http://example.org/knows> _:b0 .\n"
-- relative IRIs resolve against a base
#guard (Turtle.parse "<s> <p> <../o> ." "http://example.org/a/b").toOption.map (·.toList) ==
  some [⟨.iri ⟨"http://example.org/a/s"⟩, .iri ⟨"http://example.org/a/p"⟩, .iri ⟨"http://example.org/o"⟩⟩]

/-! ## Datasets -/

def trig : String := "@prefix : <http://example.org/> .
:alice :knows :bob . :g1 { :bob :knows :carol . }"

def ds : Dataset := (TriG.parse trig).toOption.getD Dataset.empty

#guard ds.defaultGraph.size == 1 && (ds.namedGraph (.iri ⟨"http://example.org/g1"⟩)).size == 1
#guard ds.unionGraph.size == 2

/-! ## XSD values -/

#guard match (Literal.typed "042" ⟨Xsd.ns ++ "integer"⟩).value? with
  | some (.integer 42) => true
  | _ => false
-- an ill-formed literal of a known datatype has no value
#guard (Literal.typed "forty-two" ⟨Xsd.ns ++ "integer"⟩).value?.isNone
#guard match (Literal.typed "1.5" ⟨Xsd.ns ++ "decimal"⟩).value?, (Literal.typed "2" ⟨Xsd.ns ++ "integer"⟩).value? with
  | some a, some b => a.compare? b == some .lt
  | _, _ => false

end LeanRDF.Tests.Guide
