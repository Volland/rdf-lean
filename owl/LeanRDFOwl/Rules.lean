import LeanRDFOwl.Semantics

/-!
# The OWL 2 RL rules

The OWL 2 RL/RDF rules of OWL 2 Profiles §4.3 (Tables 4 to 9) with a fixed number of premises and
a triple as conclusion, as `Rule` values. A rule with several conclusions is split into one rule
per conclusion (`eq-ref-s`, `eq-ref-p`, …). Rules equal to RDFS patterns are not repeated:
`prp-dom` is rdfs2, `prp-rng` rdfs3, `prp-spo1` rdfs7, `cax-sco` rdfs9, `scm-sco` rdfs11 and
`scm-spo` rdfs5. Not included: the rules over lists (`prp-spo2`, `prp-key`, `prp-adp`, `cls-int1`,
`cls-int2`, `cls-uni`, `cls-oo`, `cax-adc`, `eq-diff2`, `eq-diff3`, `scm-int`, `scm-uni`), the
rules that conclude `false`, and the datatype rules.
-- SIMPLIFICATION: [[simplifications#OWL 2 RL without list rules and inconsistency rules]]
-/

namespace LeanRDF.Owl

open Vocab

private def v (n : String) : Pat := .var n
private def c (i : IRI) : Pat := .const (.iri i)
private def ty : Pat := c rdf.type
private def T (s p o : Pat) : TPat := ⟨s, p, o⟩
private def R (name : String) (body : List TPat) (head : TPat) : Rule := { name, body, head }

/-! ## Equality (Table 4) -/

def eqRefS := R "eq-ref-s" [T (v "s") (v "p") (v "o")] (T (v "s") (c sameAs) (v "s"))
def eqRefP := R "eq-ref-p" [T (v "s") (v "p") (v "o")] (T (v "p") (c sameAs) (v "p"))
def eqRefO := R "eq-ref-o" [T (v "s") (v "p") (v "o")] (T (v "o") (c sameAs) (v "o"))
def eqSym := R "eq-sym" [T (v "x") (c sameAs) (v "y")] (T (v "y") (c sameAs) (v "x"))
def eqTrans := R "eq-trans" [T (v "x") (c sameAs) (v "y"), T (v "y") (c sameAs) (v "z")]
  (T (v "x") (c sameAs) (v "z"))
def eqRepS := R "eq-rep-s" [T (v "s") (c sameAs) (v "s2"), T (v "s") (v "p") (v "o")]
  (T (v "s2") (v "p") (v "o"))
def eqRepP := R "eq-rep-p" [T (v "p") (c sameAs) (v "p2"), T (v "s") (v "p") (v "o")]
  (T (v "s") (v "p2") (v "o"))
def eqRepO := R "eq-rep-o" [T (v "o") (c sameAs) (v "o2"), T (v "s") (v "p") (v "o")]
  (T (v "s") (v "p") (v "o2"))

/-! ## Properties (Table 5) -/

def prpFp := R "prp-fp" [T (v "p") ty (c FunctionalProperty), T (v "x") (v "p") (v "y1"),
  T (v "x") (v "p") (v "y2")] (T (v "y1") (c sameAs) (v "y2"))
def prpIfp := R "prp-ifp" [T (v "p") ty (c InverseFunctionalProperty), T (v "x1") (v "p") (v "y"),
  T (v "x2") (v "p") (v "y")] (T (v "x1") (c sameAs) (v "x2"))
def prpSymp := R "prp-symp" [T (v "p") ty (c SymmetricProperty), T (v "x") (v "p") (v "y")]
  (T (v "y") (v "p") (v "x"))
def prpTrp := R "prp-trp" [T (v "p") ty (c TransitiveProperty), T (v "x") (v "p") (v "y"),
  T (v "y") (v "p") (v "z")] (T (v "x") (v "p") (v "z"))
def prpEqp1 := R "prp-eqp1" [T (v "p1") (c equivalentProperty) (v "p2"), T (v "x") (v "p1") (v "y")]
  (T (v "x") (v "p2") (v "y"))
def prpEqp2 := R "prp-eqp2" [T (v "p1") (c equivalentProperty) (v "p2"), T (v "x") (v "p2") (v "y")]
  (T (v "x") (v "p1") (v "y"))
def prpInv1 := R "prp-inv1" [T (v "p1") (c inverseOf) (v "p2"), T (v "x") (v "p1") (v "y")]
  (T (v "y") (v "p2") (v "x"))
def prpInv2 := R "prp-inv2" [T (v "p1") (c inverseOf) (v "p2"), T (v "x") (v "p2") (v "y")]
  (T (v "y") (v "p1") (v "x"))

/-! ## Classes (Table 6) -/

def clsSvf1 := R "cls-svf1" [T (v "x") (c someValuesFrom) (v "y"), T (v "x") (c onProperty) (v "p"),
  T (v "u") (v "p") (v "v"), T (v "v") ty (v "y")] (T (v "u") ty (v "x"))
def clsSvf2 := R "cls-svf2" [T (v "x") (c someValuesFrom) (c Thing), T (v "x") (c onProperty) (v "p"),
  T (v "u") (v "p") (v "v")] (T (v "u") ty (v "x"))
def clsAvf := R "cls-avf" [T (v "x") (c allValuesFrom) (v "y"), T (v "x") (c onProperty) (v "p"),
  T (v "u") ty (v "x"), T (v "u") (v "p") (v "v")] (T (v "v") ty (v "y"))
def clsHv1 := R "cls-hv1" [T (v "x") (c hasValue) (v "y"), T (v "x") (c onProperty) (v "p"),
  T (v "u") ty (v "x")] (T (v "u") (v "p") (v "y"))
def clsHv2 := R "cls-hv2" [T (v "x") (c hasValue) (v "y"), T (v "x") (c onProperty) (v "p"),
  T (v "u") (v "p") (v "y")] (T (v "u") ty (v "x"))
def clsMaxc2 := R "cls-maxc2" [T (v "x") (c maxCardinality) (.const (.lit one)),
  T (v "x") (c onProperty) (v "p"), T (v "u") ty (v "x"), T (v "u") (v "p") (v "y1"),
  T (v "u") (v "p") (v "y2")] (T (v "y1") (c sameAs) (v "y2"))
def clsMaxqc3 := R "cls-maxqc3" [T (v "x") (c maxQualifiedCardinality) (.const (.lit one)),
  T (v "x") (c onProperty) (v "p"), T (v "x") (c onClass) (v "c"), T (v "u") ty (v "x"),
  T (v "u") (v "p") (v "y1"), T (v "y1") ty (v "c"), T (v "u") (v "p") (v "y2"), T (v "y2") ty (v "c")]
  (T (v "y1") (c sameAs) (v "y2"))
def clsMaxqc4 := R "cls-maxqc4" [T (v "x") (c maxQualifiedCardinality) (.const (.lit one)),
  T (v "x") (c onProperty) (v "p"), T (v "x") (c onClass) (c Thing), T (v "u") ty (v "x"),
  T (v "u") (v "p") (v "y1"), T (v "u") (v "p") (v "y2")] (T (v "y1") (c sameAs) (v "y2"))

/-! ## Class axioms (Table 7) -/

def caxEqc1 := R "cax-eqc1" [T (v "c1") (c equivalentClass) (v "c2"), T (v "x") ty (v "c1")]
  (T (v "x") ty (v "c2"))
def caxEqc2 := R "cax-eqc2" [T (v "c1") (c equivalentClass) (v "c2"), T (v "x") ty (v "c2")]
  (T (v "x") ty (v "c1"))

/-! ## Schema (Table 9) -/

def scmCls1 := R "scm-cls-1" [T (v "c") ty (c «Class»)] (T (v "c") (c rdfs.subClassOf) (v "c"))
def scmCls2 := R "scm-cls-2" [T (v "c") ty (c «Class»)] (T (v "c") (c equivalentClass) (v "c"))
def scmCls3 := R "scm-cls-3" [T (v "c") ty (c «Class»)] (T (v "c") (c rdfs.subClassOf) (c Thing))
def scmCls4 := R "scm-cls-4" [T (v "c") ty (c «Class»)] (T (c Nothing) (c rdfs.subClassOf) (v "c"))
def scmEqc1a := R "scm-eqc1-a" [T (v "c1") (c equivalentClass) (v "c2")]
  (T (v "c1") (c rdfs.subClassOf) (v "c2"))
def scmEqc1b := R "scm-eqc1-b" [T (v "c1") (c equivalentClass) (v "c2")]
  (T (v "c2") (c rdfs.subClassOf) (v "c1"))
def scmEqc2 := R "scm-eqc2" [T (v "c1") (c rdfs.subClassOf) (v "c2"), T (v "c2") (c rdfs.subClassOf) (v "c1")]
  (T (v "c1") (c equivalentClass) (v "c2"))
def scmOp1 := R "scm-op-1" [T (v "p") ty (c ObjectProperty)] (T (v "p") (c rdfs.subPropertyOf) (v "p"))
def scmOp2 := R "scm-op-2" [T (v "p") ty (c ObjectProperty)] (T (v "p") (c equivalentProperty) (v "p"))
def scmDp1 := R "scm-dp-1" [T (v "p") ty (c DatatypeProperty)] (T (v "p") (c rdfs.subPropertyOf) (v "p"))
def scmDp2 := R "scm-dp-2" [T (v "p") ty (c DatatypeProperty)] (T (v "p") (c equivalentProperty) (v "p"))
def scmEqp1a := R "scm-eqp1-a" [T (v "p1") (c equivalentProperty) (v "p2")]
  (T (v "p1") (c rdfs.subPropertyOf) (v "p2"))
def scmEqp1b := R "scm-eqp1-b" [T (v "p1") (c equivalentProperty) (v "p2")]
  (T (v "p2") (c rdfs.subPropertyOf) (v "p1"))
def scmEqp2 := R "scm-eqp2" [T (v "p1") (c rdfs.subPropertyOf) (v "p2"),
  T (v "p2") (c rdfs.subPropertyOf) (v "p1")] (T (v "p1") (c equivalentProperty) (v "p2"))
def scmDom1 := R "scm-dom1" [T (v "p") (c rdfs.domain) (v "c1"), T (v "c1") (c rdfs.subClassOf) (v "c2")]
  (T (v "p") (c rdfs.domain) (v "c2"))
def scmDom2 := R "scm-dom2" [T (v "p2") (c rdfs.domain) (v "c"), T (v "p1") (c rdfs.subPropertyOf) (v "p2")]
  (T (v "p1") (c rdfs.domain) (v "c"))
def scmRng1 := R "scm-rng1" [T (v "p") (c rdfs.range) (v "c1"), T (v "c1") (c rdfs.subClassOf) (v "c2")]
  (T (v "p") (c rdfs.range) (v "c2"))
def scmRng2 := R "scm-rng2" [T (v "p2") (c rdfs.range) (v "c"), T (v "p1") (c rdfs.subPropertyOf) (v "p2")]
  (T (v "p1") (c rdfs.range) (v "c"))
def scmHv := R "scm-hv" [T (v "c1") (c hasValue) (v "i"), T (v "c1") (c onProperty) (v "p1"),
  T (v "c2") (c hasValue) (v "i"), T (v "c2") (c onProperty) (v "p2"),
  T (v "p1") (c rdfs.subPropertyOf) (v "p2")] (T (v "c1") (c rdfs.subClassOf) (v "c2"))
def scmSvf1 := R "scm-svf1" [T (v "c1") (c someValuesFrom) (v "y1"), T (v "c1") (c onProperty) (v "p"),
  T (v "c2") (c someValuesFrom) (v "y2"), T (v "c2") (c onProperty) (v "p"),
  T (v "y1") (c rdfs.subClassOf) (v "y2")] (T (v "c1") (c rdfs.subClassOf) (v "c2"))
def scmSvf2 := R "scm-svf2" [T (v "c1") (c someValuesFrom) (v "y"), T (v "c1") (c onProperty) (v "p1"),
  T (v "c2") (c someValuesFrom) (v "y"), T (v "c2") (c onProperty) (v "p2"),
  T (v "p1") (c rdfs.subPropertyOf) (v "p2")] (T (v "c1") (c rdfs.subClassOf) (v "c2"))
def scmAvf1 := R "scm-avf1" [T (v "c1") (c allValuesFrom) (v "y1"), T (v "c1") (c onProperty) (v "p"),
  T (v "c2") (c allValuesFrom) (v "y2"), T (v "c2") (c onProperty) (v "p"),
  T (v "y1") (c rdfs.subClassOf) (v "y2")] (T (v "c1") (c rdfs.subClassOf) (v "c2"))
def scmAvf2 := R "scm-avf2" [T (v "c1") (c allValuesFrom) (v "y"), T (v "c1") (c onProperty) (v "p1"),
  T (v "c2") (c allValuesFrom) (v "y"), T (v "c2") (c onProperty) (v "p2"),
  T (v "p1") (c rdfs.subPropertyOf) (v "p2")] (T (v "c2") (c rdfs.subClassOf) (v "c1"))

/-- The derivation rules, without the axioms. -/
def owlRLDerivationRules : List Rule :=
  [eqRefS, eqRefP, eqRefO, eqSym, eqTrans, eqRepS, eqRepP, eqRepO,
   prpFp, prpIfp, prpSymp, prpTrp, prpEqp1, prpEqp2, prpInv1, prpInv2,
   clsSvf1, clsSvf2, clsAvf, clsHv1, clsHv2, clsMaxc2, clsMaxqc3, clsMaxqc4,
   caxEqc1, caxEqc2,
   scmCls1, scmCls2, scmCls3, scmCls4, scmEqc1a, scmEqc1b, scmEqc2, scmOp1, scmOp2, scmDp1, scmDp2,
   scmEqp1a, scmEqp1b, scmEqp2, scmDom1, scmDom2, scmRng1, scmRng2, scmHv, scmSvf1, scmSvf2,
   scmAvf1, scmAvf2]

-- @tg: implements:: [[openspec:owl-rl#OWL 2 RL rules]]
/-- The OWL 2 RL rules: the derivation rules and the axioms of `prp-ap`, `cls-thing` and
`cls-nothing1`. -/
def owlRLRules : List Rule := owlRLDerivationRules ++ owlAxioms.map RDFS.axiomRule

/-- The RDFS rules and the OWL 2 RL rules. -/
def owlRules : List Rule := RDFS.rdfsRules ++ owlRLRules

end LeanRDF.Owl
