---
title: Reference
summary: The modules of LeanRDF and leanrdf-elpi, and their main definitions and theorems.
---
# Reference

Two Lake packages share one repository. `leanrdf` (the root) has no dependencies; `leanrdf-elpi` (`elpi/`) requires `leanrdf` and lean-elpi v0.3.3. Both use Lean 4.35.0.

```lean
-- lakefile.lean of a project using the model and the checker
require leanrdf from git "https://github.com/Volland/rdf-lean" @ "main"
```

## leanrdf

| Module | Main contents |
|---|---|
| `LeanRDF.Core.Term` | `IRI`, `BlankNode`, `Literal` (`typed`, `lang`), `Term` |
| `LeanRDF.Core.Literal` | `Literal.datatype`, `mk?`, `lang'`, `str`, `WellFormed` |
| `LeanRDF.Core.Triple` | `Triple`, `WellFormed`, `mk?`, `renameBNodes` |
| `LeanRDF.Core.Graph` | `Graph`, `empty`, `insert`, `union`, `singleton`, `ofList`, `toList`, `size`, `mem_*` |
| `LeanRDF.Core.Iso` | `Graph.Iso`, `Iso.refl` |
| `LeanRDF.Core.Vocab` | `rdf.*`, `rdfs.*`, `xsd.string`, `rdf.member n` |
| `LeanRDF.Parse.NTriples.*` | `NTriples.parse`, `parseTriples`, `parseTerm`, `ParseError`, `Graph.toNTriples`, `Term.toNTriples` |
| `LeanRDF.Parse.Turtle.*` | `Turtle.parse src base`, `parseTriples`, `parseTriG`, `resolve` |
| `LeanRDF.Core.Dataset` | `Quad`, `Dataset`, `defaultGraph`, `namedGraph`, `graphNames`, `unionGraph`, `ofGraph`, `mem_*` |
| `LeanRDF.Parse.NQuads.*` | `NQuads.parse`, `NTriples.parseQuads`, `Dataset.toNQuads` |
| `LeanRDF.Parse.TriG.Parser` | `TriG.parse src base` |
| `LeanRDF.Xsd.*` | `Literal.value?`, `XsdValue`, `XsdValue.compare?`, `canonicalInteger`, `canonicalDecimal?`, `canonicalDouble`, `DateTime` |
| `LeanRDF.Semantics.Interpretation` | `SimpleInterp`, `denote`, `Holds`, `Satisfies`, `InClass`, `DInterp` |
| `LeanRDF.Semantics.RDFS` | `RDFConditions`, `RDFSConditions`, `IsRDF`, `IsRDFS`, `RDFSCore`, `IsRDFS.toCore` |
| `LeanRDF.Semantics.Entails` | `Graph.SimpleEntails`, `DEntails`, `RDFEntails`, `RDFSEntails` |
| `LeanRDF.Entailment.Rule` | `Pat`, `TPat`, `Guard`, `Rule`, `RangeRestricted`, `UniqueNames` |
| `LeanRDF.Entailment.Rules` | `rdfs2` … `rdfs13`, `rdfD2`, `grdfD1String`, `grdfD1Lang`, `axiomRules`, `rdfsRules` |
| `LeanRDF.Entailment.Derivation` | `Derives`, `Triple.instantiate` |
| `LeanRDF.Entailment.Soundness` | `Rule.Sound`, `rdfsRules_sound`, `Derives.sound`, `Derives.sound_graph` |
| `LeanRDF.Cert.Check` | `Node`, `Certificate`, `check`, `checkQuery`, `check_sound`, `checkQuery_sound`, `checkB_sound`, `checkQueryB_sound` |
| `LeanRDF.Cert.Json` | `Certificate.render`, `Certificate.parse` |
| `LeanRDF.Cert.Datalog` | `toDatalog` (CertifyingDatalog `GraphProblemInput`) |

## leanrdf-elpi

| Module | Main contents |
|---|---|
| `LeanRDFElpi.Encode` | `encodeTerm`, `decodeTerm`, `encodeTriple`, `decodeTriple` |
| `LeanRDFElpi.Codegen` | `stepClauses` (rules to Elpi clauses) |
| `LeanRDFElpi.Saturate` | `program`, `saturate`, `Entry`, `Closure` |
| `LeanRDFElpi.Certify` | `certify`, `entailmentCertificate` |
| `LeanRDFElpi.Demo` | `run`, `verdict`; executable `leanrdf-demo` |

| `LeanRDFElpi.Oxilite.*` | `parseResults`, `patternQuery`, `instantiate`, `WhyNode`, `certificateOfWhy`, `certifyByElpi`, `certifyByWhy`, `run`; `lake exe leanrdf-oxilite` |

## leanrdf-sparql

`leanrdf-sparql` (`sparql/`) requires `leanrdf`.

| Module | Main definitions |
|---|---|
| `LeanRDFSparql.Mapping` | `Mapping`, `find?`, `insert`, `merge`, `restrict`, `compatible`, `ext` |
| `LeanRDFSparql.Algebra` | `TermPat`, `TriplePattern`, `Expr`, `Pattern`, `Query`, `subst`, `size` |
| `LeanRDFSparql.Expr` | `Expr.eval`, `ebv`, `termEq`, `termCmp`, `callBuiltin`, `castTo` |
| `LeanRDFSparql.Semantics` | `Spec.bgp`, `Spec.join`, `Spec.leftJoin`, `Spec.minus`, `Spec.evalN`, `Spec.eval` |
| `LeanRDFSparql.Eval` | `Eval.matchTP`, `Eval.bgp`, `Eval.evalN`, `Eval.eval` |
| `LeanRDFSparql.BgpCorrect`, `Correct`, `Query` | `bgp_perm`, `evalN_perm`, `eval_perm_spec`, `orderBy_sorted`, `Spec.Answer`, `Eval.runQuery`, `runQuery_answer` |
| `LeanRDF.Text.Regex` (core) | `compile`, `isMatch`, `replace` |

## Key theorems

```lean
theorem Derives.sound {g : Graph} {t : Triple} (h : Derives rdfsRules g t) :
    g.RDFSEntails (Graph.singleton t)

theorem Derives.sound_graph {g q : Graph} (μ : BlankNode → Term)
    (h : ∀ t ∈ q, Derives rdfsRules g (t.instantiate μ)) : g.RDFSEntails q

theorem check_sound (h : check rules g c = .ok t) : Derives rules g t

theorem checkQuery_sound (h : checkQuery RDFS.rdfsRules g q c = .ok ()) : g.RDFSEntails q

-- XSD values: canonical forms read back, comparison is the order of Int and Rat
theorem Xsd.parseInteger_canonical (n : Int) : parseInteger (canonicalInteger n) = some n
theorem Xsd.parseDecimal_canonical (q : Rat) (s : String) (h : canonicalDecimal? q = some s) :
    parseDecimal s = some q
-- SPARQL: the evaluator computes the semantics
theorem evalN_perm (n : Nat) (D : Dataset) (G : Graph) (P : Pattern) :
    Eval.evalN n D G P ~ Spec.evalN n D G P
theorem runQuery_answer (D : Dataset) (q : Query) : Spec.Answer D q (Eval.runQuery D q)

theorem Xsd.compare_integer_iff (a b : Int) :
    ((XsdValue.integer a).compare? (.integer b) = some .lt ↔ a < b) ∧
    ((XsdValue.integer a).compare? (.integer b) = some .eq ↔ a = b)
```

## Design and requirements

The design is a typed graph in `tg.md/` (decisions, constraints, simplifications), and the requirements and scenarios are OpenSpec capabilities in `openspec/specs/`. In a checkout:

```bash
tg search "certificate checker"
tg trace --gaps
```
