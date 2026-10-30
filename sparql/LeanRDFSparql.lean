import LeanRDFSparql.Mapping
import LeanRDFSparql.Algebra
import LeanRDFSparql.Expr
import LeanRDFSparql.Semantics
import LeanRDFSparql.Eval
import LeanRDFSparql.BgpCorrect
import LeanRDFSparql.Correct
import LeanRDFSparql.Query

/-!
# LeanRDFSparql

SPARQL 1.1 for LeanRDF: the algebra (§18.2), its semantics (§18.5) transcribed as operations on
solution multisets, expressions (§17), and a reference evaluator proven to compute the
semantics (`eval_perm_spec`).
-/
