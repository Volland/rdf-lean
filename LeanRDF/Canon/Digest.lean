import LeanRDF.Canon.Rdfc

/-!
# Graph and dataset digests

The content identity of a dataset: `sha256:` and the lower-case hexadecimal SHA-256 of its
RDFC-1.0 canonical N-Quads, as in RDFC-1.0 §4 and W3C Verifiable Credentials Data Integrity. A
graph is a dataset with only a default graph. Two parties that hold isomorphic data compute the
same digest, whatever the triple order and blank-node labels of their files.
-/

namespace LeanRDF

-- @tg: implements:: [[openspec:rdf-canonicalization#Graph digests]]
/-- The digest of a dataset; an error only when RDFC-1.0 exceeds its work limit. -/
def Dataset.digest (d : Dataset) : Except String String := do
  return "sha256:" ++ Canon.sha256 (← Canon.canonicalNQuads d)

/-- The digest of a graph, as the default graph of a dataset. -/
def Graph.digest (g : Graph) : Except String String := (Dataset.ofGraph g).digest

end LeanRDF
