# Vendored abstract development

`Kernel.lean`, `Export.lean`, `History.lean`, `Quoting.lean` and `Encoding.lean` are copied from
tiramemsu (github.com/Volland/tiramemsu), `paper/statement-as-one-record/lean/StatementExport/`, at
commit `55735c3` ("Paper 3: Lean mechanization, validation archive and Zenodo record"). They
mechanize *When Is a Temporal Statement Store a Statement Graph?* (Volodymyr Pavlyshyn, rev. 4,
12 October 2026, Zenodo 10.5281/zenodo.23335652). The code is licensed `MIT OR Apache-2.0`, as
LeanRDF is; the paper text is CC BY 4.0.

The files keep the paper's namespace (`StatementExport`), definitions, theorem names and
statements. They are abstract over the types of terms (`T`), eids (`E`) and leaf labels (`L`);
`LeanRDFStatements` instantiates them with LeanRDF's types.

## Port edits

Ported from Lean 4.34.1 to Lean 4.35.0. The only edits are:

- each file starts with a four-line provenance comment;
- `import StatementExport.X` became `import LeanRDFStatements.Abstract.X`.

No proof needed a change. `#print axioms` gives the same axioms as in the paper's `Axioms.lean`:
at most `propext`, `Classical.choice` and `Quot.sound`.
