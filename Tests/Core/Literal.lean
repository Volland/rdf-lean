import LeanRDF

/-! Scenarios of `rdf-core › Literal forms`. -/

namespace LeanRDF.Tests.Literal

open Vocab

private def xsdInteger : IRI := ⟨xsdNS ++ "integer"⟩

-- @tg: verifies:: [[openspec:rdf-core#Literal forms#Language-tagged literal has langString datatype]] {level: unit}
example : (Literal.lang' "chat" "fr").datatype = rdf.langString := rfl

-- @tg: verifies:: [[openspec:rdf-core#Literal forms#Typed langString literal is rejected]] {level: unit}
example : Literal.mk? "x" rdf.langString none = none := by decide

/- `String.toLower` is defined by well-founded recursion, so the kernel cannot decide this;
the interpreter evaluates it. -/
-- @tg: verifies:: [[openspec:rdf-core#Literal forms#Language tags are lowercased]] {level: unit}
#guard Literal.lang' "a" "EN" == Literal.lang' "a" "en"

-- @tg: verifies:: [[openspec:rdf-core#Literal forms#Lexical forms are compared exactly]] {level: unit}
example : Literal.typed "1" xsdInteger ≠ Literal.typed "01" xsdInteger := by decide

/-- Smart-constructed literals are well-formed. -/
example : (Literal.str "x").WellFormed := by decide

-- @tg: verifies:: [[openspec:rdf-core#Literal forms#Directional literal has dirLangString datatype]] {level: unit}
#guard
  let l := Literal.dirLang' "مرحبا" "AR" .rtl
  l.datatype == rdf.dirLangString && l.langTag? == some "ar" &&
    l != Literal.lang' "مرحبا" "ar" && l != Literal.dirLang' "مرحبا" "ar" .ltr

-- @tg: verifies:: [[openspec:rdf-core#Literal forms#Typed dirLangString literal is rejected]] {level: unit}
example : Literal.mk? "x" rdf.dirLangString none = none := by decide

/-- A tag with a direction needs `rdf:dirLangString`, and a direction needs a tag. -/
example : Literal.mk? "x" rdf.langString none (some .ltr) = none := by decide

end LeanRDF.Tests.Literal
