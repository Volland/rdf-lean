import LeanRDF

/-! Scenarios of `sparql-algebra › Regular expressions`, on the core regex engine. -/

namespace LeanRDF.Tests.RegexTests

open Text.Regex

private def m (p f s : String) : Bool :=
  match compile p f with
  | .ok r => isMatch r s
  | .error _ => false

-- @tg: verifies:: [[openspec:sparql-algebra#Regular expressions#Case-insensitive match]] {level: unit}
#guard m "^ali" "i" "Alice" && !m "^ali" "" "Alice" && m "BA" "i" "xxba"

-- @tg: verifies:: [[openspec:sparql-algebra#Regular expressions#Bounded quantifiers]] {level: unit}
#guard m "[0-9]{3}-[0-9]{2}" "" "123-45" && !m "^[0-9]{3}-[0-9]{2}$" "" "12-345" &&
  m "^a{2,3}$" "" "aaa" && !m "^a{2,3}$" "" "aaaa"

#guard m "^(ab)+$" "" "ababab" && m "(a)\\1" "" "aa" && m "[a-z-[aeiou]]+" "" "xyz" &&
  m "\\d+" "" "x12" && m "^a.b$" "s" "a\nb" && !m "^a.b$" "" "a\nb" && m "^b" "m" "a\nb" &&
  m "a b" "x" "ab" && m "a.b" "q" "a.b" && !m "a.b" "q" "axb"

#guard ((compile "(\\w+)@(\\w+)" "").bind fun r => replace r "joe@ex and al@foo" "$2:$1").toOption ==
  some "ex:joe and foo:al"
#guard ((compile "a*?" "").bind fun r => replace r "aaa" "b").toOption.isNone
#guard (compile "[z-a]" "").toOption.isNone && (compile "a{3,2}" "").toOption.isNone &&
  (compile "(a" "").toOption.isNone && (compile "a" "g").toOption.isNone

end LeanRDF.Tests.RegexTests
