import LeanRDF.Canon.Sha256
import LeanRDF.Text.Hash

/-! # The fast SHA-256 of canonicalization agrees with the reference -/

namespace LeanRDF.Tests.Canon.Sha256

open LeanRDF

-- NIST vectors (FIPS 180-4 examples)
#guard Canon.sha256 "" == "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
#guard Canon.sha256 "abc" == "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
#guard Canon.sha256 "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq" ==
  "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"

/-- Inputs of every length from 0 to 200 bytes (every padding case, one to four blocks),
non-ASCII characters, and a long input. -/
def inputs : List String :=
  (List.range 201).map (fun n => String.ofList (List.replicate n 'x')) ++
  ["_:a <http://example.org/p> _:z .\n", "é", "日本語のテキスト", "\x00", "a\nb\r\n",
   String.join ((List.range 500).map toString)]

#guard inputs.all fun s => Canon.sha256 s == Hash.sha256 s

end LeanRDF.Tests.Canon.Sha256
