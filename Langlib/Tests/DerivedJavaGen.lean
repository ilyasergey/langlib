import Langlib.Common.TestHarness
import Langlib.Languages.Turpentine.Compile.Derived

/-! # The certified JavaGen backend, including its ordinary source round-trip

These checks execute the completeness witness and its byte decoder. They
check distinct answers, divergence and the closed-source restriction.
-/

namespace Langlib.Tests.DerivedJavaGen
open Langlib.Common Langlib.Computability
open Langlib.Turpentine.Compile (derivedJavaGen)

def runCertified (src : String) (_input : Input) (fuel : Nat) : Except String RunResult := do
  let p ← derivedJavaGen.compileSource src
  let parsed ← Langlib.JavaGen.parse (JavaGen.Source.sourceText p.source)
  unless parsed == p do throw "generated source changed the prepared artifact"
  let result := Langlib.JavaGen.evalPrepared parsed fuel
  if result.exit != .halted then return result
  let some answer := derivedJavaGen.decodeOutput result.output
    | throw "the compiled JavaGen proof record did not decode"
  return { result with output := (toString answer).toUTF8 }

def suite : Suite where
  name := "turpentine -> javagen (certified), rendered source and decoded answer"
  run := runCertified
  cases :=
    [ { name := "default zero", fuel := 2000000,
        source := .inline "var answer : int;", expect := .outputs "0" }
    , { name := "constant", fuel := 2000000,
        source := .inline "var answer : int := 2;", expect := .outputs "2" }
    , { name := "divergent self loop", fuel := 7,
        source := .inline "var answer : int; while answer == 0 { }",
        expect := .diverges }
    , { name := "rejects printing", source := .inline "var answer : int; println(1);",
        expect := .parseError "outside the certified URM fragment" }
    ]

def suites : List Suite := [suite]
end Langlib.Tests.DerivedJavaGen
