import Langlib.Common.TestHarness
import Langlib.Computability.Derived

/-!
Executable checks for the certified Turpentine-to-FRACTRAN compiler.

`derivedFractran.correct` supplies the proof. These tests exercise the concrete
composition, including the compiled artifact's input-dependent starting
integer, the real FRACTRAN interpreter, and final-power-of-two decoding.
-/

namespace Langlib.Tests.DerivedFractran

open Langlib.Common
open Langlib.Computability

def runCertified (src : String) (_input : Input) (fuel : Nat) :
    Except String RunResult := do
  let prog ← derivedFractran.compileSource src
  let result := ProgLang.run (L := FractranLang) prog derivedFractran.encodeInput fuel
  match derivedFractran.decodeOutput result.output with
  | none => throw "the compiled program's final power of two did not decode"
  | some n => return { output := (toString n).toUTF8, exit := result.exit }

def suite : Suite where
  name := "turpentine -> fractran (certified), decoded answer"
  run := runCertified
  cases :=
    [ { name := "default zero", fuel := 5_000_000,
        source := .inline "var answer : int;", expect := .outputs "0" }
    , { name := "constant", fuel := 5_000_000,
        source := .inline "var answer : int; answer := 2;", expect := .outputs "2" }
    , { name := "rejects printing", source := .inline
          "var answer : int; println(1);",
        expect := .parseError "outside the certified URM fragment" }
    ]

def suites : List Suite := [suite]

end Langlib.Tests.DerivedFractran
