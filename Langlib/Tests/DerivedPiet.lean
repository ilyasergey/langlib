import Langlib.Common.TestHarness
import Langlib.Computability.Derived

/-!
Executable checks for the certified Turpentine-to-Piet compiler.

`derivedPiet.correct` supplies the proof. These tests exercise the concrete
composition: the shared URM pass, the image generator, the real `evalGrid`
evaluator walking codels with its own DP/CC rules and white slides, and the
decimal decoding of what the image prints.

The images are large — every command is one codel and every literal is
built from one-codel pushes — so the cases are small and the fuel is
generous.
-/

namespace Langlib.Tests.DerivedPiet

open Langlib.Common
open Langlib.Computability

def runCertified (src : String) (_input : Input) (fuel : Nat) :
    Except String RunResult := do
  let prog ← derivedPiet.compileSource src
  let result := ProgLang.run (L := PietLang) prog derivedPiet.encodeInput fuel
  match derivedPiet.decodeOutput result.output with
  | none => throw "the compiled image's output did not decode"
  | some n => return { output := (toString n).toUTF8, exit := result.exit }

def suite : Suite where
  name := "turpentine -> piet (certified), decoded answer"
  run := runCertified
  cases :=
    [ { name := "default zero", fuel := 1_000_000,
        source := .inline "var answer : int;", expect := .outputs "0" }
    , { name := "constant", fuel := 1_000_000,
        source := .inline "var answer : int; answer := 2;", expect := .outputs "2" }
    , { name := "rejects printing", source := .inline
          "var answer : int; println(1);",
        expect := .parseError "outside the certified URM fragment" }
    ]

def suites : List Suite := [suite]

end Langlib.Tests.DerivedPiet
