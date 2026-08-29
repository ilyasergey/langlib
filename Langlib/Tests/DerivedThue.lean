import Langlib.Common.TestHarness
import Langlib.Computability.Derived

/-!
Executable checks for the certified Turpentine-to-Thue compiler.

`derivedThue.correct` supplies the proof. These tests exercise the concrete
composition: the shared URM pass, the rule generator, the real Thue rewriting
engine under its deterministic strategy, and the final-state decoder that
reads the unary run of register zero.

The generated rulebases are large and every counter is unary, so the cases
are deliberately tiny and the fuel is generous.
-/

namespace Langlib.Tests.DerivedThue

open Langlib.Common
open Langlib.Computability

def runCertified (src : String) (_input : Input) (fuel : Nat) :
    Except String RunResult := do
  let prog ← derivedThue.compileSource src
  let result := ProgLang.run (L := ThueLang) prog derivedThue.encodeInput fuel
  match derivedThue.decodeOutput result.output with
  | none => throw "the compiled program's final state did not decode"
  | some n => return { output := (toString n).toUTF8, exit := result.exit }

def suite : Suite where
  name := "turpentine -> thue (certified), decoded answer"
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

end Langlib.Tests.DerivedThue
