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

/-- What `lake exe turpentine compile --to fractran --tc` writes, read back.
A `.ft` file holds only the fractions, so the CLI puts the starting value in
a `#` comment header and repeats it in the run command it prints; this checks
that a file shaped like that parses back to the fractions compiled. -/
def renderRoundTrip (src : String) (_input : Input) (_fuel : Nat) :
    Except String RunResult := do
  let cp ← derivedFractran.compileSource src
  let text := s!"# starting value: {cp.start}\n" ++ Langlib.Fractran.Prog.render cp.code ++ "\n"
  let code ← Langlib.Fractran.parse text
  if code == cp.code then
    return { output := "ok".toUTF8, exit := .halted }
  else
    return { exit := .error "the rendered fractions did not parse back unchanged" }

def renderSuite : Suite where
  name := "turpentine -> fractran (certified), rendered text parses back"
  run := renderRoundTrip
  cases :=
    [ { name := "default zero", source := .inline "var answer : int;",
        expect := .outputs "ok" }
    , { name := "constant", source := .inline "var answer : int; answer := 2;",
        expect := .outputs "ok" }
    ]

def suites : List Suite := [suite, renderSuite]

end Langlib.Tests.DerivedFractran
