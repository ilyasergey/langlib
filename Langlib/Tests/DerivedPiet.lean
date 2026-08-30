import Langlib.Common.TestHarness
import Langlib.Languages.Turpentine.Compile.Derived
import Langlib.Languages.Piet.Semantics

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
open Langlib.Turpentine.Compile (derivedPiet)

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

/-- What `lake exe turpentine compile --to piet --tc` actually does, and
what `--via piet` runs: compile to a grid, *paint it as a PPM*, and hand
that text to Piet's own parse-and-run. The suite above runs the grid
directly, so it never touches the renderer; this one does, and so it fails
if `Grid.toImage` and `parseGrid` ever stop being inverse.

Unlike `runCertified`, the answer here is whatever the image prints, which
for `URMPiet` images is the decimal answer already — no decoding step. -/
def runRendered (src : String) (input : Input) (fuel : Nat) :
    Except String RunResult := do
  let prog ← derivedPiet.compileSource src
  Langlib.Piet.run {} prog.toImage.toPpm3 input fuel

def renderedSuite : Suite where
  name := "turpentine -> piet (certified), emitted PPM re-parsed and run"
  run := runRendered
  cases :=
    [ { name := "default zero", fuel := 1_000_000,
        source := .inline "var answer : int;", expect := .outputs "0" }
    , { name := "constant", fuel := 1_000_000,
        source := .inline "var answer : int; answer := 2;", expect := .outputs "2" }
    , { name := "sum", fuel := 5_000_000,
        source := .inline "var answer : int; var b : int; answer := 2; b := 3; answer := answer + b;",
        expect := .outputs "5" }
    ]

def suites : List Suite := [suite, renderedSuite]

end Langlib.Tests.DerivedPiet
