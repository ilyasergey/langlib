import Langlib.Common.TestHarness
import Langlib.Languages.Turpentine.Compile.Derived

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
open Langlib.Turpentine.Compile (derivedThue)

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

/-- What `lake exe turpentine compile --to thue --tc` writes, read back.
The CLI emits concrete syntax and the Thue runner parses it, so the emitted
file is the program the theorem is about only if `Prog.render` inverts
`parse` on what the compiler generates. -/
def renderRoundTrip (src : String) (_input : Input) (_fuel : Nat) :
    Except String RunResult := do
  let prog ← derivedThue.compileSource src
  let prog' ← Langlib.Thue.parse (Langlib.Thue.Prog.render prog)
  if prog' == prog then
    return { output := "ok".toUTF8, exit := .halted }
  else
    return { exit := .error "the rendered rulebase did not parse back unchanged" }

def renderSuite : Suite where
  name := "turpentine -> thue (certified), rendered text parses back"
  run := renderRoundTrip
  cases :=
    [ { name := "default zero", source := .inline "var answer : int;",
        expect := .outputs "ok" }
    , { name := "constant", source := .inline "var answer : int; answer := 2;",
        expect := .outputs "ok" }
    ]

def suites : List Suite := [suite, renderSuite]

end Langlib.Tests.DerivedThue
