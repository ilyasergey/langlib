import Langlib.Common.TestHarness
import Langlib.Languages.Ook.Semantics

/-!
Golden tests for the Ook! interpreter: the examples (whose expected outputs
equal those of the brainfuck originals they were generated from, pinning the
isomorphism on real programs), inline programs, all four parse errors, and a
mechanical brainfuck → Ook! → run round trip.
-/

namespace Langlib.Tests.Ook

open Langlib.Common
open Langlib.Ook (run parse render)

private def ex (f : String) : Source :=
  .file s!"Langlib/Examples/Ook/{f}"

/-- Tests under the default configuration (EOF leaves the cell unchanged). -/
def suite : Suite where
  name := "ook"
  run := run {}
  cases :=
    [ { name := "hello example (translated from hello.b)", source := ex "hello.ook",
        expect := .outputs "Hello World!\n" }
    , { name := "alphabet example (translated from alphabet.b)",
        source := ex "alphabet.ook",
        expect := .outputs "ABCDEFGHIJKLMNOPQRSTUVWXYZ\n" }
    , { name := "increment then output", source := .inline "Ook. Ook. Ook! Ook.",
        expect := .outputsBytes (ByteArray.mk #[1]) }
    , { name := "input copies byte (like brainfuck ,.)",
        source := .inline "Ook. Ook! Ook! Ook.", input := "A",
        expect := .outputs "A" }
    , { name := "line breaks ignored",
        source := .inline "Ook.\nOok.\n\nOok!\nOok.", expect := .outputsBytes (ByteArray.mk #[1]) }
    , { name := "empty program", source := .inline "  \n ",
        expect := .outputs "" }
    , { name := "infinite loop diverges (+[])",
        source := .inline "Ook. Ook. Ook! Ook? Ook? Ook!",
        fuel := 10_000, expect := .diverges }
    , { name := "pointer left of zero", source := .inline "Ook? Ook.",
        expect := .runtimeError "left of cell 0" }
    , { name := "odd number of Ooks", source := .inline "Ook. Ook. Ook!",
        expect := .parseError "odd number of Ook words (3)" }
    , { name := "non-Ook word", source := .inline "Ook. Ook. banana",
        expect := .parseError "'banana' at 1:11 is not an Ook! word" }
    , { name := "prose is not a comment", source := .inline "Hello Ook. Ook.",
        expect := .parseError "not an Ook! word" }
    , { name := "banana pair", source := .inline "Ook. Ook. Ook? Ook?",
        expect := .parseError "banana" }
    , { name := "unmatched open loop", source := .inline "Ook. Ook. Ook! Ook?",
        expect := .parseError "unmatched 'Ook! Ook?' at 1:11 (token 3)" }
    , { name := "unmatched close loop", source := .inline "Ook? Ook!",
        expect := .parseError "unmatched 'Ook? Ook!' at 1:1 (token 1)" }
    ]

/-- Tests under `--eof zero` (inherited from brainfuck). -/
def suiteEofZero : Suite where
  name := "ook (eof zero)"
  run := run { eof := .zero }
  cases :=
    [ { name := "cat example (translated from cat.b)", source := ex "cat.ook",
        input := "Ook ook?", expect := .outputs "Ook ook?" }
    ]

/-- Round-trip suite: each case's source is *brainfuck*; it is translated to
Ook! with `render`, parsed back with `parse`, and run on the brainfuck core.
This spot-checks the isomorphism mechanically, in both directions. -/
def suiteRoundtrip : Suite where
  name := "ook (bf → ook → bf round trip)"
  run := fun bfSrc input fuel => do
    let ookSrc ← Langlib.Ook.ofBrainfuck bfSrc
    let prog ← parse ookSrc
    return Langlib.Brainfuck.evalProg {} prog input fuel
  cases :=
    [ { name := "hello.b via ook", source := .file "Langlib/Examples/Brainfuck/hello.b",
        expect := .outputs "Hello World!\n" }
    , { name := "countdown.b via ook",
        source := .file "Langlib/Examples/Brainfuck/countdown.b",
        expect := .outputs "9876543210\n" }
    , { name := ",. via ook", source := .inline ",.", input := "Z",
        expect := .outputs "Z" }
    ]

def suites : List Suite := [suite, suiteEofZero, suiteRoundtrip]

end Langlib.Tests.Ook
