import Langlib.Common.TestHarness
import Langlib.Brainfuck.Semantics

/-!
Golden tests for the brainfuck interpreter, covering the examples, the three
EOF conventions, runtime errors, divergence, and parse errors.
-/

namespace Langlib.Tests.Brainfuck

open Langlib.Common
open Langlib.Brainfuck (run)

private def ex (f : String) : Source :=
  .file s!"Langlib/Examples/Brainfuck/{f}"

/-- Tests under the default configuration (EOF leaves the cell unchanged). -/
def suite : Suite where
  name := "brainfuck"
  run := run {}
  cases :=
    [ { name := "hello example", source := ex "hello.b",
        expect := .outputs "Hello World!\n" }
    , { name := "countdown example", source := ex "countdown.b",
        expect := .outputs "9876543210\n" }
    , { name := "add example", source := ex "add.b", input := "34",
        expect := .outputs "7" }
    , { name := "truth-machine example on 0", source := ex "truth.b",
        input := "0", expect := .outputs "0" }
    , { name := "truth-machine example on 1", source := ex "truth.b",
        input := "1", fuel := 100_000, expect := .diverges }
    , { name := "xkcd random example", source := ex "xkcd-random.b",
        expect := .outputs "4" }
    , { name := "alphabet example", source := ex "alphabet.b",
        expect := .outputs "ABCDEFGHIJKLMNOPQRSTUVWXYZ\n" }
    , { name := "quine example (Erik Bosman)", source := ex "quine.b",
        expect := .selfReproduces }
    , { name := "input copies byte", source := .inline ",.", input := "A",
        expect := .outputs "A" }
    , { name := "eof unchanged keeps cell", source := .inline "+++,.",
        expect := .outputsBytes (ByteArray.mk #[3]) }
    , { name := "cell wraparound", source := .inline "-.",
        expect := .outputsBytes (ByteArray.mk #[255]) }
    , { name := "nested loops clear", source := .inline "++++[>++++[-]<-]>.",
        expect := .outputsBytes (ByteArray.mk #[0]) }
    , { name := "empty program", source := .inline "no commands here",
        expect := .outputs "" }
    , { name := "infinite loop diverges", source := .inline "+[]",
        fuel := 10_000, expect := .diverges }
    , { name := "pointer left of zero", source := .inline "<",
        expect := .runtimeError "left of cell 0" }
    , { name := "unmatched open bracket", source := .inline "+[",
        expect := .parseError "unmatched '['" }
    , { name := "unmatched close bracket", source := .inline "+]\n]",
        expect := .parseError "unmatched ']' at 1:2" }
    ]

/-- Tests under `--eof zero`. -/
def suiteEofZero : Suite where
  name := "brainfuck (eof zero)"
  run := run { eof := .zero }
  cases :=
    [ { name := "cat example", source := ex "cat.b", input := "hello there",
        expect := .outputs "hello there" }
    , { name := "rev example", source := ex "rev.b", input := "stressed",
        expect := .outputs "desserts" }
    , { name := "eof stores zero", source := .inline "+++,.",
        expect := .outputsBytes (ByteArray.mk #[0]) }
    ]

/-- Tests under `--eof minus1`. -/
def suiteEofMinusOne : Suite where
  name := "brainfuck (eof minus1)"
  run := run { eof := .minusOne }
  cases :=
    [ { name := "eof stores 255", source := .inline ",.",
        expect := .outputsBytes (ByteArray.mk #[255]) }
    ]

def suites : List Suite := [suite, suiteEofZero, suiteEofMinusOne]

end Langlib.Tests.Brainfuck
