import Langlib.Common.TestHarness
import Langlib.Languages.Thue.Semantics

/-!
Golden tests for the Thue interpreter: the examples under the default
deterministic strategy, input via `:::`, output via `~`, erasing rules,
halting, divergence, seeded-random reproducibility, and parse errors.

`--final-state` cases observe pure rewriters through the langlib extension
that appends the final state to the output on a normal halt.
-/

namespace Langlib.Tests.Thue

open Langlib.Common
open Langlib.Thue (run Strategy)

private def ex (f : String) : Source :=
  .file s!"Langlib/Examples/Thue/{f}"

/-- Tests under the default configuration (deterministic `first` strategy:
first rule in program order, leftmost occurrence). -/
def suite : Suite where
  name := "thue"
  run := run {}
  cases :=
    [ { name := "hello example", source := ex "hello.t",
        expect := .outputs "Hello World!\n" }
    , { name := "increment example halts silently", source := ex "increment.t",
        expect := .outputs "" }
    , { name := "truth-machine example on 0", source := ex "truth.t",
        input := "0", expect := .outputs "0\n" }
    , { name := "truth-machine example on 1", source := ex "truth.t",
        input := "1", fuel := 10_000, expect := .diverges }
    , { name := "parity example on 111", source := ex "parity.t",
        input := "111", expect := .outputs "odd\n" }
    , { name := "parity example on 1111", source := ex "parity.t",
        input := "1111", expect := .outputs "even\n" }
    , { name := "parity example at end of input", source := ex "parity.t",
        expect := .outputs "even\n" }
    , { name := "first matching rule wins",
        source := .inline "a::=~first\na::=~second\n::=\na",
        expect := .outputs "first\n" }
    , { name := "output of bare ~ is a newline", source := .inline "a::=~\n::=\na",
        expect := .outputs "\n" }
    , { name := "terminator rhs is ignored",
        source := .inline "a::=~yes\n::=~ignored\na",
        expect := .outputs "yes\n" }
    , { name := "blank lines in the rulebase are skipped",
        source := .inline "a::=~hi\n\n::=\na",
        expect := .outputs "hi\n" }
    , { name := "CRLF line endings are normalised",
        source := .inline "a::=~hi\r\n::=\r\na\r\n",
        expect := .outputs "hi\n" }
    , { name := "halts when no lhs occurs", source := .inline "a::=b\n::=\nxyz",
        expect := .outputs "" }
    , { name := "growing state diverges", source := .inline "a::=aa\n::=\na",
        fuel := 5_000, expect := .diverges }
    , { name := "junk line in the rulebase", source := .inline "a::=b\nnonsense\n::=\nx",
        expect := .parseError "line 2" }
    , { name := "missing terminator", source := .inline "a::=b",
        expect := .parseError "terminator" }
    ]

/-- Tests under `--final-state` (langlib extension: on a normal halt the
final state and a newline are appended to the output), which makes pure
rewriters observable. -/
def suiteFinalState : Suite where
  name := "thue (--final-state)"
  run := run { finalState := true }
  cases :=
    [ { name := "increment example result", source := ex "increment.t",
        expect := .outputs "10000000000\n" }
    , { name := "empty rhs erases lhs", source := .inline "a::=\n::=\nbab",
        expect := .outputs "bb\n" }
    , { name := "leftmost occurrence is rewritten", source := .inline "aa::=b\n::=\naaa",
        expect := .outputs "ba\n" }
    , { name := "rhs may contain ::=", source := .inline "a::=b::=c\n::=\na",
        expect := .outputs "b::=c\n" }
    , { name := "::: substitutes an input line", source := .inline "x::=:::\n::=\n<x>",
        input := "hi\n", expect := .outputs "<hi>\n" }
    , { name := "::: at end of input substitutes nothing",
        source := .inline "x::=:::\n::=\n<x>",
        expect := .outputs "<>\n" }
    ]

/-- The output-order program used to pin down the random strategy: under the
deterministic strategy it prints `A` then `B`; seed 0 happens to pick `b`
first. Running the same case twice checks that a seed fully determines the
run. -/
private def abProg : String := "a::=~A\nb::=~B\n::=\nab"

/-- Tests under `--strategy random --seed 0`. -/
def suiteRandom0 : Suite where
  name := "thue (random, seed 0)"
  run := run { strategy := .random 0 }
  cases :=
    [ { name := "seed 0 picks b before a", source := .inline abProg,
        expect := .outputs "B\nA\n" }
    , { name := "same seed, same run", source := .inline abProg,
        expect := .outputs "B\nA\n" }
    , { name := "hello example (single match, any strategy)",
        source := ex "hello.t", expect := .outputs "Hello World!\n" }
    ]

/-- Tests under `--strategy random --seed 42`. -/
def suiteRandom42 : Suite where
  name := "thue (random, seed 42)"
  run := run { strategy := .random 42 }
  cases :=
    [ { name := "seed 42 scrambles abcd reproducibly",
        source := .inline "a::=~A\nb::=~B\nc::=~C\nd::=~D\n::=\nabcd",
        expect := .outputs "C\nD\nA\nB\n" }
    , { name := "increment example is confluent", source := ex "increment.t",
        expect := .outputs "" }
    ]

def suites : List Suite := [suite, suiteFinalState, suiteRandom0, suiteRandom42]

end Langlib.Tests.Thue
