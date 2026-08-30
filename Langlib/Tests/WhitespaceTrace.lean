import Langlib.Common.TestHarness
import Langlib.Languages.Whitespace

/-!
Golden tests for whitespace's trace semantics.

`Langlib/Languages/Whitespace/Trace.lean` proves the two `TraceLang` laws, so
these tests are not what makes the instance lawful. They pin the thing the
laws deliberately do **not** determine: the *interleaving*. Both laws are
satisfied by a trace that reports every read before every write, and a
`RunResult` cannot tell the two apart, because it records the bytes that
came out and nothing about the bytes that went in. Only a golden trace can
say that `cat.ws` alternates.

Each case renders the run as an exit tag and the events in order, `<n` for
a byte consumed and `>n` for a byte emitted. Before rendering, `run` checks
the two laws on that very run: it is cheap, and it would catch a mismatch
between what the theorems are about (`evalTrace`) and what the tests are
about (the same function, run on real programs) if the two ever drifted.
-/

namespace Langlib.Tests.WhitespaceTrace

open Langlib.Common

private def ex (f : String) : Source :=
  .file s!"Langlib/Examples/Whitespace/{f}"

private def renderEvent : Event → String
  | .inp b => s!" <{b.toNat}"
  | .out b => s!" >{b.toNat}"

private def renderExit : Exit → String
  | .halted => "halted"
  | .outOfFuel => "outOfFuel"
  | .error _ => "error"

/-- Parse and run, reporting the run's trace as its output. The two
`TraceLang` laws are re-checked on this run before reporting. -/
def run (src : String) (input : Input) (fuel : Nat) : Except String RunResult := do
  let prog ← Langlib.Whitespace.parse src
  let r := Langlib.Whitespace.evalProg prog input fuel
  let t := Langlib.Whitespace.evalTrace prog input fuel
  if t.outputs != r.output.toList then
    throw "trace_outputs violated: the events disagree with the run's output"
  if !(t.inputs.isPrefixOf input.remaining) then
    throw "trace_inputs violated: the events read what the stream did not have"
  return { output := (renderExit r.exit ++ " |" ++ String.join (t.map renderEvent)).toUTF8 }

def suite : Suite where
  name := "whitespace traces"
  run := run
  cases :=
    [ -- A program that only computes has the empty trace.
      { name := "no I/O at all", source := .inline (Langlib.Whitespace.Prog.render
          #[.push 1, .push 2, .add, .drop, .halt]),
        expect := .outputs "halted |" }
      -- Output only: the trace is the output, one event per byte.
    , { name := "one character out", source := .inline (Langlib.Whitespace.Prog.render
          #[.push 65, .outChar, .halt]),
        expect := .outputs "halted | >65" }
    , { name := "outnum emits every digit of the numeral",
        source := .inline (Langlib.Whitespace.Prog.render #[.push (-42), .outNum, .halt]),
        expect := .outputs "halted | >45 >52 >50" }
      -- The interleaving, which no `RunResult` can express.
    , { name := "cat alternates read and write", source := ex "cat.ws", input := "hi",
        expect := .outputs "error | <104 >104 <105 >105" }
    , { name := "add reads both numerals before printing", source := ex "add.ws",
        input := "12\n30\n",
        expect := .outputs "halted | <49 <50 <10 <51 <48 <10 >52 >50 >10" }
      -- `readnum` consumes a whole line, newline included.
    , { name := "readnum consumes the line terminator", source := ex "add.ws",
        input := "1\n2\n", expect := .outputs "halted | <49 <10 <50 <10 >51 >10" }
    , { name := "readchar consumes exactly one byte", source := ex "greet.ws",
        input := "Bo\n",
        expect := .outputs
          "halted | <66 <111 <10 >72 >101 >108 >108 >111 >44 >32 >66 >111 >33 >10" }
      -- A run that stops early still reports what it did before stopping.
    , { name := "out of fuel keeps the events so far", source := ex "count.ws",
        fuel := 40, expect := .outputs "outOfFuel | >49 >10 >50 >10 >51 >10 >52 >10" }
    ]

def suites : List Suite := [suite]

end Langlib.Tests.WhitespaceTrace
