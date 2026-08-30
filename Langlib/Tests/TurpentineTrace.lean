import Langlib.Common.TestHarness
import Langlib.Languages.Turpentine
import Langlib.Languages.Whitespace

/-!
Golden tests for Turpentine's trace semantics, and for the one thing the
behavioural compiler proof is going to claim.

Two suites.

* **turpentine traces** pins the interleaving of a Turpentine run, the same
  way `Langlib/Tests/WhitespaceTrace.lean` does for the target. As there, the
  runner re-checks on each run the two properties
  `Langlib/Languages/Turpentine/Trace.lean` proves, so the tests and the
  theorems cannot drift apart.

* **turpentine vs whitespace traces** runs a program through the reference
  interpreter and through the hand-written whitespace backend and insists
  the two performed *the same I/O events, in the same order*. That is
  `encodeTrace = id`, executed. `docs/PLAN.md` Stage 6 aims to prove it over
  a fragment; until then these cases are the evidence, and they are also
  what would catch the claim being false before a proof is attempted.

The known divergence is `readByte` at end of input: Turpentine yields `-1`
and carries on, whitespace's `readchar` raises. `cat.turp` is here to pin
exactly that, by stopping short of EOF where the two agree.
-/

namespace Langlib.Tests.TurpentineTrace

open Langlib.Common

private def ex (f : String) : Source :=
  .file s!"Langlib/Examples/Turpentine/{f}"

private def renderEvent : Event → String
  | .inp b => s!" <{b.toNat}"
  | .out b => s!" >{b.toNat}"

private def renderExit : Exit → String
  | .halted => "halted"
  | .outOfFuel => "outOfFuel"
  | .error _ => "error"

private def render (e : Exit) (t : Trace) : ByteArray :=
  (renderExit e ++ " |" ++ String.join (t.map renderEvent)).toUTF8

/-- Parse, type-check and run, reporting the run's trace as its output.
The two properties proved in `Turpentine/Trace.lean` are re-checked here. -/
def run (src : String) (input : Input) (fuel : Nat) : Except String RunResult := do
  let p ← Langlib.Turpentine.parse src
  let _ ← (Langlib.Turpentine.checkProgram p).mapError ("type error: " ++ ·)
  let r := Langlib.Turpentine.evalProgram p input fuel
  let t := Langlib.Turpentine.evalTrace p input fuel
  if t.outputs != r.output.toList then
    throw "the trace's output events disagree with the run's output"
  if !(t.inputs.isPrefixOf input.remaining) then
    throw "the trace's input events read what the stream did not have"
  return { output := render r.exit t }

/-- Run the source twice — reference interpreter, and hand-written
whitespace backend — and report the trace only if they agree. -/
def runBoth (src : String) (input : Input) (fuel : Nat) : Except String RunResult := do
  let p ← Langlib.Turpentine.parse src
  let _ ← (Langlib.Turpentine.checkProgram p).mapError ("type error: " ++ ·)
  let ref := Langlib.Turpentine.evalProgram p input fuel
  let refT := Langlib.Turpentine.evalTrace p input fuel
  let ws ← Langlib.Turpentine.Compile.Whitespace.compile p
  let wsR := Langlib.Whitespace.evalProg ws input fuel
  let wsT := Langlib.Whitespace.evalTrace ws input fuel
  if ref.exit != wsR.exit then
    throw s!"exits differ: {repr ref.exit} vs {repr wsR.exit}"
  if refT != wsT then
    throw s!"traces differ:\n  turpentine {String.join (refT.map renderEvent)}\n  \
      whitespace {String.join (wsT.map renderEvent)}"
  return { output := render ref.exit refT }

def traces : Suite where
  name := "turpentine traces"
  run := run
  cases :=
    [ { name := "a program that only computes has no events",
        source := .inline "var answer: int; answer := 6 * 7;",
        expect := .outputs "halted |" }
    , { name := "print renders an int in decimal",
        source := .inline "var answer: int; print(-42);",
        expect := .outputs "halted | >45 >52 >50" }
    , { name := "print renders a bool as a word",
        source := .inline "var answer: int; print(1 < 2);",
        expect := .outputs "halted | >116 >114 >117 >101" }
    , { name := "println adds the newline as its own event",
        source := .inline "var answer: int; println(7);",
        expect := .outputs "halted | >55 >10" }
    , { name := "printByte emits one byte",
        source := .inline "var answer: int; printByte(65);",
        expect := .outputs "halted | >65" }
    , { name := "readInt consumes the whole line, terminator included",
        source := .inline "var answer: int; answer := readInt(); print(answer);",
        input := "12\n", expect := .outputs "halted | <49 <50 <10 >49 >50" }
    , { name := "readByte consumes exactly one byte",
        source := .inline "var answer: int; answer := readByte(); print(answer);",
        input := "AB", expect := .outputs "halted | <65 >54 >53" }
    , { name := "readByte at end of input consumes nothing and yields -1",
        source := .inline "var answer: int; answer := readByte(); print(answer);",
        input := "", expect := .outputs "halted | >45 >49" }
    , { name := "echo interleaves read and write",
        source := .inline
          "var answer: int; var i: int; var c: int; i := 0; \
           while i < 2 { c := readByte(); printByte(c); i := i + 1; }",
        input := "hi", expect := .outputs "halted | <104 >104 <105 >105" }
    ]

def crossCheck : Suite where
  name := "turpentine vs whitespace traces"
  run := runBoth
  cases :=
    [ { name := "hello example", source := ex "hello.turp",
        expect := .outputs
          "halted | >72 >101 >108 >108 >111 >44 >32 >84 >117 >114 >112 >101 >110 \
           >116 >105 >110 >101 >33 >10" }
    , { name := "print of an int agrees byte for byte",
        source := .inline "var answer: int; println(-12345);",
        expect := .outputs "halted | >45 >49 >50 >51 >52 >53 >10" }
    , { name := "print of a bool agrees byte for byte",
        source := .inline "var answer: int; print(2 < 1); print(1 < 2);",
        expect := .outputs "halted | >102 >97 >108 >115 >101 >116 >114 >117 >101" }
    , { name := "readInt agrees on what it consumed",
        source := .inline "var answer: int; answer := readInt(); println(answer * 2);",
        input := "21\n", expect := .outputs "halted | <50 <49 <10 >52 >50 >10" }
    , { name := "two reads and two writes, interleaved",
        source := .inline
          "var answer: int; var a: int; var b: int; \
           a := readInt(); println(a); b := readInt(); println(b);",
        input := "3\n4\n",
        expect := .outputs "halted | <51 <10 >51 >10 <52 <10 >52 >10" }
    , { name := "echo, short of end of input",
        source := .inline
          "var answer: int; var i: int; var c: int; i := 0; \
           while i < 3 { c := readByte(); printByte(c); i := i + 1; }",
        input := "cat", expect := .outputs "halted | <99 >99 <97 >97 <116 >116" }
    ]

def suites : List Suite := [traces, crossCheck]

end Langlib.Tests.TurpentineTrace
