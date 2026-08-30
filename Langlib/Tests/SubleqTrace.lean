import Langlib.Common.TestHarness
import Langlib.Languages.Subleq
import Langlib.Languages.Turpentine

/-!
Golden tests for subleq's trace semantics, and for the claim its own
behavioural proof will make.

Two suites, on the pattern of `Langlib/Tests/WhitespaceTrace.lean` and
`Langlib/Tests/TurpentineTrace.lean`.

* **subleq traces** pins the interleaving, which is the one thing the two
  `TraceLang` laws deliberately do not determine: both are satisfied by a
  trace that reports every read before every write, and a `RunResult` cannot
  tell the two apart. The runner re-checks both laws on each run before
  reporting, so the tests and `Langlib/Languages/Subleq/Trace.lean` cannot
  drift apart.

* **turpentine vs subleq traces** compares a program's reference run against
  its hand-written subleq compilation, event for event. This one is a
  genuine surprise worth pinning: subleq prints integers through the
  `printint` runtime routine, which builds a decimal numeral by repeated
  doubling on top of a self-modifying calling convention, and it *still*
  emits exactly the bytes `Value.render` does. `encodeTrace` for the subleq
  backend is the identity, as `docs/certified-compilation.md` §1.4 claims
  and nothing until now checked.
-/

namespace Langlib.Tests.SubleqTrace

open Langlib.Common

private def ex (f : String) : Source :=
  .file s!"Langlib/Examples/Subleq/{f}"

private def renderEvent : Event → String
  | .inp b => s!" <{b.toNat}"
  | .out b => s!" >{b.toNat}"

private def renderExit : Exit → String
  | .halted => "halted"
  | .outOfFuel => "outOfFuel"
  | .error _ => "error"

private def render (e : Exit) (t : Trace) : ByteArray :=
  (renderExit e ++ " |" ++ String.join (t.map renderEvent)).toUTF8

/-- Assemble and run, reporting the run's trace as its output. The two
`TraceLang` laws are re-checked on this run before reporting. -/
def run (src : String) (input : Input) (fuel : Nat) : Except String RunResult := do
  let prog ← Langlib.Subleq.assemble src
  let r := Langlib.Subleq.evalProg prog input fuel
  let t := Langlib.Subleq.evalTrace prog input fuel
  if t.outputs != r.output.toList then
    throw "trace_outputs violated: the events disagree with the run's output"
  if !(t.inputs.isPrefixOf input.remaining) then
    throw "trace_inputs violated: the events read what the stream did not have"
  return { output := render r.exit t }

/-- Run the source through the reference interpreter and through the
hand-written subleq backend, and report the trace only if they agree. -/
def runBoth (src : String) (input : Input) (fuel : Nat) : Except String RunResult := do
  let p ← Langlib.Turpentine.parse src
  let _ ← (Langlib.Turpentine.checkProgram p).mapError ("type error: " ++ ·)
  let ref := Langlib.Turpentine.evalProgram p input fuel
  let refT := Langlib.Turpentine.evalTrace p input fuel
  let sq ← Langlib.Turpentine.Compile.Subleq.compile p
  let sqR := Langlib.Subleq.evalProg sq input fuel
  let sqT := Langlib.Subleq.evalTrace sq input fuel
  if ref.exit != sqR.exit then
    throw s!"exits differ: {repr ref.exit} vs {repr sqR.exit}"
  if refT != sqT then
    throw s!"traces differ:\n  turpentine {String.join (refT.map renderEvent)}\n  \
      subleq     {String.join (sqT.map renderEvent)}"
  return { output := render ref.exit refT }

def traces : Suite where
  name := "subleq traces"
  run := run
  cases :=
    [ { name := "a program that only computes has no events",
        source := .inline "a a ?+3  Z Z -1  a: 5 Z: 0",
        expect := .outputs "halted |" }
    , { name := "one byte out", source := .inline "b -1 ?+1  Z Z -1  b: 65 Z: 0",
        expect := .outputs "halted | >65" }
    , { name := "hello example", source := ex "hello.sq",
        expect := .outputs
          "halted | >72 >101 >108 >108 >111 >44 >32 >87 >111 >114 >108 >100 >33 >10" }
    , { name := "countdown example", source := ex "countdown.sq",
        expect := .outputs
          "halted | >57 >56 >55 >54 >53 >52 >51 >50 >49 >48 >10" }
      -- The interleaving, which no `RunResult` can express.
    , { name := "cat alternates read and write", source := ex "cat.sq", input := "hi",
        expect := .outputs "halted | <104 >104 <105 >105" }
    , { name := "a read is one event", source := .inline "-1 c ?+1  c -1 ?+1  Z Z -1  c: 0 Z: 0",
        input := "Q", expect := .outputs "halted | <81 >81" }
      -- Reading at end of input consumes nothing, so it records nothing.
    , { name := "a read at end of input records no event",
        source := .inline "-1 c ?+1  Z Z -1  c: 0 Z: 0",
        input := "", expect := .outputs "halted |" }
    ]

def crossCheck : Suite where
  name := "turpentine vs subleq traces"
  run := runBoth
  cases :=
    [ { name := "printByte emits the same byte",
        source := .inline "var answer: int; printByte(65);",
        fuel := 2_000_000, expect := .outputs "halted | >65" }
    , { name := "printint agrees with Value.render on a negative int",
        source := .inline "var answer: int; println(-12345);",
        fuel := 2_000_000, expect := .outputs "halted | >45 >49 >50 >51 >52 >53 >10" }
    , { name := "readInt agrees on what it consumed",
        source := .inline "var answer: int; answer := readInt(); println(answer * 2);",
        input := "21\n", fuel := 2_000_000,
        expect := .outputs "halted | <50 <49 <10 >52 >50 >10" }
    ]

def suites : List Suite := [traces, crossCheck]

end Langlib.Tests.SubleqTrace
