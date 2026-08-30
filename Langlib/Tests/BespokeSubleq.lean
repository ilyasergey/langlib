import Langlib.Common.TestHarness
import Langlib.Computability.BespokeSubleq
import Langlib.Languages.Subleq.Semantics
import Langlib.Languages.Turpentine.Semantics

/-!
Differential tests for the verified fragment of the hand-written
Turpentine-to-subleq backend.

`bespokeSubleq.correct` proves that a program the instance accepts halts with
an output that decodes to the source program's `answer`, and
`BespokeSubleq.backend_skipZero` and `BespokeSubleq.backend_printLit` prove
that the backend emits the images the simulation is about. So these tests are
not what makes the fragment inhabited; they are what checks the pieces the
theorem does not reach.

The theorem is stated against the pure interpreter core and against a program
already in abstract syntax. These cases start from source text, so they
exercise the parser and the type checker as well, and they compare the
compiled run against the reference run rather than against the decoded answer
alone.

Each accepting case checks three things: the decoded answer equals the
`answer` the Turpentine reference semantics computes, the compiled program's
output bytes equal the reference program's own output bytes, and the decoded
answer is the pinned value. The rejecting cases pin the fragment boundary, so
that a widening of the backend cannot silently widen the theorem.
-/

namespace Langlib.Tests.BespokeSubleq

open Langlib.Common
open Langlib.Computability

/-- The `answer` the Turpentine reference semantics leaves behind, which is
what `TurpentineHaltsWith` names and what both compilers have to reproduce. -/
def referenceAnswer (p : Turpentine.Program) (fuel : Nat) : Except String Nat := do
  let env₀ ← Turpentine.initEnv p
  let (st, exit) := Turpentine.exec fuel p.body { env := env₀, input := Input.ofString "" }
  match exit with
  | .halted =>
    match st.env["answer"]? with
    | some (.int n) =>
      if n < 0 then throw "the reference run left a negative 'answer'" else return n.toNat
    | some _ => throw "'answer' is not an int"
    | none => throw "the program has no variable named 'answer'"
  | .outOfFuel => throw "the reference run ran out of fuel"
  | .error m => throw s!"the reference run failed: {m}"

/-- Compile with `bespokeSubleq`, run the image, and report the decoded
answer as decimal, failing if it disagrees with the reference semantics. -/
def runBespoke (src : String) (_input : Input) (fuel : Nat) : Except String RunResult := do
  let p ← Turpentine.parse src
  let _ ← (Turpentine.checkProgram p).mapError ("type error: " ++ ·)
  let prog ← bespokeSubleq.compile p
  let want ← referenceAnswer p fuel
  let r := Langlib.Subleq.evalProg prog bespokeSubleq.encodeInput fuel
  match bespokeSubleq.decodeOutput r.output with
  | none => throw "the compiled program's output did not decode"
  | some n =>
    if n != want then
      throw s!"decoded {n}, but the Turpentine reference computes {want}"
    else
      let refOut := (Turpentine.evalProgram p (Input.ofString "") fuel).output
      if r.output != refOut then
        throw s!"the compiled program printed {r.output.size} bytes, \
          the reference printed {refOut.size}"
      else
        return { output := (toString n).toUTF8, exit := r.exit }

/-- The accepted shapes, with the answer each one is supposed to report. -/
def accepts : Suite where
  name := "turpentine -> subleq (bespoke, verified fragment), decoded answer"
  run := runBespoke
  cases :=
    [ { name := "printByte of a one-digit literal",
        source := .inline "var answer : int := 7;\nprintByte(answer);\n",
        expect := .outputs "7" }
    , { name := "printByte of a printable byte",
        source := .inline "var answer : int := 65;\nprintByte(answer);\n",
        expect := .outputs "65" }
    , { name := "printByte at the bottom of the range",
        source := .inline "var answer : int := 1;\nprintByte(answer);\n",
        expect := .outputs "1" }
    , { name := "printByte at the top of the range",
        source := .inline "var answer : int := 255;\nprintByte(answer);\n",
        expect := .outputs "255" }
    , { name := "an uninitialised answer and an empty body",
        source := .inline "var answer : int;\n",
        expect := .outputs "0" }
    ]

/-- The fragment boundary. Every case here is a program the backend itself
compiles happily; the instance refuses it because the proof does not cover
it, which is what makes the theorem an honest statement about the programs
it does accept. -/
def rejects : Suite where
  name := "turpentine -> subleq (bespoke), programs outside the verified fragment"
  run := runBespoke
  cases :=
    [ { name := "a literal of zero uses a different layout",
        source := .inline "var answer : int := 0;\nprintByte(answer);\n",
        expect := .parseError "outside the verified fragment" }
    , { name := "a literal above one byte",
        source := .inline "var answer : int := 256;\nprintByte(answer);\n",
        expect := .parseError "outside the verified fragment" }
    , { name := "a negative literal",
        source := .inline "var answer : int := -3;\nprintByte(answer);\n",
        expect := .parseError "outside the verified fragment" }
    , { name := "an assignment in the body",
        source := .inline "var answer : int;\nanswer := 7;\n",
        expect := .parseError "outside the verified fragment" }
    , { name := "decimal printing, which needs the printint routine",
        source := .inline "var answer : int := 7;\nprint(answer);\n",
        expect := .parseError "outside the verified fragment" }
    , { name := "a second variable",
        source := .inline "var answer : int := 7;\nvar i : int;\nprintByte(answer);\n",
        expect := .parseError "outside the verified fragment" }
    , { name := "printing a variable that is not the answer",
        source := .inline "var answer : int := 7;\nprintByte(7);\n",
        expect := .parseError "outside the verified fragment" }
    , { name := "a loop",
        source := .inline "var answer : int := 1;\nwhile answer < 3 { answer := answer + 1; }\n",
        expect := .parseError "outside the verified fragment" }
    ]

def suites : List Suite := [accepts, rejects]

end Langlib.Tests.BespokeSubleq
