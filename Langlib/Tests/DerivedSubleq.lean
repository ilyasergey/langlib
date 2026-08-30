import Langlib.Common.TestHarness
import Langlib.Languages.Turpentine.Compile.Derived
import Langlib.Languages.Subleq.Semantics

/-!
Differential tests for the certified Turpentine-to-subleq compiler.

`derivedSubleq.correct` already *proves* that the compiled program's
decoded answer equals the source program's. These tests check the same
thing by running both, which is worth doing for a reason the proof cannot
cover: the theorem talks about `decodeOutput` applied to the output bytes,
and it is the pairing of that function with the emitted program that a
reader has to trust. Running both ends and comparing exercises the actual
executables, the renderer, and the subleq parser as well as the compiler.

The answer convention differs from Whitespace's. Subleq's only output
primitive writes one byte, so `decodeOutput` counts bytes: an answer of
`n` is `n` bytes of output. That makes the encoding cheap to emit and
expensive to read, which is the right trade for a compiler that exists to
be proved rather than to be fast.
-/

namespace Langlib.Tests.DerivedSubleq

open Langlib.Common
open Langlib.Computability
open Langlib.Turpentine.Compile (derivedSubleq)

/-- Compile Turpentine source through the certified subleq compiler and run
the result, reporting the decoded answer as decimal so a golden test can
name it. Parse and fragment errors surface as `Except.error`. -/
def runCertified (src : String) (input : Input) (fuel : Nat) :
    Except String RunResult := do
  let p ← Turpentine.parse src
  let prog ← derivedSubleq.compile p
  let r := Langlib.Subleq.evalProg prog input fuel
  match derivedSubleq.decodeOutput r.output with
  | none => throw "the compiled program's output did not decode"
  | some n => return { output := (toString n).toUTF8, exit := r.exit }

private def ex (f : String) : Source :=
  .file s!"Langlib/Examples/Turpentine/{f}"

/-- Every expected value here is the `answer` the Turpentine interpreter
computes for that program, checked independently. -/
def suite : Suite where
  name := "turpentine -> subleq (certified), decoded answer"
  run := runCertified
  cases :=
    [ { name := "sumsq example", source := ex "sumsq.turp",
        expect := .outputs "30" }
    , { name := "isqrt-tc example", source := ex "isqrt-tc.turp",
        expect := .outputs "4" }
    , { name := "fact-tc example", source := ex "fact-tc.turp",
        expect := .outputs "120" }
    , { name := "fib-tc example", source := ex "fib-tc.turp",
        expect := .outputs "55" }
    , { name := "constant", source := .inline "var answer : int; answer := 7;",
        expect := .outputs "7" }
    , { name := "zero", source := .inline "var answer : int;",
        expect := .outputs "0" }
    , { name := "multiplication", source := .inline
          "var answer : int; var i : int; i := 6; answer := i * 7;",
        expect := .outputs "42" }
    , { name := "conditional", source := .inline
          "var answer : int; var i : int; i := 3; if i < 5 { answer := 1; } else { answer := 2; }",
        expect := .outputs "1" }
      -- out of fragment, refused rather than mis-compiled
    , { name := "rejects printing", source := .inline
          "var answer : int; println(1);",
        expect := .parseError "outside the certified URM fragment" }
      -- arrays are inside the fragment since the dispatch-chain work
    , { name := "array element and length", source := .inline
          "var answer : int; var a : int[3]; a[1] := 4; answer := a[1] + len(a);",
        expect := .outputs "7" }
    ]

def suites : List Suite := [suite]

end Langlib.Tests.DerivedSubleq
