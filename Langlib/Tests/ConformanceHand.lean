import Langlib.Tests.Conformance
import Langlib.Languages.Brainfuck.Semantics

/-!
# The conformance suite, hand-written

`Langlib/Tests/Conformance.lean` runs the twenty conformance programs
through the Turpentine reference interpreter and through every bespoke
backend. Those runs test the *compilers*: they say the backend preserved
whatever the reference interpreter does.

This file runs the other half. Each program here was written **by hand**
in the target language, against that language as its specification
documents it, and is run on the target's own interpreter against the same
expected output. Nothing about it came from the Turpentine source except
the specification of what it must print.

Where both halves exist for a program, they are two independent
implementations of one written-down answer, so a disagreement is a real
finding rather than a golden file drifting.

Coverage is partial and grows language by language; `docs/conformance.md`
carries the matrix and the reasons for the gaps. The commonest reason is
arithmetic range: brainfuck's cells hold one byte, so a program whose
intermediate values pass 255 needs multi-byte arithmetic that the
conformance programs were not written to require.
-/

namespace Langlib.Tests.ConformanceHand

open Langlib.Common

/-- The expected output of the conformance program called `name`, or `none`
if there is no such program. Keeping the expectation in one place is the
point of the suite: a hand-written implementation is checked against the
same string the compiled one is. -/
def expectedOf (name : String) : Option String :=
  (Conformance.programs.find? (fun p => p.name == name)).map (fun p => p.output)

/-- Cases for one language's hand-written directory. A name with no
conformance program is reported as a failing case rather than skipped, so a
typo cannot quietly shrink the suite. -/
def cases (dir : String) (ext : String) (names : List String) : List TestCase :=
  names.map fun n =>
    match expectedOf n with
    | some out =>
      { name := n
        source := .file s!"Langlib/Examples/{dir}/suite/{n}.{ext}"
        expect := .outputs out
        fuel := Conformance.fuel }
    | none =>
      { name := s!"{n} (no such conformance program)"
        source := .inline ""
        expect := .outputs "this case fails on purpose: fix the name" }

/-- Brainfuck, on the default EOF convention. None of these programs reads,
so the convention does not matter; it is named to keep the runner honest. -/
def brainfuck : Suite where
  name := "conformance: brainfuck by hand"
  run := Langlib.Brainfuck.run {}
  cases := cases "Brainfuck" "b" ["hello", "triangle", "count", "fib"]

def suites : List Suite := [brainfuck]

end Langlib.Tests.ConformanceHand
