import Langlib.Common.TestHarness
import Langlib.Computability.Deadfish

/-!
# Deadfish termination tests

These tests cover the exact fuel boundary and evaluate the direct halting
decision procedure.  The historical file name says "BoundedDeadfish", but
`Deadfish.no_boundedStorage` proves that the current `BoundedStorage`
interface has no witness for this evaluator.
-/

namespace Langlib.Tests.BoundedDeadfish

open Langlib.Common
open Langlib.Computability

/-- Parse a program and evaluate Deadfish's direct halting decision.  On the
positive branch, report the canonical witness `program length + 1`. -/
private def runDecision (src : String) (input : Input) (_fuel : Nat) :
    Except String RunResult := do
  let p ← Langlib.Deadfish.parse src
  match Deadfish.haltingDecidable p input with
  | isTrue _ =>
      return {
        output := s!"halts at fuel {p.length + 1}\n".toUTF8
        exit := .halted
      }
  | isFalse _ =>
      return { exit := .error "Deadfish halting decision returned false" }

def exactFuelSuite : Suite where
  name := "deadfish exact halting fuel"
  run := Langlib.Deadfish.run
  cases :=
    [ { name := "empty program has not halted at fuel 0",
        source := .inline "", fuel := 0, expect := .diverges }
    , { name := "empty program first halts at fuel 1",
        source := .inline "", fuel := 1, expect := .outputs "" }
    , { name := "one command has not halted at fuel 1",
        source := .inline "i", fuel := 1, expect := .diverges }
    , { name := "one command first halts at fuel 2",
        source := .inline "i", fuel := 2, expect := .outputs "" }
    , { name := "output command needs one final observation step",
        source := .inline "io", fuel := 2, expect := .diverges }
    , { name := "two commands first halt at fuel 3",
        source := .inline "io", fuel := 3, expect := .outputs "1\n" }
    , { name := "noise obeys the same exact boundary",
        source := .inline "xyz", fuel := 3, expect := .diverges }
    , { name := "noise halts one fuel later",
        source := .inline "xyz", fuel := 4, expect := .outputs "\n\n\n" }
    ]

def decisionSuite : Suite where
  name := "deadfish direct halting decision"
  run := runDecision
  cases :=
    [ { name := "empty program decision", source := .inline "",
        expect := .outputs "halts at fuel 1\n" }
    , { name := "four commands decision", source := .inline "iiso",
        expect := .outputs "halts at fuel 5\n" }
    , { name := "noise counts as commands", source := .inline "i o",
        expect := .outputs "halts at fuel 4\n" }
    , { name := "input does not affect the decision", source := .inline "diissisdo",
        input := "ignored input", expect := .outputs "halts at fuel 10\n" }
    ]

def suites : List Suite := [exactFuelSuite, decisionSuite]

end Langlib.Tests.BoundedDeadfish
