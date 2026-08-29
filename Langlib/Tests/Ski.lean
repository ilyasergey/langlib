import Langlib.Common.TestHarness
import Langlib.Languages.Ski.Semantics

/-!
Golden tests for the SKI interpreter. A run's observable behaviour is the
normal form it prints, so every case is a normal form, and the one term
without a normal form runs out of fuel instead.
-/

namespace Langlib.Tests.Ski

open Langlib.Common
open Langlib.Ski (run)

private def ex (f : String) : Source :=
  .file s!"Langlib/Examples/Ski/{f}"

def suite : Suite where
  name := "ski"
  run := run
  cases :=
    [ -- The examples.
      { name := "identity example: SKKI reduces to I",
        source := ex "identity.ski", expect := .outputs "I\n" }
    , { name := "booleans example: SK selects the second branch",
        source := ex "booleans.ski", expect := .outputs "I\n" }
    , { name := "flip example: the eliminated \\f\\x\\y.fyx swaps two arguments",
        source := ex "flip.ski", expect := .outputs "I\n" }
    , { name := "church example: two plus three has five S's",
        source := ex "church.ski", expect := .outputs "S(S(S(S(SK))))\n" }
    , { name := "omega example has no normal form", source := ex "omega.ski",
        fuel := 10_000, expect := .diverges }
      -- The three rules.
    , { name := "I x reduces to x", source := .inline "IK",
        expect := .outputs "K\n" }
    , { name := "K x y reduces to x", source := .inline "KSI",
        expect := .outputs "S\n" }
    , { name := "S x y z reduces to xz(yz)", source := .inline "SKKS",
        expect := .outputs "S\n" }
    , { name := "a combinator on its own is already normal",
        source := .inline "S", expect := .outputs "S\n" }
    , { name := "application associates to the left: KKSI is ((KK)S)I",
        source := .inline "KKSI", expect := .outputs "KI\n" }
    , { name := "brackets group an argument", source := .inline "K(KS)I",
        expect := .outputs "KS\n" }
    , { name := "normal order reduces under an argument that never runs",
        source := .inline "K I (KKK)", expect := .outputs "I\n" }
      -- Parse errors.
    , { name := "empty program", source := .inline "",
        expect := .parseError "empty program" }
    , { name := "unrecognised character", source := .inline "SXK",
        expect := .parseError "unrecognised character" }
    , { name := "unclosed bracket", source := .inline "S(KI",
        expect := .parseError "unclosed" }
    , { name := "unmatched bracket", source := .inline "SKI)",
        expect := .parseError "unmatched" }
    , { name := "empty brackets", source := .inline "S()K",
        expect := .parseError "empty parentheses" }
    ]

def suites : List Suite := [suite]

end Langlib.Tests.Ski
