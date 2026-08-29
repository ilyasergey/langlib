import Langlib.Common.TestHarness
import Langlib.Computability.Befunge93

/-!
Tests for the explicitly bounded-stack, no-input, byte-celled Befunge-93
core.  The suite checks its operational restrictions and terminal behavior.
The declarations after the suite instantiate the proved halting decision
procedure on an immediate-halt program.
-/

namespace Langlib.Tests.BoundedBefunge93

open Langlib.Common
open Langlib.Computability
open Langlib.Computability.BoundedByteBefunge93

def suite : Suite where
  name := "bounded byte Befunge-93 core"
  run := run
  cases :=
    let cases : List TestCase :=
    [ { name := "immediate halt", source := .inline "@",
        expect := .outputs "" }
    , { name := "full stack can halt",
        source := .inline "1111111111111111@", expect := .outputs "" }
    , { name := "seventeenth push overflows the fixed stack",
        source := .inline "11111111111111111@",
        expect := .runtimeError "bounded byte Befunge-93 runtime error" }
    , { name := "empty pop yields zero", source := .inline "$@",
        expect := .outputs "" }
    , { name := "string mode uses the bounded byte stack",
        source := .inline "\"abc\"$$$@", expect := .outputs "" }
    , { name := "zero horizontal branch moves right",
        source := .inline "0_@", expect := .outputs "" }
    , { name := "left movement wraps around the torus",
        source := .inline "<@", fuel := 80, expect := .outputs "" }
    , { name := "bridge skips one cell", source := .inline "#@@",
        expect := .outputs "" }
    , { name := "self modification writes a byte cell",
        source := .inline "\"@\"80p  q", expect := .outputs "" }
    , { name := "put then get stays inside byte storage",
        source := .inline "\"A\"01p01g$@", expect := .outputs "" }
    , { name := "division by zero is an error", source := .inline "10/@",
        expect := .runtimeError "bounded byte Befunge-93 runtime error" }
    , { name := "modulo by zero is an error", source := .inline "10%@",
        expect := .runtimeError "bounded byte Befunge-93 runtime error" }
    , { name := "output is outside the no-I/O fragment",
        source := .inline ".@",
        expect := .runtimeError "bounded byte Befunge-93 runtime error" }
    , { name := "input is outside the no-input fragment",
        source := .inline "&@", input := "7",
        expect := .runtimeError "bounded byte Befunge-93 runtime error" }
    , { name := "random direction is outside the deterministic fragment",
        source := .inline "?@",
        expect := .runtimeError "bounded byte Befunge-93 runtime error" }
    , { name := "unsupported instruction is an error",
        source := .inline "q@",
        expect := .runtimeError "bounded byte Befunge-93 runtime error" }
    , { name := "two-cell horizontal loop diverges", source := .inline "><",
        fuel := 10_000, expect := .diverges }
    , { name := "ordinary loader still enforces width 80",
        source := .inline (String.ofList (List.replicate 81 '1')),
        expect := .parseError "only 80 wide" }
    , { name := "ordinary loader still enforces height 25",
        source := .inline (String.ofList (List.replicate 26 '\n')),
        expect := .parseError "only 25 tall" }
    ]
    cases.map fun c => { c with fuel := min c.fuel 10_000 }

def suites : List Suite := [suite]

/-- A program whose first cell is `@` and whose remaining cells are spaces. -/
private def immediateHalt : Program where
  cells y x :=
    if x.val = 0 ∧ y.val = 0 then
      ⟨64, by decide⟩
    else
      ⟨32, by decide⟩

private def emptyInput : Input := Input.ofString ""

theorem immediateHalt_halts :
    (evalProg immediateHalt emptyInput 1).isHalted = true := by
  native_decide

/-- The general bounded-storage search theorem recognizes the immediate
halt.  This uses the actual `BoundedStorage` witness; evaluating its full
astronomical bound is intentionally not part of the executable suite. -/
theorem immediateHalt_searches_true :
    boundedStorage.search immediateHalt emptyInput = true :=
  (boundedStorage.halts_iff_search immediateHalt emptyInput).mp
    ⟨1, immediateHalt_halts⟩

/-- The decidability corollary specializes to a concrete bounded byte
program and input. -/
noncomputable def immediateHaltDecision :
    Decidable (∃ fuel, (evalProg immediateHalt emptyInput fuel).isHalted = true) :=
  haltingDecidable immediateHalt emptyInput

end Langlib.Tests.BoundedBefunge93
