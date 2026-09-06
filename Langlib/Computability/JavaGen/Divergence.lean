import Langlib.Computability.JavaGen.Simulation

/-! # JavaGen: a source-realizable positive-cost infinite execution

This is a concrete divergence theorem for the small original loop example,
not yet divergence preservation for a universal compiler.
-/

namespace Langlib.Computability.JavaGen
open Langlib.JavaGen
open Langlib.Common

def loopProgram : Program :=
  { classes := [⟨"A", [⟨["B", "B", "A"], .var⟩]⟩, ⟨"B", []⟩]
    query := ⟨["A"], ["B", "A"]⟩ }

def loopMachine : Prepared :=
  { source := loopProgram
    closure :=
      [("A", [⟨⟨["A"], .var⟩, []⟩,
               ⟨⟨["B", "B", "A"], .var⟩, [⟨["B", "B", "A"], .var⟩]⟩]),
       ("B", [⟨⟨["B"], .var⟩, []⟩])] }

private instance : DecidableEq (Except String Prepared) := by
  intro a b
  cases a with
  | error x =>
    cases b with
    | error y => exact decidable_of_iff (x = y) (by simp)
    | ok _ => exact isFalse (by intro h; cases h)
  | ok x =>
    cases b with
    | error _ => exact isFalse (by intro h; cases h)
    | ok y => exact decidable_of_iff (x = y) (by simp)

/-- The ordinary validator constructs this machine from the example AST. -/
theorem loop_prepared : prepare loopProgram = .ok loopMachine := by decide +kernel

set_option maxRecDepth 10000 in
/-- The ordinary parser and validator accept the rendered example. -/
theorem loop_source_realized : parse loopProgram.render = .ok loopMachine := by decide +kernel

theorem loop_step : step loopMachine loopProgram.query =
    .next ⟨loopProgram.query, [["B", "B", "A"]]⟩ loopProgram.query := by decide

/-- Every finite budget is exhausted, independently of output decoding. -/
theorem loop_outOfFuel (fuel : Nat) : (evalPrepared loopMachine fuel).exit = .outOfFuel := by
  change (exec loopMachine fuel ⟨loopProgram.query, []⟩).2 = .outOfFuel
  exact exec_self_loop loopMachine loopProgram.query _ loop_step fuel []

end Langlib.Computability.JavaGen
