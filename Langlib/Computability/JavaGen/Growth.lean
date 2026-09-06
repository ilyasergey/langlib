import Langlib.Computability.JavaGen.SweepProof

/-! # A source-realizable sweeping machine that grows its tape forever

Unlike the stationary loop, every completed sweep doubles the represented
word. Divergence is proved through the general positive-cost simulation;
the proof does not compare outputs or infer divergence from finite tests.
-/

namespace Langlib.Computability.JavaGen.Growth
open Langlib.JavaGen Langlib.Common

/-- One state and one symbol; every visit replaces a symbol with two copies. -/
def machine : Sweep.Machine 1 1 where
  initial := 0
  transition := fun _ a => (0, [a, a])
  boundary := fun _ => some 0

def source : Program := Sweep.program machine [0]

def prepared : Prepared := (prepare source).toOption.getD default

set_option maxRecDepth 10000 in
/-- Successful parsing of the ordinary rendered source, with no hidden initial state. -/
theorem source_realized : (parse source.render).toOption = some prepared := by decide +kernel

/-- All finite symbolic lookup obligations hold for the validator's actual result. -/
theorem implements : Sweep.Implements prepared machine := by decide +kernel

theorem progress (c : Sweep.Config 1 1) : ∃ c', Sweep.advance machine c = some c' := by
  rcases c with ⟨s, left, right⟩
  cases right <;> simp [Sweep.advance, machine]

/-- Every fuel budget is exhausted, including budgets ending halfway through a turn. -/
theorem outOfFuel (fuel : Nat) : (evalPrepared prepared fuel).exit = .outOfFuel := by
  change (exec prepared fuel ⟨Sweep.query ⟨0, [], [0]⟩, []⟩).2 = .outOfFuel
  exact Sweep.divergence_simulation implements (fun _ => True)
    (fun c _ => by obtain ⟨c', h⟩ := progress c; exact ⟨c', h, trivial⟩)
    ⟨0, [], [0]⟩ trivial fuel []

end Langlib.Computability.JavaGen.Growth
