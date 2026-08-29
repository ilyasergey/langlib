/-!
# Fuel algebra for the reference interpreters

Every interpreter core in langlib has the shape `Nat → State → Result`: a
fuel bound, a machine state, and an answer. Proofs about such interpreters
spend most of their effort on fuel bookkeeping, and this module isolates the
one abstraction that removes it.

`Reaches E s t` says: running `E` from `s` costs a fixed amount of fuel and
then continues exactly as a run from `t` would. It is an *exact* statement,
not an inequality, which is what makes it compose: two consecutive code
fragments cost the sum of their costs, and nothing else about the run
changes. `docs/verification.md` also asks for the monotonicity lemmas
`output_mono` and `halted_stable`; a proof phrased through `Reaches` needs
neither, because the fuel is threaded exactly rather than bounded.

The definition is deliberately generic over the state and result types, so
the same three lemmas serve whitespace, subleq, brainfuck and Turpentine.
-/

namespace Langlib.Common

variable {σ ρ : Type _}

/-- `Reaches E s t`: for some fixed cost `c`, running the fuel-indexed
interpreter `E` from state `s` with `c + f` fuel gives exactly what running
from `t` with `f` fuel gives, for every `f`. -/
def Reaches (E : Nat → σ → ρ) (s t : σ) : Prop :=
  ∃ c, ∀ f, E (c + f) s = E f t

namespace Reaches

variable {E : Nat → σ → ρ} {s t u : σ}

/-- Reflexivity: reaching yourself costs nothing. -/
theorem refl (E : Nat → σ → ρ) (s : σ) : Reaches E s s :=
  ⟨0, fun f => by rw [Nat.zero_add]⟩

/-- One instruction: a state that steps to another for one unit of fuel. -/
theorem one (h : ∀ f, E (f + 1) s = E f t) : Reaches E s t :=
  ⟨1, fun f => by rw [Nat.add_comm]; exact h f⟩

/-- Costs add. This is the composition rule the backend proofs run on. -/
theorem trans (h₁ : Reaches E s t) (h₂ : Reaches E t u) : Reaches E s u := by
  cases h₁ with
  | intro c₁ h₁ =>
    cases h₂ with
    | intro c₂ h₂ =>
      refine ⟨c₁ + c₂, fun f => ?_⟩
      rw [Nat.add_assoc, h₁ (c₂ + f), h₂ f]

/-- Reaching a state where the run is known lets you name the total fuel. -/
theorem eval (h : Reaches E s t) (f : Nat) : ∃ m, E m s = E f t := by
  cases h with
  | intro c hc => exact ⟨c + f, hc f⟩

end Reaches

end Langlib.Common
