import Langlib.Common.Fuel
import Langlib.Common.Io

/-!
# Divergence from continuing simulation

Exact finite-prefix simulation needs a progress bound to preserve divergence.
`ReachesPlus` records a strictly positive cost; a zero-cost `Reaches` loop
cannot be used as evidence of divergent execution.
-/

namespace Langlib.Common

variable {σ ρ : Type _}

/-- Exact execution of a nonempty target segment. -/
def ReachesPlus (E : Nat → σ → ρ) (s t : σ) : Prop :=
  ∃ c, 0 < c ∧ ∀ f, E (c + f) s = E f t

namespace ReachesPlus

variable {E : Nat → σ → ρ} {s t u : σ}

/-- Distinct zero-fuel observations rule out a zero-cost segment. -/
theorem of_ne (h : Reaches E s t) (hne : E 0 s ≠ E 0 t) : ReachesPlus E s t := by
  obtain ⟨cost, hc⟩ := h
  refine ⟨cost, ?_, hc⟩
  cases cost with
  | zero => exact (hne (hc 0)).elim
  | succ n => exact Nat.zero_lt_succ n

theorem toReaches (h : ReachesPlus E s t) : Reaches E s t := by
  obtain ⟨c, _, hc⟩ := h
  exact ⟨c, hc⟩

theorem one (h : ∀ f, E (f + 1) s = E f t) : ReachesPlus E s t :=
  ⟨1, Nat.zero_lt_succ _, fun f => by rw [Nat.add_comm]; exact h f⟩

theorem trans_left (h₁ : ReachesPlus E s t) (h₂ : Reaches E t u) :
    ReachesPlus E s u := by
  obtain ⟨c₁, hp, h₁⟩ := h₁
  obtain ⟨c₂, h₂⟩ := h₂
  exact ⟨c₁ + c₂, by omega, fun f => by rw [Nat.add_assoc, h₁, h₂]⟩

theorem trans_right (h₁ : Reaches E s t) (h₂ : ReachesPlus E t u) :
    ReachesPlus E s u := by
  obtain ⟨c₁, h₁⟩ := h₁
  obtain ⟨c₂, hp, h₂⟩ := h₂
  exact ⟨c₁ + c₂, by omega, fun f => by rw [Nat.add_assoc, h₁, h₂]⟩

end ReachesPlus

/-- Any two completed runs of a stable interpreter agree, even when their
fuel budgets are ordered in the opposite direction. -/
theorem completed_runs_eq (E : Nat → σ → ρ) (exit : ρ → Exit)
    (stable : ∀ n m s, n ≤ m → exit (E n s) ≠ .outOfFuel → E m s = E n s)
    (s : σ) (n m : Nat) (hn : exit (E n s) ≠ .outOfFuel)
    (hm : exit (E m s) ≠ .outOfFuel) : E n s = E m s :=
  (stable n (max n m) s (Nat.le_max_left _ _) hn).symm.trans
    (stable m (max n m) s (Nat.le_max_right _ _) hm)

/-- A stable interpreter that can always simulate another positive-cost
segment from an invariant state exhausts every finite fuel budget. -/
theorem outOfFuel_of_progress (E : Nat → σ → ρ) (exit : ρ → Exit)
    (zero : ∀ s, exit (E 0 s) = .outOfFuel)
    (stable : ∀ n m s, n ≤ m → exit (E n s) ≠ .outOfFuel → E m s = E n s)
    (I : σ → Prop)
    (progress : ∀ s, I s → ∃ t, ReachesPlus E s t ∧ I t)
    (fuel : Nat) (s : σ) (hs : I s) : exit (E fuel s) = .outOfFuel := by
  induction fuel using Nat.strongRecOn generalizing s with
  | ind fuel ih =>
    obtain ⟨t, ⟨cost, hp, hc⟩, ht⟩ := progress s hs
    by_cases hle : cost ≤ fuel
    · rw [show fuel = cost + (fuel - cost) by omega, hc]
      exact ih (fuel - cost) (by omega) t ht
    · apply Classical.byContradiction
      intro hdone
      have hstable := congrArg exit (stable fuel cost s (by omega) hdone)
      have hcost := congrArg exit (hc 0)
      simp only [Nat.add_zero, zero] at hcost
      exact hdone (hstable.symm.trans hcost)

/-- A finite prefix leading to a divergent continuation also diverges. -/
theorem Reaches.outOfFuel {E : Nat → σ → ρ} {s t : σ}
    (h : Reaches E s t) (exit : ρ → Exit)
    (stable : ∀ n m s, n ≤ m → exit (E n s) ≠ .outOfFuel → E m s = E n s)
    (ht : ∀ fuel, exit (E fuel t) = .outOfFuel) (fuel : Nat) :
    exit (E fuel s) = .outOfFuel := by
  obtain ⟨cost, hc⟩ := h
  by_cases hle : cost ≤ fuel
  · rw [show fuel = cost + (fuel - cost) by omega, hc]
    exact ht _
  · apply Classical.byContradiction
    intro hdone
    have hstable := congrArg exit (stable fuel cost s (by omega) hdone)
    have hcost := congrArg exit (hc 0)
    simp only [Nat.add_zero, ht] at hcost
    exact hdone (hstable.symm.trans hcost)

end Langlib.Common
