import Langlib.Languages.Ski.Semantics

/-!
# SKI: completed runs are stable under more fuel

One unit of fuel per reduction, and a term in normal form is a fixed point
of `normalise`, so a run that has normalised does not change with more
fuel. Discharges SKI's `Langlib.Common.LawfulProgLang` instance in
`Langlib/Computability/Ski.lean`.
-/

namespace Langlib.Ski

open Langlib.Common

/-- A run that reached a normal form is a fixed point of more fuel. -/
theorem normalise_stable :
    ∀ (n m : Nat) (t : Term), n ≤ m → normalise n t ≠ none →
      normalise m t = normalise n t := by
  intro n
  induction n with
  | zero => intro m t _ h; exact absurd rfl h
  | succ n ih =>
    intro m t hm h
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hm' : n ≤ m' := by omega
    rw [normalise] at h
    conv => lhs; rw [normalise]
    conv => rhs; rw [normalise]
    try dsimp only at h ⊢
    repeat' split at h
    all_goals try simp_all only
    all_goals first
      | rfl
      | exact ih _ _ hm' h

/-- A completed `evalProg` run does not change when given more fuel. -/
theorem evalProg_stable (p : Prog) {n m : Nat} (hnm : n ≤ m)
    (h : (evalProg p n).exit ≠ .outOfFuel) : evalProg p m = evalProg p n := by
  unfold evalProg at h ⊢
  have hn : normalise n p ≠ none := by
    intro hnone
    rw [hnone] at h
    exact h rfl
  rw [normalise_stable n m p hnm hn]

end Langlib.Ski
