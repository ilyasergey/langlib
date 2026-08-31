import Langlib.Languages.Unlambda.Semantics

/-!
# Unlambda: completed runs are stable under more fuel

`exec` iterates the machine's `step` one unit of fuel at a time and stops on
its own only when `step` does, so a completed run is a fixed point of more
fuel. Discharges unlambda's `Langlib.Common.LawfulProgLang` instance in
`Langlib/Computability/Unlambda.lean`.
-/

namespace Langlib.Unlambda

open Langlib.Common

/-- A completed run is a fixed point of more fuel. -/
theorem exec_stable :
    ∀ (n m : Nat) (mach : Mach), n ≤ m → (exec n mach).2 ≠ .outOfFuel →
      exec m mach = exec n mach := by
  intro n
  induction n with
  | zero => intro m mach _ h; exact absurd rfl h
  | succ n ih =>
    intro m mach hm h
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hm' : n ≤ m' := by omega
    rw [exec] at h
    conv => lhs; rw [exec]
    conv => rhs; rw [exec]
    try dsimp only at h ⊢
    repeat' split at h
    all_goals try simp_all only
    all_goals first
      | rfl
      | exact ih _ _ hm' h

/-- `evalProg` written with explicit projections, so the destructuring `let`
inside it stops blocking rewrites. -/
theorem evalProg_eq (p : Prog) (i : Input) (fuel : Nat) :
    evalProg p i fuel =
      { output := (exec fuel { ctl := .eval p .nil, input := i }).1.output,
        exit := (exec fuel { ctl := .eval p .nil, input := i }).2 } := by
  unfold evalProg
  rcases exec fuel { ctl := .eval p .nil, input := i } with ⟨mach, e⟩
  rfl

/-- A completed `evalProg` run does not change when given more fuel. -/
theorem evalProg_stable (p : Prog) (i : Input) {n m : Nat} (hnm : n ≤ m)
    (h : (evalProg p i n).exit ≠ .outOfFuel) :
    evalProg p i m = evalProg p i n := by
  rw [evalProg_eq] at h
  rw [evalProg_eq, evalProg_eq, exec_stable n m _ hnm h]

end Langlib.Unlambda
