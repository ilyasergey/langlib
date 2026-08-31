import Langlib.Languages.Deadfish.Semantics

/-!
# Deadfish: completed runs are stable under more fuel

One unit of fuel per command, halting only at the end of the program, so a
completed run is a fixed point of more fuel. Discharges deadfish's
`Langlib.Common.LawfulProgLang` instance in
`Langlib/Computability/Deadfish.lean`.
-/

namespace Langlib.Deadfish

open Langlib.Common

/-- A completed run is a fixed point of more fuel. -/
theorem exec_stable :
    ∀ (n m : Nat) (k : List Cmd) (s : State), n ≤ m →
      (exec n k s).2 ≠ .outOfFuel → exec m k s = exec n k s := by
  intro n
  induction n with
  | zero => intro m k s _ h; exact absurd rfl h
  | succ n ih =>
    intro m k s hm h
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hm' : n ≤ m' := by omega
    cases k with
    | nil => rfl
    | cons c k =>
      rw [exec.eq_def] at h
      conv => lhs; rw [exec.eq_def]
      conv => rhs; rw [exec.eq_def]
      dsimp only at h ⊢
      repeat' split at h
      all_goals try simp_all only
      all_goals first
        | rfl
        | exact ih _ _ _ hm' h

/-- `evalProg` written with explicit projections, so the destructuring `let`
inside it stops blocking rewrites. -/
theorem evalProg_eq (p : Prog) (fuel : Nat) :
    evalProg p fuel =
      { output := (exec fuel p {}).1.output, exit := (exec fuel p {}).2 } := by
  unfold evalProg
  rcases exec fuel p {} with ⟨s, e⟩
  rfl

/-- A completed `evalProg` run does not change when given more fuel. -/
theorem evalProg_stable (p : Prog) {n m : Nat} (hnm : n ≤ m)
    (h : (evalProg p n).exit ≠ .outOfFuel) : evalProg p m = evalProg p n := by
  rw [evalProg_eq] at h
  rw [evalProg_eq, evalProg_eq, exec_stable n m _ _ hnm h]

end Langlib.Deadfish
