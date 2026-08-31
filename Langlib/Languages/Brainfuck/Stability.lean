import Langlib.Languages.Brainfuck.Semantics

/-!
# Brainfuck: completed runs are stable under more fuel

`exec` spends one unit of fuel per primitive command or loop check and stops
on its own only by halting or erroring, so a completed run is a fixed point
of more fuel. Proved for the whole final state, at every configuration.

These lemmas discharge the `Langlib.Common.LawfulProgLang` instances of
brainfuck and of the two languages that run through its interpreter, Ook!
and brainloller, in `Langlib/Computability/{Brainfuck,Ook,Brainloller}.lean`.
-/

namespace Langlib.Brainfuck

open Langlib.Common

/-- A completed run is a fixed point of more fuel: the entire final state
agrees, not just the exit. "Completed" is any exit but `outOfFuel`. -/
theorem exec_stable (cfg : Config) :
    ∀ (n m : Nat) (k : List Op) (s : State), n ≤ m →
      (exec cfg n k s).2 ≠ .outOfFuel → exec cfg m k s = exec cfg n k s := by
  intro n
  induction n with
  | zero => intro m k s _ h; exact absurd rfl h
  | succ n ih =>
    intro m k s hm h
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hm' : n ≤ m' := by omega
    cases k with
    | nil => rfl
    | cons op k =>
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
theorem evalProg_eq (cfg : Config) (p : Prog) (i : Input) (fuel : Nat) :
    evalProg cfg p i fuel =
      { output := (exec cfg fuel p { input := i }).1.output,
        exit := (exec cfg fuel p { input := i }).2 } := by
  unfold evalProg
  rcases exec cfg fuel p { input := i } with ⟨s, e⟩
  rfl

/-- A completed `evalProg` run does not change when given more fuel. -/
theorem evalProg_stable (cfg : Config) (p : Prog) (i : Input) {n m : Nat}
    (hnm : n ≤ m) (h : (evalProg cfg p i n).exit ≠ .outOfFuel) :
    evalProg cfg p i m = evalProg cfg p i n := by
  rw [evalProg_eq] at h
  rw [evalProg_eq, evalProg_eq, exec_stable cfg n m _ _ hnm h]

end Langlib.Brainfuck
