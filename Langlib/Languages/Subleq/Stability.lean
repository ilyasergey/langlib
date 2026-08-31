import Langlib.Languages.Subleq.Semantics

/-!
# Subleq: completed runs are stable under more fuel

`exec` spends one unit of fuel per instruction and stops on its own only by
halting or erroring, so a run that has completed is a fixed point: more fuel
re-runs the same instructions to the same end. This file proves that for the
whole final state, not merely the summary, which is what lets `evalProg`
(the `ProgLang` runner) and `evalTrace` (the `TraceLang` trace) inherit the
fact at once.

These lemmas discharge subleq's `Langlib.Common.LawfulProgLang` and
`LawfulTraceLang` instances, registered next to `ProgLang SubleqLang` in
`Langlib/Computability/Subleq.lean`. The classes live in
`Langlib/Common/Compilation.lean`; this file needs only the semantics.
-/

namespace Langlib.Subleq

open Langlib.Common

/-- A completed run is a fixed point of more fuel: the entire final state
agrees, not just the exit. "Completed" is any exit but `outOfFuel`. -/
theorem exec_stable :
    ∀ (n m : Nat) (s : State), n ≤ m → (exec n s).2 ≠ .outOfFuel →
      exec m s = exec n s := by
  intro n
  induction n with
  | zero => intro m s _ h; exact absurd rfl h
  | succ n ih =>
    intro m s hm h
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hm' : n ≤ m' := by omega
    rw [exec] at h
    conv => lhs; rw [exec]
    conv => rhs; rw [exec]
    dsimp only at h ⊢
    repeat' split at h
    all_goals simp_all only
    all_goals first
      | rfl
      | exact ih _ _ hm' h

/-- `evalProg` written with explicit projections, so the destructuring `let`
inside it stops blocking rewrites. -/
theorem evalProg_eq (p : Prog) (i : Input) (fuel : Nat) :
    evalProg p i fuel =
      { output := (exec fuel { mem := Mem.ofProg p, input := i }).1.output,
        exit := (exec fuel { mem := Mem.ofProg p, input := i }).2 } := by
  unfold evalProg
  rcases exec fuel { mem := Mem.ofProg p, input := i } with ⟨s, e⟩
  rfl

/-- The `ProgLang` half of stability: a completed `evalProg` run does not
change when given more fuel. -/
theorem evalProg_stable (p : Prog) (i : Input) {n m : Nat} (hnm : n ≤ m)
    (h : (evalProg p i n).exit ≠ .outOfFuel) :
    evalProg p i m = evalProg p i n := by
  rw [evalProg_eq] at h
  rw [evalProg_eq, evalProg_eq, exec_stable n m _ hnm h]

/-- The `TraceLang` half of stability: a completed run's trace does not
change when given more fuel. -/
theorem evalTrace_stable (p : Prog) (i : Input) {n m : Nat} (hnm : n ≤ m)
    (h : (evalProg p i n).exit ≠ .outOfFuel) :
    evalTrace p i m = evalTrace p i n := by
  rw [evalProg_eq] at h
  unfold evalTrace
  rw [exec_stable n m _ hnm h]

end Langlib.Subleq
