import Langlib.Languages.Fractran.Semantics

/-!
# FRACTRAN: completed runs are stable under more fuel

One unit of fuel per multiplication, halting only when no fraction applies,
so a completed run is a fixed point of more fuel. Discharges FRACTRAN's
`Langlib.Common.LawfulProgLang` (and, via `TraceLang.ofInputFree`, its
`LawfulTraceLang`) instance in `Langlib/Computability/Fractran.lean`.
-/

namespace Langlib.Fractran

open Langlib.Common

/-- A completed run is a fixed point of more fuel. -/
theorem exec_stable (cfg : Config) (p : Prog) :
    ∀ (n m : Nat) (x : Nat) (out : ByteArray), n ≤ m →
      (exec cfg p n x out).exit ≠ .outOfFuel →
      exec cfg p m x out = exec cfg p n x out := by
  intro n
  induction n with
  | zero => intro m x out _ h; exact absurd rfl h
  | succ n ih =>
    intro m x out hm h
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
      | exact ih _ _ _ hm' h

/-- A completed `evalProg` run does not change when given more fuel. -/
theorem evalProg_stable (cfg : Config) (p : Prog) (x : Nat) {n m : Nat}
    (hnm : n ≤ m) (h : (evalProg cfg p x n).exit ≠ .outOfFuel) :
    evalProg cfg p x m = evalProg cfg p x n := by
  unfold evalProg at h ⊢
  cases hx : x == 0 with
  | true => rfl
  | false =>
    rw [hx] at h
    rw [if_neg (show ¬(false = true) by simp)] at h ⊢
    exact exec_stable cfg p n m _ _ hnm h

end Langlib.Fractran
