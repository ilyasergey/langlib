import Langlib.Languages.MalbolgeUnshackled.Semantics

/-!
# Malbolge Unshackled: completed runs are stable under more fuel

One unit of fuel per (attempted) instruction — Johansen's `hang` included —
and the machine stops on its own only at `halt` or on an error, so a
completed run is a fixed point of more fuel. Discharges the
`Langlib.Common.LawfulProgLang` instance in
`Langlib/Computability/MalbolgeUnshackled.lean`.
-/

namespace Langlib.MalbolgeUnshackled

open Langlib.Common

/-- A completed run is a fixed point of more fuel. -/
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
    try dsimp only at h ⊢
    repeat' split at h
    all_goals try simp_all only
    all_goals first
      | rfl
      | exact ih _ _ hm' h

/-- `evalImage` written with explicit projections, so the destructuring
`let` inside it stops blocking rewrites. -/
theorem evalImage_eq (cfg : Config) (img : Image) (i : Input) (fuel : Nat) :
    evalImage cfg img i fuel =
      { output :=
          (exec fuel
            { mem := img.mem, input := i,
              rotWidth := max cfg.rotWidth minRotWidth }).1.output,
        exit :=
          (exec fuel
            { mem := img.mem, input := i,
              rotWidth := max cfg.rotWidth minRotWidth }).2 } := by
  unfold evalImage
  rcases exec fuel
    { mem := img.mem, input := i, rotWidth := max cfg.rotWidth minRotWidth }
    with ⟨s, e⟩
  rfl

/-- A completed `evalImage` run does not change when given more fuel. -/
theorem evalImage_stable (cfg : Config) (img : Image) (i : Input) {n m : Nat}
    (hnm : n ≤ m) (h : (evalImage cfg img i n).exit ≠ .outOfFuel) :
    evalImage cfg img i m = evalImage cfg img i n := by
  rw [evalImage_eq] at h
  rw [evalImage_eq, evalImage_eq, exec_stable n m _ hnm h]

end Langlib.MalbolgeUnshackled
