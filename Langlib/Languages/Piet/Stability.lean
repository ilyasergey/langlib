import Langlib.Languages.Piet.Semantics

/-!
# Piet: completed runs are stable under more fuel

One unit of evaluator fuel per transition attempt, and `exec` stops on its
own only when `tryFrom` halts or gives up, so a completed run is a fixed
point of more fuel. The white-start slide and the block analysis are fuel
bounds of their own, independent of the evaluator's, so the wrapper's
branches are stable trivially. Discharges Piet's
`Langlib.Common.LawfulProgLang` instance in
`Langlib/Computability/Piet.lean`.
-/

namespace Langlib.Piet

open Langlib.Common

/-- A completed run is a fixed point of more fuel. -/
theorem exec_stable (g : Grid) (bl : Blocks) :
    ∀ (n m : Nat) (s : MState), n ≤ m → (exec g bl n s).2 ≠ .outOfFuel →
      exec g bl m s = exec g bl n s := by
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

/-- A completed `evalGrid` run does not change when given more fuel. -/
theorem evalGrid_stable (g : Grid) (i : Input) {n m : Nat} (hnm : n ≤ m)
    (h : (evalGrid g i n).exit ≠ .outOfFuel) :
    evalGrid g i m = evalGrid g i n := by
  unfold evalGrid at h ⊢
  dsimp only at h ⊢
  cases hg : g.get 0 0 with
  | black => rfl
  | white =>
    simp only [hg] at h ⊢
    cases hs : slide g (slideFuel g) [] (0, 0) .right .left with
    | landed p dp cc =>
      simp only [hs] at h ⊢
      have hne : (exec g (computeBlocks g) n
          { pos := p, dp := dp, cc := cc, input := i }).2 ≠ .outOfFuel := by
        rcases hE : exec g (computeBlocks g) n
          { pos := p, dp := dp, cc := cc, input := i } with ⟨s, e⟩
        rw [hE] at h
        exact h
      rw [exec_stable g (computeBlocks g) n m _ hnm hne]
    | trapped => rfl
    | noFuel =>
      simp only [hs] at h
      exact absurd rfl h
  | chromatic hue l =>
    simp only [hg] at h ⊢
    have hne : (exec g (computeBlocks g) n { pos := (0, 0), input := i }).2
        ≠ .outOfFuel := by
      rcases hE : exec g (computeBlocks g) n { pos := (0, 0), input := i }
        with ⟨s, e⟩
      rw [hE] at h
      exact h
    rw [exec_stable g (computeBlocks g) n m _ hnm hne]

end Langlib.Piet
