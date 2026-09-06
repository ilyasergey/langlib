import Langlib.Languages.JavaGen.Answer
import Langlib.Languages.JavaGen.Stability

/-! # Stability of numeric answer inference and concrete checking -/

namespace Langlib.JavaGen
open Langlib.Common

theorem infer_stable (p : Prepared) :
    ∀ (n m : Nat) (q : OpenQuery) (digits : Ty), n ≤ m →
      infer p n q digits ≠ .outOfFuel → infer p m q digits = infer p n q digits := by
  intro n
  induction n with
  | zero => intro m q digits _ h; exact absurd rfl h
  | succ n ih =>
    intro m q digits hnm h
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hn : n ≤ m' := by omega
    cases hs : inferStep p q digits with
    | candidate k => simp [infer, hs]
    | error msg => simp [infer, hs]
    | next q' digits' =>
      simp only [infer, hs] at h ⊢
      exact ih m' q' digits' hn h

theorem evalAnswer_stable (p : Prepared) {n m : Nat} (hnm : n ≤ m)
    (h : (evalAnswer p n).exit ≠ .outOfFuel) :
    evalAnswer p m = evalAnswer p n := by
  have hi : infer p n (initialOpen p.source) [] ≠ .outOfFuel := by
    intro hi
    simp [evalAnswer, hi] at h
  have hm := infer_stable p n m _ [] hnm hi
  unfold evalAnswer at h ⊢
  rw [hm]
  cases hs : infer p n (initialOpen p.source) [] with
  | outOfFuel => exact False.elim (hi hs)
  | error msg => rfl
  | candidate k =>
    simp only
    cases hp : prepare (p.source.bindAnswer k) with
    | error msg => rfl
    | ok concrete =>
      simp only [hs, hp, checkedAnswer] at h
      simp only
      rw [evalProg_stable concrete hnm h]

theorem evalPrepared_stable (p : Prepared) {n m : Nat} (hnm : n ≤ m)
    (h : (evalPrepared p n).exit ≠ .outOfFuel) :
    evalPrepared p m = evalPrepared p n := by
  unfold evalPrepared at h ⊢
  split at h <;> simp_all only
  · exact evalAnswer_stable p hnm h
  · exact evalProg_stable p hnm h

end Langlib.JavaGen
