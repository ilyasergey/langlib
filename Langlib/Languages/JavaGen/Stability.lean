import Langlib.Languages.JavaGen.Semantics

/-! # JavaGen: completed runs and stationary queries

These proofs concern the actual evaluator, including the retained proof
record. They do not assume validator correctness or Java correspondence.
-/

namespace Langlib.JavaGen
open Langlib.Common

/-- More fuel cannot change a completed result, including its proof record. -/
theorem exec_stable (p : Prepared) :
    ∀ (n m : Nat) (st : State), n ≤ m → (exec p n st).2 ≠ .outOfFuel →
      exec p m st = exec p n st := by
  intro n
  induction n with
  | zero => intro m st _ h; exact absurd rfl h
  | succ n ih =>
    intro m st hnm h
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hn : n ≤ m' := by omega
    cases hs : step p st.query with
    | accept frame => simp [exec, hs]
    | reject => simp [exec, hs]
    | next frame q =>
      simp only [exec, hs] at h ⊢
      exact ih m' _ hn h

theorem evalProg_stable (p : Prepared) {n m : Nat} (hnm : n ≤ m)
    (h : (evalProg p n).exit ≠ .outOfFuel) :
    evalProg p m = evalProg p n := by
  unfold evalProg at h ⊢
  split
  · rfl
  · next hg =>
    rw [if_neg hg] at h
    rw [exec_stable p n m ⟨p.source.query, []⟩ hnm h]

/-- A query returning to itself really diverges at every finite fuel,
even though the retained history keeps growing. The step has positive cost. -/
theorem exec_self_loop (p : Prepared) (q : Query) (frame : Frame)
    (hs : step p q = .next frame q) (fuel : Nat) (history : List Frame) :
    (exec p fuel ⟨q, history⟩).2 = .outOfFuel := by
  induction fuel generalizing history with
  | zero => rfl
  | succ fuel ih => simpa only [exec, hs] using ih (frame :: history)

end Langlib.JavaGen
