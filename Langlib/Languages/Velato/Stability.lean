import Langlib.Languages.Velato.Semantics

/-!
# Velato: completed runs are stable under more fuel

`execStmt` spends one unit of fuel per statement and one more per loop
iteration, and it stops on its own only by halting or erroring. So a run
that has completed is a fixed point: more fuel re-runs the same statements
to the same end.

This is proved for the whole final state rather than for the exit alone,
which is what lets `evalProg` (the `ProgLang` runner) and `evalTrace` (the
`TraceLang` trace) inherit the fact at once — the two read different fields
off the same state.

These lemmas discharge Velato's `Langlib.Common.LawfulProgLang` and
`LawfulTraceLang` instances, registered next to `ProgLang VelatoLang` in
`Langlib/Computability/Velato.lean`. Without them the completeness theorem
in that file would be a weaker statement than it looks: see the module
header of `Langlib/Common/Compilation.lean` for why fuel that is not pinned
to its budget role can be used as a smuggled input channel.
-/

namespace Langlib.Velato

open Langlib.Common

/-- A completed run is a fixed point of more fuel: the entire final state
agrees, not merely the exit. Both halves of the interpreter are proved at
once, because each calls the other. -/
theorem exec_stable : ∀ n : Nat,
    (∀ (cs : List Stmt) (m : Nat) (s : State), n ≤ m →
      (execList n cs s).2 ≠ .outOfFuel → execList m cs s = execList n cs s) ∧
    (∀ (c : Stmt) (m : Nat) (s : State), n ≤ m →
      (execStmt n c s).2 ≠ .outOfFuel → execStmt m c s = execStmt n c s) := by
  intro n
  induction n with
  | zero =>
    constructor
    · intro cs m s _ h
      cases cs with
      | nil => simp only [execList]
      | cons c rest => simp only [execList] at h; exact absurd rfl h
    · intro c m s _ h
      simp only [execStmt] at h
      exact absurd rfl h
  | succ n ih =>
    obtain ⟨ihL, ihS⟩ := ih
    constructor
    · intro cs m s hm h
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have hm' : n ≤ m' := by omega
      cases cs with
      | nil => simp only [execList]
      | cons c rest =>
        simp only [execList] at h ⊢
        rcases hstep : execStmt n c s with ⟨s', e⟩
        rw [hstep] at h
        cases e with
        | outOfFuel => simp at h
        | error msg =>
          rw [ihS c m' s hm' (by rw [hstep]; nofun), hstep]
        | halted =>
          rw [ihS c m' s hm' (by rw [hstep]; nofun), hstep]
          exact ihL rest m' s' hm' h
    · intro c m s hm h
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have hm' : n ≤ m' := by omega
      cases c with
      | declare v ty => simp only [execStmt]
      | assign v e => simp only [execStmt]
      | print e => simp only [execStmt]
      | input v => simp only [execStmt]
      | ite cond thn els =>
        simp only [execStmt] at h ⊢
        rcases hc : evalExpr s.store cond with msg | v
        · rfl
        · rw [hc] at h
          dsimp only at h ⊢
          exact ihL _ m' s hm' h
      | «while» cond body =>
        simp only [execStmt] at h ⊢
        rcases hc : evalExpr s.store cond with msg | v
        · rfl
        · rw [hc] at h
          dsimp only at h ⊢
          by_cases hv : v.truthy = true
          · simp only [if_pos hv] at h ⊢
            rcases hstep : execList n body s with ⟨s', e⟩
            rw [hstep] at h
            cases e with
            | outOfFuel => simp at h
            | error msg2 =>
              rw [ihL body m' s hm' (by rw [hstep]; nofun), hstep]
            | halted =>
              rw [ihL body m' s hm' (by rw [hstep]; nofun), hstep]
              dsimp only at h ⊢
              exact ihS _ m' s' hm' h
          · simp only [if_neg hv] at h ⊢

/-- The statement half, in the form callers need. -/
theorem execStmt_stable (c : Stmt) (s : State) {n m : Nat} (hnm : n ≤ m)
    (h : (execStmt n c s).2 ≠ .outOfFuel) : execStmt m c s = execStmt n c s :=
  (exec_stable n).2 c m s hnm h

/-- The block half, in the form the runner needs. -/
theorem execList_stable (cs : List Stmt) (s : State) {n m : Nat} (hnm : n ≤ m)
    (h : (execList n cs s).2 ≠ .outOfFuel) : execList m cs s = execList n cs s :=
  (exec_stable n).1 cs m s hnm h

/-- `evalProg` written with explicit projections, so the destructuring `let`
inside it stops blocking rewrites. -/
theorem evalProg_eq (p : Prog) (i : Input) (fuel : Nat) :
    evalProg p i fuel =
      { output := (execList fuel p { input := i }).1.output,
        exit := (execList fuel p { input := i }).2 } := by
  unfold evalProg
  rcases execList fuel p { input := i } with ⟨s, e⟩
  rfl

/-- The `ProgLang` half of stability: a completed `evalProg` run does not
change when given more fuel. -/
theorem evalProg_stable (p : Prog) (i : Input) {n m : Nat} (hnm : n ≤ m)
    (h : (evalProg p i n).exit ≠ .outOfFuel) : evalProg p i m = evalProg p i n := by
  rw [evalProg_eq] at h
  rw [evalProg_eq, evalProg_eq, execList_stable p _ hnm h]

/-- The `TraceLang` half of stability: a completed run's trace does not
change when given more fuel. -/
theorem evalTrace_stable (p : Prog) (i : Input) {n m : Nat} (hnm : n ≤ m)
    (h : (evalProg p i n).exit ≠ .outOfFuel) : evalTrace p i m = evalTrace p i n := by
  rw [evalProg_eq] at h
  unfold evalTrace
  rw [execList_stable p _ hnm h]

end Langlib.Velato
