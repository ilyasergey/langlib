import Langlib.Languages.Turpentine.Semantics

/-!
# Turpentine divergence

Divergence means exhaustion at every finite fuel budget in the actual source
interpreter. It is independent of the answer convention and output decoding.
Completed-run stability and the structural inversions below support compiler
proofs without introducing a second source semantics.
-/

namespace Langlib.Turpentine

open Langlib.Common

/-- A source statement exhausts every finite budget from this state. -/
def StmtDiverges (st : Stmt) (s : State) : Prop :=
  ∀ fuel, (exec fuel st s).2 = .outOfFuel

/-- A source program exhausts every finite budget on this input stream. -/
def Diverges (p : Program) (input : Input) : Prop :=
  ∀ fuel, (evalProgram p input fuel).exit = .outOfFuel

/-- Every completed source execution, including an error, is stable under
increasing fuel. The source's structural fuel need not count machine steps. -/
theorem exec_stable : ∀ n st s m, n ≤ m →
    (exec n st s).2 ≠ .outOfFuel → exec m st s = exec n st s := by
  intro n
  induction n with
  | zero => intro st s m _ hd; exact (hd (by simp [exec])).elim
  | succ n ih =>
    intro st
    induction st with
    | seq a b iha _ =>
      intro s m hle hd
      cases m with
      | zero => omega
      | succ m =>
        rcases h : exec (n + 1) a s with ⟨s', e⟩
        cases e with
        | outOfFuel => simp [exec, h] at hd
        | halted =>
          have ha : exec (m + 1) a s = (s', .halted) :=
            (iha s (m + 1) hle (by simp [h])).trans h
          simp only [exec, h, ha] at hd ⊢
          exact ih b s' m (by omega) hd
        | error msg =>
          have ha : exec (m + 1) a s = (s', .error msg) :=
            (iha s (m + 1) hle (by simp [h])).trans h
          simp only [exec, h, ha]
    | ite c a b _ _ =>
      intro s m hle hd
      cases m with
      | zero => omega
      | succ m =>
        cases h : evalExpr s.env c with
        | error msg => simp only [exec, h]
        | ok v =>
          cases v with
          | int z => simp only [exec, h]
          | arr xs => simp only [exec, h]
          | bool v =>
            cases v <;> simp only [exec, h] at hd ⊢
            · exact ih b s m (by omega) hd
            · exact ih a s m (by omega) hd
    | «while» c b _ =>
      intro s m hle hd
      cases m with
      | zero => omega
      | succ m =>
        cases h : evalExpr s.env c with
        | error msg => simp only [exec, h]
        | ok v =>
          cases v with
          | int z => simp only [exec, h]
          | arr xs => simp only [exec, h]
          | bool v =>
            cases v with
            | false => simp only [exec, h]
            | true =>
              rcases hb : exec n b s with ⟨s', e⟩
              cases e with
              | outOfFuel => simp [exec, h, hb] at hd
              | halted =>
                have hb' : exec m b s = (s', .halted) :=
                  (ih b s m (by omega) (by simp [hb])).trans hb
                simp only [exec, h, hb, hb'] at hd ⊢
                exact ih (.while c b) s' m (by omega) hd
              | error msg =>
                have hb' : exec m b s = (s', .error msg) :=
                  (ih b s m (by omega) (by simp [hb])).trans hb
                simp only [exec, h, hb, hb']
    | _ =>
      intro s m hle _
      cases m with
      | zero => omega
      | succ m => simp only [exec]

/-- Exhaustion at a larger source budget implies exhaustion at a smaller one. -/
theorem exec_outOfFuel_of_le {n m : Nat} {st : Stmt} {s : State}
    (hle : n ≤ m) (hm : (exec m st s).2 = .outOfFuel) :
    (exec n st s).2 = .outOfFuel := by
  apply Classical.byContradiction
  intro hn
  rw [exec_stable n st s m hle hn] at hm
  exact hn hm

namespace StmtDiverges

/-- A divergent first statement prevents a sequence from completing. -/
theorem seq_left {a : Stmt} {s : State} (hd : StmtDiverges a s) (b : Stmt) :
    StmtDiverges (.seq a b) s := by
  intro fuel
  cases fuel with
  | zero => simp only [exec]
  | succ fuel =>
    have h := hd (fuel + 1)
    rcases he : exec (fuel + 1) a s with ⟨s', e⟩
    simp only [he] at h
    subst e
    simp only [exec, he]

/-- After a terminating first statement, divergence of a sequence belongs
exactly to its continuation. -/
theorem seq_right {a b : Stmt} {s s' : State} {n : Nat}
    (hd : StmtDiverges (.seq a b) s) (ha : exec n a s = (s', .halted)) :
    StmtDiverges b s' := by
  intro fuel
  have ha' : exec (n + fuel + 1) a s = (s', .halted) :=
    (exec_stable n a s _ (by omega) (by simp [ha])).trans ha
  have h := hd (n + fuel + 1)
  simp only [exec, ha'] at h
  exact exec_outOfFuel_of_le (by omega : fuel ≤ n + fuel) h

/-- A divergent sequence either diverges in its first statement or reaches
a normally halting first statement followed by a divergent second one. -/
theorem seq_cases {a b : Stmt} {s : State} (hd : StmtDiverges (.seq a b) s) :
    StmtDiverges a s ∨
      ∃ n s', exec n a s = (s', .halted) ∧ StmtDiverges b s' := by
  by_cases ha : StmtDiverges a s
  · exact Or.inl ha
  · simp only [StmtDiverges, Classical.not_forall] at ha
    obtain ⟨n, hn⟩ := ha
    rcases he : exec n a s with ⟨s', e⟩
    cases e with
    | outOfFuel => exact (hn (by simp [he])).elim
    | halted => exact Or.inr ⟨n, s', he, hd.seq_right he⟩
    | error msg =>
      have he' : exec (n + 1) a s = (s', .error msg) :=
        (exec_stable n a s _ (by omega) (by simp [he])).trans he
      have h := hd (n + 1)
      simp [exec, he'] at h

/-- A divergent conditional selected a Boolean branch, and that branch diverges. -/
theorem ite_cases {c : Expr} {a b : Stmt} {s : State}
    (hd : StmtDiverges (.ite c a b) s) :
    (evalExpr s.env c = .ok (.bool true) ∧ StmtDiverges a s) ∨
      (evalExpr s.env c = .ok (.bool false) ∧ StmtDiverges b s) := by
  have h := hd 1
  cases he : evalExpr s.env c with
  | error msg => simp [exec, he] at h
  | ok v =>
    cases v with
    | int z => simp [exec, he] at h
    | arr xs => simp [exec, he] at h
    | bool v =>
      cases v with
      | false => exact Or.inr ⟨rfl, fun f => by simpa [exec, he] using hd (f + 1)⟩
      | true => exact Or.inl ⟨rfl, fun f => by simpa [exec, he] using hd (f + 1)⟩

/-- A divergent loop enters its body. -/
theorem while_cond {c : Expr} {b : Stmt} {s : State}
    (hd : StmtDiverges (.while c b) s) : evalExpr s.env c = .ok (.bool true) := by
  have h := hd 1
  cases he : evalExpr s.env c with
  | error msg => simp [exec, he] at h
  | ok v =>
    cases v with
    | int z => simp [exec, he] at h
    | arr xs => simp [exec, he] at h
    | bool v =>
      cases v with
      | false => simp [exec, he] at h
      | true => rfl

/-- After a terminating iteration, the same loop diverges from the next state. -/
theorem while_next {c : Expr} {b : Stmt} {s s' : State} {n : Nat}
    (hd : StmtDiverges (.while c b) s) (hb : exec n b s = (s', .halted)) :
    StmtDiverges (.while c b) s' := by
  intro fuel
  have hb' : exec (n + fuel) b s = (s', .halted) :=
    (exec_stable n b s _ (by omega) (by simp [hb])).trans hb
  have h := hd (n + fuel + 1)
  simp only [exec, hd.while_cond, hb'] at h
  exact exec_outOfFuel_of_le (by omega : fuel ≤ n + fuel) h

/-- A divergent loop either diverges inside its body or completes an
iteration and continues diverging. -/
theorem while_cases {c : Expr} {b : Stmt} {s : State}
    (hd : StmtDiverges (.while c b) s) :
    StmtDiverges b s ∨
      ∃ n s', exec n b s = (s', .halted) ∧ StmtDiverges (.while c b) s' := by
  by_cases hb : StmtDiverges b s
  · exact Or.inl hb
  · simp only [StmtDiverges, Classical.not_forall] at hb
    obtain ⟨n, hn⟩ := hb
    rcases he : exec n b s with ⟨s', e⟩
    cases e with
    | outOfFuel => exact (hn (by simp [he])).elim
    | halted => exact Or.inr ⟨n, s', he, hd.while_next he⟩
    | error msg =>
      have h := hd (n + 1)
      simp [exec, hd.while_cond, he] at h

end StmtDiverges

/-- Program divergence consists of successful initialization followed by
statement divergence; an initialization error is never divergence. -/
theorem diverges_iff (p : Program) (input : Input) :
    Diverges p input ↔ ∃ env, initEnv p = .ok env ∧
      StmtDiverges p.body { env, input } := by
  cases he : initEnv p with
  | error msg => simp [Diverges, evalProgram, he]
  | ok env => simp [Diverges, evalProgram, StmtDiverges, he]

end Langlib.Turpentine
