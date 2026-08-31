import Langlib.Languages.Thue.Semantics

/-!
# Thue: completed runs are stable under more fuel

`exec` applies one rewrite per unit of fuel and stops on its own only when
no rule matches, so a completed run is a fixed point of more fuel. The
random strategy is no obstacle: the generator state lives in `MState` and
the run is a deterministic function of the seed. Discharges thue's
`Langlib.Common.LawfulProgLang` instance in
`Langlib/Computability/Thue.lean`.
-/

namespace Langlib.Thue

open Langlib.Common

/-- A completed run is a fixed point of more fuel. -/
theorem exec_stable (cfg : Config) (rules : List Rule) :
    ∀ (n m : Nat) (st : MState), n ≤ m → (exec cfg rules n st).2 ≠ .outOfFuel →
      exec cfg rules m st = exec cfg rules n st := by
  intro n
  induction n with
  | zero => intro m st _ h; exact absurd rfl h
  | succ n ih =>
    intro m st hm h
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

/-- `evalProg` written with explicit projections, so the destructuring `let`
inside it stops blocking rewrites. The seed is inlined the way `evalProg`
computes it. -/
theorem evalProg_eq (cfg : Config) (p : Prog) (i : Input) (fuel : Nat) :
    evalProg cfg p i fuel =
      (let seed := match cfg.strategy with
        | .random s => s
        | .first => 0
      let r := exec cfg p.rules fuel { str := p.initial.toList, input := i, rng := seed }
      { output :=
          if cfg.finalState && r.2 == .halted then
            r.1.output ++ (String.ofList r.1.str ++ "\n").toUTF8
          else
            r.1.output,
        exit := r.2 }) := by
  unfold evalProg
  dsimp only
  rcases exec cfg p.rules fuel
    { str := p.initial.toList, input := i,
      rng := match cfg.strategy with | .random s => s | .first => 0 } with ⟨st, e⟩
  rfl

/-- A completed `evalProg` run does not change when given more fuel. -/
theorem evalProg_stable (cfg : Config) (p : Prog) (i : Input) {n m : Nat}
    (hnm : n ≤ m) (h : (evalProg cfg p i n).exit ≠ .outOfFuel) :
    evalProg cfg p i m = evalProg cfg p i n := by
  rw [evalProg_eq] at h
  dsimp only at h
  rw [evalProg_eq, evalProg_eq]
  dsimp only
  rw [exec_stable cfg p.rules n m _ hnm h]

end Langlib.Thue
