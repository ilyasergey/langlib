import Cslib.Computability.URM.Execution

/-!
# The unlimited register machine: langlib's adapter over cslib

The universal model langlib measures its languages against is the unlimited
register machine of Shepherdson and Sturgis, in Cutland's presentation:
countably many registers holding natural numbers, and four instructions,
`Z n` (zero a register), `S n` (increment), `T m n` (copy), and `J m n q`
(jump to instruction `q` when registers `m` and `n` are equal). That machine
is universal, so a simulation of an arbitrary URM inside a language `L`
shows that `L` computes every computable function.

**The machine itself is cslib's** (`Cslib.Computability.URM`), not ours: the
instruction set, the register state, the `Step` relation, `Steps`, `Halts`
and `HaltsWithResult` are all used directly. This file adds only what cslib
does not have and langlib needs, namely an *executable* interpreter.

cslib's execution semantics is a relation, `Step`, together with a
`Part`-valued `eval` built from `Classical.choose`. That is the right choice
for reasoning but it cannot be run, and langlib's differential tests
(`Langlib/Tests/URMWhitespace.lean`) want to execute a URM program and
compare its answer against the compiled Whitespace program's output. So this
module defines a fuel-driven `step`/`run` and proves it agrees with cslib's
relation:

* `step_eq_some_iff_Step` : `step p s = some s' ↔ Cslib.URM.Step p s s'`
* `step_eq_none_iff_isHalted` : `step p s = none ↔ s.isHalted p`
* `steps_run` : `Cslib.URM.Steps p s (run p s n)`
* `haltsWithResult_of_haltsIn` : a terminating `run` gives cslib's
  `HaltsWithResult`

so the executable side is a definition plus four lemmas, and every theorem
in `Langlib/Computability/` is stated against cslib's relation.

Mathlib arrives with cslib. It is confined to `Langlib/Computability/`; the
interpreters under `Langlib/Languages/` and `Langlib/Languages/Turpentine/` do not
import it.
-/

namespace Langlib.Computability.URM

open Cslib.URM

/-! ## Convenience lemmas about registers

cslib's `Regs.write` is `Function.update`; these two lemmas are the only
facts about it the simulation proofs need. -/

theorem read_write_self (σ : Regs) (n v : Nat) : (σ.write n v).read n = v := by
  simp [Regs.read, Regs.write]

theorem read_write_of_ne (σ : Regs) {n k : Nat} (h : k ≠ n) (v : Nat) :
    (σ.write n v).read k = σ.read k := by
  simp [Regs.read, Regs.write, Function.update_of_ne h]

/-! ## An executable interpreter -/

/-- One step of execution, or `none` when the machine has halted. This is
the functional counterpart of `Cslib.URM.Step`. -/
def step (p : Program) (s : State) : Option State :=
  match p[s.pc]? with
  | none => none
  | some (.Z n) => some ⟨s.pc + 1, s.regs.write n 0⟩
  | some (.S n) => some ⟨s.pc + 1, s.regs.write n (s.regs.read n + 1)⟩
  | some (.T m n) => some ⟨s.pc + 1, s.regs.write n (s.regs.read m)⟩
  | some (.J m n q) =>
    if s.regs.read m = s.regs.read n then some ⟨q, s.regs⟩
    else some ⟨s.pc + 1, s.regs⟩

/-- Run for at most `n` steps; a halted machine stays put. -/
def run (p : Program) (s : State) : Nat → State
  | 0 => s
  | n + 1 => match step p s with
    | none => s
    | some s' => run p s' n

/-- `p` reaches a halted configuration from `s` within `n` steps. -/
def haltsIn (p : Program) (s : State) (n : Nat) : Prop :=
  (run p s n).isHalted p

instance (p : Program) (s : State) (n : Nat) : Decidable (haltsIn p s n) :=
  inferInstanceAs (Decidable ((run p s n).isHalted p))

/-- The answer register after running `n` steps from the initial state. -/
def result (p : Program) (inputs : List Nat) (n : Nat) : Nat :=
  (run p (State.init inputs) n).regs.output

/-! ## Agreement with cslib's relation -/

private theorem lt_length_of_getElem?_some {p : Program} {k : Nat} {i : Instr}
    (h : p[k]? = some i) : k < p.length := by
  cases Nat.lt_or_ge k p.length with
  | inl hlt => exact hlt
  | inr hge => rw [List.getElem?_eq_none hge] at h; exact absurd h (by simp)

theorem step_eq_none_iff_isHalted {p : Program} {s : State} :
    step p s = none ↔ s.isHalted p := by
  unfold step
  cases hi : p[s.pc]? with
  | none => exact iff_of_true rfl (List.getElem?_eq_none_iff.mp hi)
  | some i =>
    have hnh : ¬ (p.length ≤ s.pc) := Nat.not_le.mpr (lt_length_of_getElem?_some hi)
    simp only [State.isHalted, hnh, iff_false]
    cases i with
    | Z n => simp
    | S n => simp
    | T m n => simp
    | J m n q => dsimp only; split <;> simp

theorem step_eq_some_iff_Step {p : Program} {s s' : State} :
    step p s = some s' ↔ Step p s s' := by
  constructor
  · intro h
    unfold step at h
    cases hi : p[s.pc]? with
    | none => rw [hi] at h; simp at h
    | some i =>
      rw [hi] at h
      cases i with
      | Z n => dsimp only at h; simp only [Option.some.injEq] at h; exact h ▸ .zero hi
      | S n => dsimp only at h; simp only [Option.some.injEq] at h; exact h ▸ .succ hi
      | T m n => dsimp only at h; simp only [Option.some.injEq] at h; exact h ▸ .transfer hi
      | J m n q =>
        dsimp only at h
        by_cases hq : s.regs.read m = s.regs.read n
        · rw [if_pos hq] at h
          simp only [Option.some.injEq] at h
          exact h ▸ .jump_eq hi hq
        · rw [if_neg hq] at h
          simp only [Option.some.injEq] at h
          exact h ▸ .jump_ne hi hq
  · intro h
    cases h with
    | zero hi => unfold step; rw [hi]
    | succ hi => unfold step; rw [hi]
    | transfer hi => unfold step; rw [hi]
    | jump_eq hi hq => unfold step; rw [hi]; simp [hq]
    | jump_ne hi hq => unfold step; rw [hi]; simp [hq]

/-- Everything `run` reaches, cslib's `Steps` reaches. -/
theorem steps_run (p : Program) (s : State) (n : Nat) : Steps p s (run p s n) := by
  induction n generalizing s with
  | zero => exact .refl
  | succ n ih =>
    unfold run
    cases h : step p s with
    | none => exact .refl
    | some s' => exact Relation.ReflTransGen.head (step_eq_some_iff_Step.mp h) (ih s')

/-- A halted machine does not move. -/
theorem run_halted {p : Program} {s : State} (h : s.isHalted p) (n : Nat) :
    run p s n = s := by
  cases n with
  | zero => rfl
  | succ n => unfold run; rw [step_eq_none_iff_isHalted.mpr h]

/-- Once the machine has halted, extra budget changes nothing. -/
theorem run_add_of_haltsIn {p : Program} {s : State} {n : Nat}
    (h : (run p s n).isHalted p) (k : Nat) : run p s (n + k) = run p s n := by
  induction n generalizing s with
  | zero =>
    simp only [Nat.zero_add]
    simp only [run] at h
    exact run_halted h k
  | succ n ih =>
    rw [show n + 1 + k = (n + k) + 1 from by omega]
    simp only [run]
    cases hs : step p s with
    | none => rfl
    | some s' =>
      simp only [run, hs] at h
      exact ih h

/-- Halting is monotone in the step budget. -/
theorem haltsIn_of_le {p : Program} {s : State} {n m : Nat}
    (h : haltsIn p s n) (hle : n ≤ m) : haltsIn p s m := by
  cases Nat.exists_eq_add_of_le hle with
  | intro k hk =>
    subst hk
    unfold haltsIn at h ⊢
    rw [run_add_of_haltsIn h]
    exact h

/-- The executable interpreter's answer is cslib's answer: a `run` that
halts witnesses `Cslib.URM.HaltsWithResult`. This is the bridge the
differential tests rely on. -/
theorem haltsWithResult_of_haltsIn {p : Program} {inputs : List Nat} {n : Nat}
    (h : haltsIn p (State.init inputs) n) :
    HaltsWithResult p inputs (result p inputs n) :=
  ⟨run p (State.init inputs) n, steps_run p _ n, h, rfl⟩

end Langlib.Computability.URM
