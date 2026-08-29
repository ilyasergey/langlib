/-!
# The unlimited register machine

This is langlib's yardstick for Turing completeness: the unlimited register
machine (URM) of Shepherdson and Sturgis, in the presentation Cutland uses.
A URM has countably many registers, each holding a natural number, and four
instructions: zero a register, increment a register, copy one register into
another, and jump when two registers are equal. That instruction set is
universal (Cutland, *Computability*, chapter 1), so exhibiting a simulation
of an arbitrary URM inside a language `L` shows that `L` computes every
computable function.

## Relation to cslib

[cslib](https://github.com/leanprover/cslib) has this machine as
`Cslib.Computability.URM`. langlib does not depend on cslib, because cslib
depends on Mathlib and langlib is deliberately dependency-free (see
`docs/computability.md` for the full argument and the evidence). The
definitions below therefore *mirror* cslib's, name for name and constructor
for constructor, so that a bridging lemma is a formality once a `proofs/`
package exists. Deviations, all of them forced by the absence of Mathlib:

* `Regs` is `Nat → Nat` rather than `ℕ → ℕ`; these are the same type.
* `Regs.write` is `fun k => if k = n then v else σ k` rather than
  `Function.update σ n v`, which is not in core Lean. The two agree
  pointwise (`Function.update` for a non-dependent codomain reduces to the
  same conditional), so a bridging lemma is `funext` plus `dif_eq_if`.
* `Instr.readsFrom` returns a `List Nat` rather than a `Finset ℕ`, since
  `Finset` is a Mathlib notion. It is not used in any proof here.
* cslib's execution semantics is the relation `Step` plus a `Part`-valued,
  `Classical.choose`-based `eval`. That is not executable, and langlib wants
  to *run* compiled URM programs in its test suite, so this module adds a
  fuel-based executable `step`/`run` and proves it agrees with the relation
  (`step_eq_some_iff_Step`, `Steps_run`). The relation itself is a
  constructor-for-constructor copy of cslib's, so anything proved against
  `Step` transfers directly.
* `Steps` is spelled as its own inductive rather than
  `Relation.ReflTransGen (Step p)`, which lives in Mathlib. The two
  definitions are the same up to renaming the constructors.

Nothing else differs: the instruction set, the 0-indexed program counter,
the "halted when the counter is at or past the end of the program"
convention, `Regs.ofInputs`, and "the answer is register 0" are all cslib's.
-/

namespace Langlib.Computability.URM

/-! ## Instructions -/

/-- URM instructions.

* `Z n`: set register `n` to zero.
* `S n`: increment register `n` by one.
* `T m n`: transfer (copy) the contents of register `m` to register `n`.
* `J m n q`: if registers `m` and `n` hold equal values, jump to instruction
  `q`; otherwise proceed to the next instruction.

Jump targets are 0-indexed absolute instruction positions, and a target at
or past the end of the program halts the machine. -/
inductive Instr where
  | Z : Nat → Instr
  | S : Nat → Instr
  | T : Nat → Nat → Instr
  | J : Nat → Nat → Nat → Instr
deriving DecidableEq, Repr, Inhabited

namespace Instr

/-- The registers read by an instruction. -/
def readsFrom : Instr → List Nat
  | Z _ => []
  | S n => [n]
  | T m _ => [m]
  | J m n _ => [m, n]

/-- The register written by an instruction, if any. -/
def writesTo : Instr → Option Nat
  | Z n => some n
  | S n => some n
  | T _ n => some n
  | J _ _ _ => none

/-- The largest register index an instruction mentions. -/
def maxRegister : Instr → Nat
  | Z n => n
  | S n => n
  | T m n => max m n
  | J m n _ => max m n

/-- Shift every jump target by `offset`. Used when concatenating programs. -/
def shiftJumps (offset : Nat) : Instr → Instr
  | Z n => Z n
  | S n => S n
  | T m n => T m n
  | J m n q => J m n (q + offset)

/-- Shift every register reference by `offset`. Used to isolate register use
when composing programs. -/
def shiftRegisters (offset : Nat) : Instr → Instr
  | Z n => Z (n + offset)
  | S n => S (n + offset)
  | T m n => T (m + offset) (n + offset)
  | J m n q => J (m + offset) (n + offset) q

end Instr

/-! ## Registers -/

/-- Register contents, as a total function from register index to value.
Only finitely many registers are ever touched by a program, but keeping the
state total avoids carrying a finiteness side-condition through every
lemma. -/
abbrev Regs := Nat → Nat

namespace Regs

/-- All registers zero. -/
def zero : Regs := fun _ => 0

/-- Read register `n`. -/
def read (σ : Regs) (n : Nat) : Nat := σ n

/-- Write `v` to register `n`. -/
def write (σ : Regs) (n : Nat) (v : Nat) : Regs :=
  fun k => if k = n then v else σ k

@[simp] theorem read_write_self (σ : Regs) (n v : Nat) :
    (σ.write n v).read n = v := by
  simp [read, write]

@[simp] theorem read_write_of_ne (σ : Regs) {n k : Nat} (h : k ≠ n) (v : Nat) :
    (σ.write n v).read k = σ.read k := by
  simp [read, write, h]

/-- Load the inputs into registers `0, 1, …`; every other register is zero. -/
def ofInputs (inputs : List Nat) : Regs := fun n => inputs.getD n 0

/-- The machine's answer: the contents of register 0. -/
def output (σ : Regs) : Nat := σ 0

end Regs

/-! ## Programs -/

/-- A URM program is a finite list of instructions. -/
abbrev Program := List Instr

namespace Program

/-- The largest register index the program mentions. -/
def maxRegister (p : Program) : Nat :=
  p.foldl (fun acc i => max acc i.maxRegister) 0

/-- Shift every jump target in the program by `offset`. -/
def shiftJumps (p : Program) (offset : Nat) : Program :=
  p.map (Instr.shiftJumps offset)

/-- Shift every register reference in the program by `offset`. -/
def shiftRegisters (p : Program) (offset : Nat) : Program :=
  p.map (Instr.shiftRegisters offset)

end Program

/-! ## Machine state -/

/-- A machine configuration: a 0-indexed program counter and the registers. -/
structure State where
  pc : Nat
  regs : Regs

namespace State

/-- The initial configuration for a given input vector. -/
def init (inputs : List Nat) : State := ⟨0, Regs.ofInputs inputs⟩

/-- A configuration is halted when the counter has run off the end. -/
def isHalted (s : State) (p : Program) : Prop := p.length ≤ s.pc

instance (s : State) (p : Program) : Decidable (s.isHalted p) :=
  inferInstanceAs (Decidable (p.length ≤ s.pc))

instance : Inhabited State := ⟨init []⟩

end State

/-! ## Execution, as a relation

This is cslib's `Step`, copied constructor for constructor. -/

/-- Single-step execution. -/
inductive Step (p : Program) : State → State → Prop where
  | zero {s : State} {n : Nat}
      (h : p[s.pc]? = some (Instr.Z n)) :
      Step p s ⟨s.pc + 1, s.regs.write n 0⟩
  | succ {s : State} {n : Nat}
      (h : p[s.pc]? = some (Instr.S n)) :
      Step p s ⟨s.pc + 1, s.regs.write n (s.regs.read n + 1)⟩
  | transfer {s : State} {m n : Nat}
      (h : p[s.pc]? = some (Instr.T m n)) :
      Step p s ⟨s.pc + 1, s.regs.write n (s.regs.read m)⟩
  | jump_eq {s : State} {m n q : Nat}
      (h : p[s.pc]? = some (Instr.J m n q))
      (heq : s.regs.read m = s.regs.read n) :
      Step p s ⟨q, s.regs⟩
  | jump_ne {s : State} {m n q : Nat}
      (h : p[s.pc]? = some (Instr.J m n q))
      (hne : s.regs.read m ≠ s.regs.read n) :
      Step p s ⟨s.pc + 1, s.regs⟩

/-- Multi-step execution: the reflexive-transitive closure of `Step`.
cslib writes this as `Relation.ReflTransGen (Step p)`. -/
inductive Steps (p : Program) : State → State → Prop where
  | refl {s : State} : Steps p s s
  | tail {s s' s'' : State} : Steps p s s' → Step p s' s'' → Steps p s s''

theorem Steps.single {p : Program} {s s' : State} (h : Step p s s') :
    Steps p s s' := .tail .refl h

theorem Steps.head {p : Program} {s s' s'' : State} (h : Step p s s')
    (hs : Steps p s' s'') : Steps p s s'' := by
  induction hs with
  | refl => exact .single h
  | tail _ hlast ih => exact .tail ih hlast

theorem Steps.trans {p : Program} {s s' s'' : State}
    (h : Steps p s s') (h' : Steps p s' s'') : Steps p s s'' := by
  induction h' with
  | refl => exact h
  | tail _ hlast ih => exact .tail ih hlast

/-! ## Execution, as a function

cslib's `eval` is `Part`-valued and noncomputable. langlib runs its
machines, so here is the executable version, together with the lemmas that
tie it back to `Step`. -/

/-- One step of execution, or `none` when the machine has halted. -/
def step (p : Program) (s : State) : Option State :=
  match p[s.pc]? with
  | none => none
  | some (.Z n) => some ⟨s.pc + 1, s.regs.write n 0⟩
  | some (.S n) => some ⟨s.pc + 1, s.regs.write n (s.regs.read n + 1)⟩
  | some (.T m n) => some ⟨s.pc + 1, s.regs.write n (s.regs.read m)⟩
  | some (.J m n q) =>
    if s.regs.read m = s.regs.read n then some ⟨q, s.regs⟩
    else some ⟨s.pc + 1, s.regs⟩

/-- Run for at most `n` steps. A halted machine stays where it is, so `run`
is monotone in the step budget in the strong sense that once the machine
halts more budget changes nothing (`run_halted`). -/
def run (p : Program) (s : State) : Nat → State
  | 0 => s
  | n + 1 => match step p s with
    | none => s
    | some s' => run p s' n

/-- `p` halts on `s` within `n` steps. -/
def haltsIn (p : Program) (s : State) (n : Nat) : Prop :=
  (run p s n).isHalted p

instance (p : Program) (s : State) (n : Nat) : Decidable (haltsIn p s n) :=
  inferInstanceAs (Decidable ((run p s n).isHalted p))

/-- `p` halts on `inputs`, cslib's `Halts`. -/
def Halts (p : Program) (inputs : List Nat) : Prop :=
  ∃ n, haltsIn p (State.init inputs) n

/-- `p` halts on `inputs` with `result` in register 0, cslib's
`HaltsWithResult`. -/
def HaltsWithResult (p : Program) (inputs : List Nat) (result : Nat) : Prop :=
  ∃ n, haltsIn p (State.init inputs) n ∧ (run p (State.init inputs) n).regs.output = result

/-! ### Agreement between the two presentations -/

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

/-- Everything `run` reaches is reachable by `Steps`. -/
theorem Steps_run (p : Program) (s : State) (n : Nat) : Steps p s (run p s n) := by
  induction n generalizing s with
  | zero => exact .refl
  | succ n ih =>
    unfold run
    cases h : step p s with
    | none => exact .refl
    | some s' => exact Steps.head (step_eq_some_iff_Step.mp h) (ih s')

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

end Langlib.Computability.URM
