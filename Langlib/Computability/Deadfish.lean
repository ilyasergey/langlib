import Langlib.Common.Computability
import Langlib.Languages.Deadfish.Semantics

/-!
# Deadfish: exact termination and decidable halting

Deadfish programs are finite lists of straight-line commands.  The
accumulator is globally unbounded because repeated squaring can grow without
limit, but this does not affect termination: a program with `n` commands
returns `.halted` exactly when its fuel is greater than `n`.

The current `BoundedStorage` interface cannot express the program-dependent
finite set of prefixes of a Deadfish program.  Its `Config` type is fixed for
the whole language, and `index_inj` requires every value of that type to fit
inside every program's finite bound.  `deadfish_not_boundedStorage` makes the
mismatch precise for this evaluator.
-/

namespace Langlib.Computability

open Langlib.Common

/-- The tag type naming Deadfish for the `ProgLang` class. -/
inductive DeadfishLang : Type

instance : ProgLang DeadfishLang where
  Prog := Langlib.Deadfish.Prog
  parse := Langlib.Deadfish.parse
  run := fun p _input fuel => Langlib.Deadfish.evalProg p fuel

namespace Deadfish

private theorem exit_beq_halted_eq_true_iff (e : Exit) :
    (e == Exit.halted) = true ↔ e = Exit.halted := by
  cases e with
  | halted => constructor <;> intro <;> rfl
  | outOfFuel =>
      constructor
      · intro h
        change false = true at h
        contradiction
      · intro h
        contradiction
  | error msg =>
      constructor
      · intro h
        change false = true at h
        contradiction
      · intro h
        contradiction

/-- The exit status of `exec` depends only on the program length and fuel.
The strict inequality reflects the evaluator's base-case order: after the
last command, one further unit of fuel observes the empty command list. -/
theorem exec_exit_eq_halted_iff (fuel : Nat) (p : Langlib.Deadfish.Prog)
    (s : Langlib.Deadfish.State) :
    (Langlib.Deadfish.exec fuel p s).2 = Exit.halted ↔ p.length < fuel := by
  induction fuel generalizing p s with
  | zero => simp [Langlib.Deadfish.exec]
  | succ fuel ih =>
      cases p with
      | nil => simp [Langlib.Deadfish.exec]
      | cons c p =>
          cases c <;> simp [Langlib.Deadfish.exec, ih]

/-- A parsed Deadfish program returns `.halted` exactly above its length. -/
theorem evalProg_exit_eq_halted_iff (p : Langlib.Deadfish.Prog) (fuel : Nat) :
    (Langlib.Deadfish.evalProg p fuel).exit = Exit.halted ↔ p.length < fuel := by
  simp only [Langlib.Deadfish.evalProg]
  exact exec_exit_eq_halted_iff fuel p {}

/-- The `ProgLang` runner has halted exactly above the program length. -/
theorem isHalted_eq_true_iff (p : Langlib.Deadfish.Prog) (input : Input) (fuel : Nat) :
    (ProgLang.run (L := DeadfishLang) p input fuel).isHalted = true ↔
      p.length < fuel := by
  rw [show ProgLang.run (L := DeadfishLang) p input fuel =
      Langlib.Deadfish.evalProg p fuel from rfl]
  rw [show (Langlib.Deadfish.evalProg p fuel).isHalted =
      ((Langlib.Deadfish.evalProg p fuel).exit == Exit.halted) from rfl,
    exit_beq_halted_eq_true_iff, evalProg_exit_eq_halted_iff]

/-- Every Deadfish program halts, with `p.length + 1` units of fuel. -/
theorem halts (p : Langlib.Deadfish.Prog) (input : Input) :
    (ProgLang.run (L := DeadfishLang) p input (p.length + 1)).isHalted = true := by
  exact (isHalted_eq_true_iff p input (p.length + 1)).2 (by omega)

/-- Halting for Deadfish is decidable directly.  Every parsed program is a
positive instance, witnessed by fuel `p.length + 1`. -/
def haltingDecidable (p : Langlib.Deadfish.Prog) (input : Input) :
    Decidable (∃ fuel,
      (ProgLang.run (L := DeadfishLang) p input fuel).isHalted = true) :=
  isTrue ⟨p.length + 1, halts p input⟩

/-- No `BoundedStorage DeadfishLang` witness exists for the current
interface.  A fixed finite `Config` type cannot record arbitrarily long
straight-line executions before they halt.

This result concerns the shape of `BoundedStorage`, not unbounded execution:
every Deadfish program still halts by `halts`. -/
theorem no_boundedStorage (b : BoundedStorage DeadfishLang) : False := by
  let input : Input := Input.ofString ""
  let base : Langlib.Deadfish.Prog := []
  let B := b.bound base input
  let long : Langlib.Deadfish.Prog := List.replicate B Langlib.Deadfish.Cmd.noise
  have hindex : ∀ n,
      b.index base input (b.configOf long input n) < B := by
    intro n
    exact b.index_lt base input _
  obtain ⟨a, c, hac, hcB, hsameIndex⟩ :=
    exists_repeat B (fun n => b.index base input (b.configOf long input n)) hindex
  have hcfg : b.configOf long input a = b.configOf long input c :=
    b.index_inj base input _ _ hsameIndex
  have hshift : ∀ k,
      b.configOf long input (a + k) = b.configOf long input (c + k) := by
    intro k
    induction k with
    | zero => simpa using hcfg
    | succ k ih =>
        have hs := b.succ_congr long input (a + k) (c + k) ih
        simpa [Nat.add_assoc] using hs
  let k := B + 1 - c
  have hck : c + k = B + 1 := by
    dsimp [k]
    omega
  have hak : a + k ≤ B := by
    dsimp [k]
    omega
  have hhaltLate :
      (ProgLang.run (L := DeadfishLang) long input (B + 1)).isHalted = true := by
    apply (isHalted_eq_true_iff long input (B + 1)).2
    simp [long]
  have hhaltEarly :
      (ProgLang.run (L := DeadfishLang) long input (a + k)).isHalted = true := by
    have heq := hshift k
    rw [hck] at heq
    rw [b.halted_congr long input (a + k) (B + 1) heq]
    exact hhaltLate
  have htooEarly := (isHalted_eq_true_iff long input (a + k)).1 hhaltEarly
  simp [long] at htooEarly
  omega

end Deadfish

end Langlib.Computability
