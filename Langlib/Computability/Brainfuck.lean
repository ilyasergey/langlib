import Langlib.Common.Fuel
import Langlib.Computability.Class
import Langlib.Computability.URM
import Langlib.Languages.Brainfuck

/-!
# Brainfuck is Turing complete

This file compiles an arbitrary unlimited register machine into brainfuck and
proves the simulation, giving `brainfuckComplete : TuringComplete
BrainfuckLang`.

See `docs/computability-brainfuck.md` for the prose account.
-/

namespace Langlib.Computability.URMBrainfuck

open Langlib.Common

/-! ## The counter language

The proof goes through an intermediate language rather than compiling the URM
straight onto the tape. `Cmd` is a register machine with *structured* control:
increment, decrement, emit one output byte, and `loop r b`, which runs `b`
while register `r` is nonzero. It is the machine a brainfuck tape actually
implements, so the second half of the compiler is compositional, and it is a
register machine, so the first half is ordinary arithmetic on `Nat → Nat` with
no tape in sight.

`dec` on a zero register has no rule: the semantics below is a big-step
relation, and a program that decrements a zero register simply has no
derivation. That is exactly the discipline the brainfuck code needs, because
the code emitted for `dec` walks one cell down a unary run and would step onto
the guard row if the run were empty. -/

/-- A counter-machine command. -/
inductive Cmd where
  /-- Increment register `r`. -/
  | inc (r : Nat)
  /-- Decrement register `r`; undefined when `r` holds zero. -/
  | dec (r : Nat)
  /-- Append one byte to the output. -/
  | emit
  /-- While register `r` is nonzero, run `body`. -/
  | loop (r : Nat) (body : List Cmd)
deriving Repr, Inhabited

/-- A counter-machine program. -/
abbrev Code := List Cmd

/-- Registers plus a count of the bytes emitted so far. Only the number of
output bytes matters, because every byte the compiled program emits has the
same value. -/
structure CState where
  regs : Nat → Nat
  out : Nat

namespace CState

def up (s : CState) (r : Nat) : CState :=
  { s with regs := Function.update s.regs r (s.regs r + 1) }

def down (s : CState) (r : Nat) : CState :=
  { s with regs := Function.update s.regs r (s.regs r - 1) }

def emitOne (s : CState) : CState := { s with out := s.out + 1 }

@[simp] theorem up_regs_self (s : CState) (r : Nat) : (s.up r).regs r = s.regs r + 1 := by
  simp [up]

@[simp] theorem up_regs_of_ne (s : CState) {r k : Nat} (h : k ≠ r) :
    (s.up r).regs k = s.regs k := by
  simp [up, Function.update_of_ne h]

@[simp] theorem down_regs_self (s : CState) (r : Nat) : (s.down r).regs r = s.regs r - 1 := by
  simp [down]

@[simp] theorem down_regs_of_ne (s : CState) {r k : Nat} (h : k ≠ r) :
    (s.down r).regs k = s.regs k := by
  simp [down, Function.update_of_ne h]

@[simp] theorem up_out (s : CState) (r : Nat) : (s.up r).out = s.out := rfl
@[simp] theorem down_out (s : CState) (r : Nat) : (s.down r).out = s.out := rfl
@[simp] theorem emitOne_regs (s : CState) : s.emitOne.regs = s.regs := rfl
@[simp] theorem emitOne_out (s : CState) : s.emitOne.out = s.out + 1 := rfl

end CState

/-- Big-step semantics, in continuation-passing form so that it lines up one
for one with brainfuck's `exec`, which also carries the rest of the program as
a list. `R` bounds the register indices: a command mentioning a register at or
beyond `R` has no derivation, which is what keeps the tape layout (`R`
interleaved columns) able to hold every register the program touches. -/
inductive Ev (R : Nat) : Code → CState → CState → Prop where
  | nil {s : CState} : Ev R [] s s
  | inc {r : Nat} {cs : Code} {s t : CState} (h : r < R) :
      Ev R cs (s.up r) t → Ev R (Cmd.inc r :: cs) s t
  | dec {r : Nat} {cs : Code} {s t : CState} (h : r < R) (hnz : s.regs r ≠ 0) :
      Ev R cs (s.down r) t → Ev R (Cmd.dec r :: cs) s t
  | emit {cs : Code} {s t : CState} :
      Ev R cs s.emitOne t → Ev R (Cmd.emit :: cs) s t
  | loopZ {r : Nat} {b cs : Code} {s t : CState} (h : r < R) (hz : s.regs r = 0) :
      Ev R cs s t → Ev R (Cmd.loop r b :: cs) s t
  | loopS {r : Nat} {b cs : Code} {s t : CState} (h : r < R) (hnz : s.regs r ≠ 0) :
      Ev R (b ++ Cmd.loop r b :: cs) s t → Ev R (Cmd.loop r b :: cs) s t

/-- Sequential composition. -/
theorem Ev.append {R : Nat} {c₁ : Code} {s t : CState} (h₁ : Ev R c₁ s t) :
    ∀ {c₂ : Code} {u : CState}, Ev R c₂ t u → Ev R (c₁ ++ c₂) s u := by
  induction h₁ with
  | nil => intro c₂ u h; simpa using h
  | inc h _ ih => intro c₂ u h2; exact Ev.inc h (ih h2)
  | dec h hnz _ ih => intro c₂ u h2; exact Ev.dec h hnz (ih h2)
  | emit _ ih => intro c₂ u h2; exact Ev.emit (ih h2)
  | loopZ h hz _ ih => intro c₂ u h2; exact Ev.loopZ h hz (ih h2)
  | loopS h hnz _ ih =>
    intro c₂ u h2
    refine Ev.loopS h hnz ?_
    have hx := ih h2
    simpa [List.append_assoc] using hx

/-! ## Counter-machine macros

Each macro comes with a lemma of one shape: from any register file `w` it
produces a `w'`, gives the value of every register the macro writes, and says
that every other register is untouched. The frame condition is what makes the
dispatch chain below tractable. -/

/-- `a := 0`. -/
def clear (a : Nat) : Code := [Cmd.loop a [Cmd.dec a]]

theorem clear_spec {R a : Nat} (ha : a < R) :
    ∀ (v : Nat) (s : CState), s.regs a = v →
      ∃ w', Ev R (clear a) s ⟨w', s.out⟩ ∧ w' a = 0 ∧ ∀ r, r ≠ a → w' r = s.regs r := by
  intro v
  induction v with
  | zero =>
    intro s hs
    exact ⟨s.regs, Ev.loopZ ha hs Ev.nil, hs, fun _ _ => rfl⟩
  | succ v ih =>
    intro s hs
    have hnz : s.regs a ≠ 0 := by omega
    have hd : (s.down a).regs a = v := by simp [hs]
    obtain ⟨w', hev, h0, hfr⟩ := ih (s.down a) hd
    refine ⟨w', Ev.loopS ha hnz (Ev.dec ha hnz hev), h0, ?_⟩
    intro r hr
    rw [hfr r hr, CState.down_regs_of_ne s hr]

/-- `b := b + a; a := 0`. -/
def move (a b : Nat) : Code := [Cmd.loop a [Cmd.dec a, Cmd.inc b]]

theorem move_spec {R a b : Nat} (ha : a < R) (hb : b < R) (hab : a ≠ b) :
    ∀ (v : Nat) (s : CState), s.regs a = v →
      ∃ w', Ev R (move a b) s ⟨w', s.out⟩ ∧ w' a = 0 ∧ w' b = s.regs b + v ∧
        ∀ r, r ≠ a → r ≠ b → w' r = s.regs r := by
  intro v
  induction v with
  | zero =>
    intro s hs
    exact ⟨s.regs, Ev.loopZ ha hs Ev.nil, hs, by omega, fun _ _ _ => rfl⟩
  | succ v ih =>
    intro s hs
    have hnz : s.regs a ≠ 0 := by omega
    have hsa : ((s.down a).up b).regs a = v := by
      rw [CState.up_regs_of_ne _ hab, CState.down_regs_self, hs]
      omega
    have hsb : ((s.down a).up b).regs b = s.regs b + 1 := by
      rw [CState.up_regs_self, CState.down_regs_of_ne _ hab.symm]
    obtain ⟨w', hev, h0, hbv, hfr⟩ := ih ((s.down a).up b) hsa
    refine ⟨w', Ev.loopS ha hnz (Ev.dec ha hnz (Ev.inc hb hev)), h0, by omega, ?_⟩
    intro r hra hrb
    rw [hfr r hra hrb, CState.up_regs_of_ne _ hrb, CState.down_regs_of_ne _ hra]

/-- `b := b + a; c := c + a; a := 0`. -/
def move2 (a b c : Nat) : Code := [Cmd.loop a [Cmd.dec a, Cmd.inc b, Cmd.inc c]]

theorem move2_spec {R a b c : Nat} (ha : a < R) (hb : b < R) (hc : c < R)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∀ (v : Nat) (s : CState), s.regs a = v →
      ∃ w', Ev R (move2 a b c) s ⟨w', s.out⟩ ∧ w' a = 0 ∧ w' b = s.regs b + v ∧
        w' c = s.regs c + v ∧ ∀ r, r ≠ a → r ≠ b → r ≠ c → w' r = s.regs r := by
  intro v
  induction v with
  | zero =>
    intro s hs
    exact ⟨s.regs, Ev.loopZ ha hs Ev.nil, hs, by omega, by omega, fun _ _ _ _ => rfl⟩
  | succ v ih =>
    intro s hs
    have hnz : s.regs a ≠ 0 := by omega
    have hsa : (((s.down a).up b).up c).regs a = v := by
      rw [CState.up_regs_of_ne _ hac, CState.up_regs_of_ne _ hab,
        CState.down_regs_self, hs]
      omega
    have hsb : (((s.down a).up b).up c).regs b = s.regs b + 1 := by
      rw [CState.up_regs_of_ne _ hbc, CState.up_regs_self, CState.down_regs_of_ne _ hab.symm]
    have hsc : (((s.down a).up b).up c).regs c = s.regs c + 1 := by
      rw [CState.up_regs_self, CState.up_regs_of_ne _ hbc.symm, CState.down_regs_of_ne _ hac.symm]
    obtain ⟨w', hev, h0, hbv, hcv, hfr⟩ := ih (((s.down a).up b).up c) hsa
    refine ⟨w', Ev.loopS ha hnz (Ev.dec ha hnz (Ev.inc hb (Ev.inc hc hev))), h0,
      by omega, by omega, ?_⟩
    intro r hra hrb hrc
    rw [hfr r hra hrb hrc, CState.up_regs_of_ne _ hrc, CState.up_regs_of_ne _ hrb,
      CState.down_regs_of_ne _ hra]

end Langlib.Computability.URMBrainfuck
