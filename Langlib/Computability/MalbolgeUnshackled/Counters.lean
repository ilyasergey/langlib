import Langlib.Computability.MalbolgeUnshackled

/-!
# Finite cells containing unbounded counters

`Registers` constrains only the finitely many cells allocated to counters.
Unlike `RegMem`, it can be established by finitely many writes over any
periodic background. `initMemory` proves representability; it is a memory
constructor, not yet an MU source initializer or an instruction sequence.
-/

namespace Langlib.Computability.Unshackled.FixedCounter

open Langlib.MalbolgeUnshackled

/-- Cells may be interleaved with operand records and return tables. -/
def addr (base stride r : Nat) : Nat := base + stride * r

/-- Only counters below `R` are represented. There is no constraint on an
infinite unused suffix of the memory. -/
def Registers (base stride R : Nat) (regs : Nat → Nat) (m : Memory) : Prop :=
  ∀ r, r < R → m.get (Value.ofNat (addr base stride r)) = Value.ofNat (regs r)

/-- Initialize a finite collection of counter cells, preserving the original
background and all other cells. -/
def initMemory (base stride : Nat) (regs : Nat → Nat) : Nat → Memory → Memory
  | 0, m => m
  | R + 1, m => (initMemory base stride regs R m).set
      (Value.ofNat (addr base stride R)) (Value.ofNat (regs R))

theorem addr_inj {base stride r k : Nat} (hs : 0 < stride)
    (h : addr base stride r = addr base stride k) : r = k := by
  exact Nat.eq_of_mul_eq_mul_left hs (Nat.add_left_cancel h)

theorem initMemory_get (base : Nat) {stride : Nat} (hs : 0 < stride)
    (regs : Nat → Nat) (R : Nat) (m : Memory) :
    Registers base stride R regs (initMemory base stride regs R m) := by
  induction R with
  | zero => intro r hr; omega
  | succ R ih =>
    intro r hr
    by_cases h : r = R
    · subst r
      exact get_set_self _ _ _
    · rw [initMemory, get_set_ne _ (fun heq => h (addr_inj hs (ofNat_inj heq)).symm)]
      exact ih r (by omega)

theorem initMemory_frame (base stride : Nat) (regs : Nat → Nat) (R : Nat) (m : Memory)
    (x : Value) (h : ∀ r < R, x ≠ Value.ofNat (addr base stride r)) :
    (initMemory base stride regs R m).get x = m.get x := by
  induction R with
  | zero => rfl
  | succ R ih =>
    rw [initMemory, get_set_ne _ (Ne.symm (h R (by omega)))]
    exact ih (fun r hr => h r (by omega))

theorem initMemory_rest (base stride : Nat) (regs : Nat → Nat) (R : Nat) (m : Memory) :
    (initMemory base stride regs R m).rest = m.rest := by
  induction R with
  | zero => rfl
  | succ R ih => exact ih

/-- Every finite register file is representable over the original fill,
including a fill produced from natural loader seeds. No blank-tail
assumption or bound on the counter values is used. -/
theorem registers_exist (base : Nat) {stride : Nat} (hs : 0 < stride)
    (R : Nat) (regs : Nat → Nat) (m : Memory) :
    ∃ m', Registers base stride R regs m' ∧ m'.rest = m.rest ∧
      ∀ x, (∀ r < R, x ≠ Value.ofNat (addr base stride r)) → m'.get x = m.get x :=
  ⟨initMemory base stride regs R m, initMemory_get base hs regs R m,
    initMemory_rest base stride regs R m, initMemory_frame base stride regs R m⟩

/-- A committed counter update preserves every other counter. Reaching this
write by an MU arithmetic routine is a separate operational obligation. -/
theorem registers_set {base stride R : Nat} (hs : 0 < stride)
    {regs : Nat → Nat} {m : Memory} (h : Registers base stride R regs m)
    {r : Nat} (n : Nat) :
    Registers base stride R (Function.update regs r n)
      (m.set (Value.ofNat (addr base stride r)) (Value.ofNat n)) := by
  intro k hk
  by_cases hkr : k = r
  · subst k
    simp [get_set_self]
  · rw [Function.update_of_ne hkr, get_set_ne _ (fun heq => hkr (addr_inj hs (ofNat_inj heq)).symm)]
    exact h k hk

/-- Counter routines maintain this capacity invariant at command boundaries.
The width is a runtime quantity, not a bound fixed by the compiler. -/
def Fits (R w : Nat) (regs : Nat → Nat) : Prop := ∀ r, r < R → regs r < 3 ^ w

/-- On carry, increasing the width makes the original increment fit.
The implementation must retry from the unchanged original counter. -/
theorem increment_fits_after_growth {n w w' : Nat}
    (hcarry : n + 1 = 3 ^ w) (hgrow : w < w') : n + 1 < 3 ^ w' := by
  rw [hcarry]
  exact Nat.pow_lt_pow_right (by omega) hgrow

end Langlib.Computability.Unshackled.FixedCounter
