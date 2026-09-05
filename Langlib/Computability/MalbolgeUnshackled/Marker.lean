import Langlib.Computability.MalbolgeUnshackled.Runtime
import Langlib.Computability.MalbolgeUnshackled.Rotation

/-!
# Regenerating a one-marker without consuming constants

A rotated one contains only zero and one trits. An all-ones accumulator
clears it; the constant path `...111 → 2 → ...1110` then writes one.
The constants survive every use, and the initial accumulator can be loaded
by rotating an all-ones cell, independently of the rotation width.
-/

namespace Langlib.Computability.Unshackled.Runtime.Marker

open Langlib.MalbolgeUnshackled

def ones : Value := uniform .t1
def mask : Value := Value.mk' .t1 [.t0]

/-- Naturals whose ternary expansion contains no twos, with no width bound. -/
def ZeroOne (v : Value) : Prop := v.lead = .t0 ∧ ∀ i, v.trit i ≠ .t2

theorem zeroOne_power (k : Nat) : ZeroOne (Value.ofNat (3 ^ k)) := by
  rw [← digitAt_one_eq]
  refine ⟨rfl, ?_⟩
  intro i
  rw [trit_digitAt]
  split <;> decide

theorem clear {v : Value} (hv : ZeroOne v) : Value.crz ones v = Value.zero := by
  apply ext_of_trits (crz_normalized _ _) (uniform_normalized .t0)
  · rw [crz_lead, hv.1]; rfl
  · intro i
    rw [crz_trit]
    change crzTrit .t1 (v.trit i) = .t0
    have hh := hv.2 i
    cases he : v.trit i <;> simp_all [crzTrit]

theorem constants :
    Value.crz Value.zero ones = ones ∧
    Value.crz ones (Value.ofNat 2) = Value.ofNat 2 ∧
    Value.crz (Value.ofNat 2) mask = mask ∧
    Value.crz mask Value.zero = Value.ofNat 1 := by decide

/-- Rotating the all-ones constant loads the accumulator without modifying
that constant. No input instruction or EOF assumption is involved. -/
theorem rotate_ones (w : Nat) : Value.rot w ones = ones := by
  have hm : Value.mk' .t1 (List.replicate w Trit.t1) = ones := by
    have hh := window_eq (uniform_normalized .t1) w
    simpa [Value.padTo, uniform, ones] using hh
  have hh := rot_window .t1 (List.replicate w Trit.t1)
  simpa only [List.length_replicate, hm, List.rotate_replicate] using hh

end Langlib.Computability.Unshackled.Runtime.Marker
