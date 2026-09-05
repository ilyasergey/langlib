import Langlib.Computability.MalbolgeUnshackled
import Mathlib.Data.List.Rotate

/-!
# Rotation windows for the fixed-counter runtime

The runtime scans a finite rotation window, while the window itself can
increase without bound between calls. The lemmas below relate the reference
`Value.rot` to list rotation, including normalization and padding. They are
value-level results; executing and branching on the scan belongs to the
runtime simulation.
-/

namespace Langlib.Computability.Unshackled.Runtime

open Langlib.MalbolgeUnshackled

theorem rot_window (lead : Trit) (xs : List Trit) :
    Value.rot xs.length (Value.mk' lead xs) = Value.mk' lead (xs.rotate 1) := by
  have hmap : (List.range xs.length).map (Value.mk' lead xs).trit = xs := by
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      simp only [List.getElem_map, List.getElem_range, trit_mk']
      exact getD_lt hi' lead
  have hdrop : (Value.mk' lead xs).low.drop xs.length = [] :=
    List.drop_eq_nil_of_le (width_mk'_le lead xs)
  unfold Value.rot
  rw [hmap]
  cases xs with
  | nil => simp
  | cons x xs =>
    rw [hdrop]
    change Value.mk' lead (xs ++ [x] ++ []) = _
    simp [List.rotate_cons_succ]

/-- Iterate the actual reference rotation, keeping the width fixed. -/
def rotateTimes (w : Nat) : Nat → Value → Value
  | 0, v => v
  | n + 1, v => Value.rot w (rotateTimes w n v)

theorem rotateTimes_window (lead : Trit) (xs : List Trit) (n : Nat) :
    rotateTimes xs.length n (Value.mk' lead xs) = Value.mk' lead (xs.rotate n) := by
  induction n with
  | zero => simp [rotateTimes]
  | succ n ih =>
    rw [rotateTimes, ih, ← List.length_rotate xs n, rot_window, List.rotate_rotate]

/-- Padding to the working width does not change a normalized value. -/
theorem window_eq {v : Value} (hv : v.Normalized) (w : Nat) :
    Value.mk' v.lead (Value.padTo w v.lead v.low) = v := by
  apply ext_of_trits (Value.normalized_mk' _ _) hv rfl
  intro i
  rw [trit_mk', getD_padTo]
  rfl

/-- A complete scan restores every value that fits in the working window. -/
theorem rotateTimes_full_cycle {v : Value} (hv : v.Normalized) {w : Nat}
    (hwidth : v.width ≤ w) : rotateTimes w w v = v := by
  let xs := Value.padTo w v.lead v.low
  have hlen : xs.length = w := length_padTo _ _ _ hwidth
  have h := rotateTimes_window v.lead xs w
  rw [hlen, window_eq hv] at h
  rw [h, ← hlen, List.rotate_length]
  exact window_eq hv w

/-- A one-trit marker reaches the low position exactly once per rotation
window. This supplies the termination measure for a future runtime scan;
it does not yet implement the low-trit test as MU instructions. -/
theorem marker_low {w : Nat} (hw : 0 < w) (n : Nat) :
    (rotateTimes w n (Value.ofNat 1)).trit 0 =
      if n % w = 0 then .t1 else .t0 := by
  let v := digitAt Trit.t1 0
  have hv : v.Normalized := digitAt_normalized (by decide) 0
  have heq : v = Value.ofNat 1 := digitAt_one_eq 0
  let xs := Value.padTo w v.lead v.low
  have hlen : xs.length = w := length_padTo _ _ _ (by change 1 ≤ w; omega)
  have h := rotateTimes_window v.lead xs n
  rw [hlen, window_eq hv] at h
  rw [← heq, h, trit_mk', List.getD_eq_getElem?_getD,
    List.getElem?_rotate (by omega), Nat.zero_add, hlen,
    ← List.getD_eq_getElem?_getD, getD_padTo]
  exact trit_digitAt .t1 0 (n % w)

/-- The marker is absent after every proper nonempty prefix of a scan. -/
theorem marker_no_early_return {w n : Nat} (hn : 0 < n) (hnw : n < w) :
    (rotateTimes w n (Value.ofNat 1)).trit 0 = .t0 := by
  rw [marker_low (by omega), Nat.mod_eq_of_lt hnw, if_neg (by omega)]

end Langlib.Computability.Unshackled.Runtime
