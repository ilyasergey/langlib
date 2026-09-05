import Langlib.Computability.MalbolgeUnshackled.Runtime

/-!
# Width growth with a return from distant memory

A `movd`, three no-ops, and another `movd` enter a wide address and return
via its periodic background. The code pointer stays in finite code all
along. This theorem accounts for the actual five-step execution and its
code writes; it does not yet restore those code phases for another call.
-/

namespace Langlib.Computability.Unshackled.Runtime

open Langlib.Common Langlib.MalbolgeUnshackled

/-- A positive power of three has the same fill phase, independently of
how large the current rotation width has become. -/
theorem pow3_mod6 : ∀ n : Nat, 0 < n → 3 ^ n % 6 = 3
  | 0, h => by omega
  | n + 1, _ => by
    by_cases h : n = 0
    · subst n; decide
    · rw [Nat.pow_succ, Nat.mul_mod, pow3_mod6 n (by omega)]

/-- Four successor steps after the wide address always reach residue one.
Thus the return word is a fixed entry of the original fill. -/
theorem growth_fill (m : Memory) {w : Nat} (hw : 2 ≤ w) :
    fillAt m (3 ^ (w - 1) + 4) = m.rest.getD 1 Value.zero := by
  rw [fillAt, mod6_ofNat, Nat.add_mod, pow3_mod6 (w - 1) (by omega)]

private theorem succ_iterate_nat (n k : Nat) :
    (Value.succ^[k]) (Value.ofNat n) = Value.ofNat (n + k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, succ_ofNat]
    simp only [Nat.add_assoc]

set_option maxHeartbeats 1000000 in
/-- Five concrete instructions grow the width and return `d` to a fixed
fill-derived value. No remote return table is assumed initialized.

The first `movd` reads the result of rotating one at width `w`; the second
reads untouched memory at `3^(w-1)+4`. Only the five code cells are written.
Their post-encryption words are exposed so a caller must account for phases.
The source operand and all counter cells outside that block survive. -/
theorem grow_return {s : State} {A w : Nat} (codes : Nat → Nat)
    (hc : s.c = Value.ofNat A) (hw : s.rotWidth = w) (hwmin : 2 ≤ w)
    (hm : s.maxWidth < w)
    (hsource : s.mem.get s.d = Value.rot w (Value.ofNat 1))
    (hfar : A + 4 < 3 ^ (w - 1) + 4)
    (hfresh : ¬ s.mem.cells.contains (Value.ofNat (3 ^ (w - 1) + 4)))
    (hreturnWidth : (s.mem.rest.getD 1 Value.zero).width ≤ w)
    (hdec : ∀ i < 5, decode (s.mem.get (Value.ofNat (A + i)))
      (Value.ofNat (A + i)).modClass = if i = 0 ∨ i = 4 then .movd else .nop)
    (hprint : ∀ i < 5, printableCode? (s.mem.get (Value.ofNat (A + i))) = some (codes i)) :
    ∃ t, run? 5 s = some t ∧ t.c = Value.ofNat (A + 5)
      ∧ t.d = (s.mem.rest.getD 1 Value.zero).succ
      ∧ t.rotWidth = 2 * w ∧ t.maxWidth = w ∧ t.a = s.a
      ∧ (∀ i < 5, t.mem.get (Value.ofNat (A + i)) = Value.ofNat (encrypt (codes i)))
      ∧ (∀ x, (∀ i < 5, x ≠ Value.ofNat (A + i)) → t.mem.get x = s.mem.get x)
      ∧ t.input = s.input ∧ t.output = s.output ∧ t.outClosed = s.outClosed := by
  let N := 3 ^ (w - 1)
  let ret := s.mem.rest.getD 1 Value.zero
  let s₁ : State := { s with
    mem := s.mem.set (Value.ofNat A) (Value.ofNat (encrypt (codes 0))),
    c := Value.ofNat (A + 1), d := Value.ofNat (N + 1), rotWidth := 2 * w, maxWidth := w }
  have h₁ : step1 s = some s₁ := by
    have hh := step1_movd (s := s) (code := codes 0)
      (by rw [hc]; simpa using hdec 0 (by omega))
      (by rw [hc]; simpa using hprint 0 (by omega))
    rw [hsource, width_rot_one w (by omega), if_pos hm, if_pos hm, hw,
      growRotWidth_double, rot_one w (by omega), hc, succ_ofNat, succ_ofNat] at hh
    exact hh
  have hf₁ : ∀ x, x ≠ Value.ofNat A → s₁.mem.get x = s.mem.get x := by
    intro x hx
    exact get_set_ne _ hx.symm _
  obtain ⟨s₄, hr₄, ha₄, hc₄, hd₄, hcells₄, hf₄, hi₄, ho₄, hx₄, hw₄, hm₄⟩ :=
    nop_run 3 (s₀ := s₁) (c₀ := A + 1) (fun i => codes (1 + i)) rfl
      (fun i hi => by
        rw [hf₁ _ (ofNat_ne (by omega))]
        have hh := hdec (1 + i) (by omega)
        rw [if_neg (by omega)] at hh
        simpa only [Nat.add_assoc] using hh)
      (fun i hi => by
        rw [hf₁ _ (ofNat_ne (by omega))]
        simpa only [Nat.add_assoc] using hprint (1 + i) (by omega))
  have hcode₄ : s₄.mem.get (Value.ofNat (A + 4)) = s.mem.get (Value.ofNat (A + 4)) := by
    rw [hf₄ _ (fun i hi => ofNat_ne (by omega)), hf₁ _ (ofNat_ne (by omega))]
  have hremote : s₄.mem.get s₄.d = ret := by
    rw [hd₄]
    change s₄.mem.get ((Value.succ^[3]) (Value.ofNat (N + 1))) = _
    rw [succ_iterate_nat]
    have hn : N + 1 + 3 = 3 ^ (w - 1) + 4 := by simp [N, Nat.add_assoc]
    rw [hn, hf₄ _ (fun i hi => ofNat_ne (by omega)), hf₁ _ (ofNat_ne (by omega)),
      get_of_not_mem hfresh, growth_fill s.mem hwmin]
  let t : State := { s₄ with
    mem := s₄.mem.set (Value.ofNat (A + 4)) (Value.ofNat (encrypt (codes 4))),
    c := Value.ofNat (A + 5), d := ret.succ, maxWidth := w }
  have ht : step1 s₄ = some t := by
    have hh := step1_movd (s := s₄) (code := codes 4)
      (by rw [hc₄, show A + 1 + 3 = A + 4 by omega, hcode₄]; simpa using hdec 4 (by omega))
      (by rw [hc₄, show A + 1 + 3 = A + 4 by omega, hcode₄]; exact hprint 4 (by omega))
    rw [hremote, hm₄, show s₁.maxWidth = w from rfl,
      if_neg (by exact Nat.not_lt.mpr hreturnWidth), if_neg (by exact Nat.not_lt.mpr hreturnWidth),
      hc₄, succ_ofNat] at hh
    simpa only [show A + 1 + 3 = A + 4 by omega,
      show A + 1 + 3 + 1 = A + 5 by omega] using hh
  refine ⟨t, ?_, rfl, rfl, hw₄, rfl, ha₄, ?_, ?_, hi₄, ho₄, hx₄⟩
  · rw [show (5 : Nat) = 1 + (3 + 1) from rfl, run?_add, run?_one, h₁,
      Option.bind_some, run?_add, hr₄, Option.bind_some, run?_one, ht]
  · intro i hi
    by_cases hi4 : i = 4
    · subst i; exact get_set_self _ _ _
    · change (s₄.mem.set (Value.ofNat (A + 4)) _).get _ = _
      rw [get_set_ne _ (ofNat_ne (by omega))]
      by_cases hi0 : i = 0
      · subst i
        rw [hf₄ _ (fun j hj => ofNat_ne (by omega))]
        exact get_set_self _ _ _
      · have hh := hcells₄ (i - 1) (by omega)
        simpa only [show A + 1 + (i - 1) = A + i by omega,
          show 1 + (i - 1) = i by omega] using hh
  · intro x hx
    change (s₄.mem.set (Value.ofNat (A + 4)) _).get x = _
    rw [get_set_ne _ (Ne.symm (hx 4 (by omega))),
      hf₄ _ (fun i hi => by simpa only [Nat.add_assoc] using hx (1 + i) (by omega)),
      hf₁ _ (by simpa using hx 0 (by omega))]

end Langlib.Computability.Unshackled.Runtime
