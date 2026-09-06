import Langlib.Computability.MalbolgeUnshackled.Runtime

/-!
# Writing runtime code during initialization

The permissive loader accepts natural data words outside the printable
instruction range. A crazy/move/crazy sequence converts such a word into
executable code at a separate address. This is the operational bridge for
the three no-op synthesis pairs in `ReusableGrowth.initializer_values`.
The initializer is single-use; the code it constructs can be reusable.
-/

namespace Langlib.Computability.Unshackled.Runtime

open Langlib.Common Langlib.MalbolgeUnshackled

set_option maxHeartbeats 1000000 in
/-- Three actual steps synthesize a value at `E+1`. The scratch record at
`D` contains the first operand and then pointer `E`; the target contains
the second operand. Code and scratch are disjoint from the target. The
move fits the established address width and does not change rotation width.
This theorem requires no arithmetic value to be a source character. -/
theorem initialize_cell {s : State} {A D E : Nat} (codes : Nat → Nat)
    (hc : s.c = Value.ofNat A) (hd : s.d = Value.ofNat D)
    (hsep : A + 3 ≤ D)
    (hE : ∀ i < 3, E + 1 ≠ A + i)
    (hED : E + 1 ≠ D)
    (hptr : s.mem.get (Value.ofNat (D + 1)) = Value.ofNat E)
    (hwidth : (Value.ofNat E).width ≤ s.maxWidth)
    (hdec : ∀ i < 3, decode (s.mem.get (Value.ofNat (A + i)))
      (Value.ofNat (A + i)).modClass = if i = 1 then .movd else .crazy)
    (hprint : ∀ i < 3, printableCode? (s.mem.get (Value.ofNat (A + i))) = some (codes i)) :
    ∃ t, run? 3 s = some t ∧ t.c = Value.ofNat (A + 3) ∧ t.d = Value.ofNat (E + 2)
      ∧ t.a = Value.crz (Value.crz s.a (s.mem.get (Value.ofNat D)))
        (s.mem.get (Value.ofNat (E + 1)))
      ∧ t.mem.get (Value.ofNat (E + 1)) = t.a
      ∧ t.mem.get (Value.ofNat D) = Value.crz s.a (s.mem.get (Value.ofNat D))
      ∧ (∀ x, x ≠ Value.ofNat D → x ≠ Value.ofNat (E + 1) →
        (∀ i < 3, x ≠ Value.ofNat (A + i)) → t.mem.get x = s.mem.get x)
      ∧ t.rotWidth = s.rotWidth ∧ t.maxWidth = s.maxWidth
      ∧ t.input = s.input ∧ t.output = s.output ∧ t.outClosed = s.outClosed := by
  let v := Value.crz s.a (s.mem.get (Value.ofNat D))
  let result := Value.crz v (s.mem.get (Value.ofNat (E + 1)))
  let s₁ : State := { s with
    a := v,
    mem := (s.mem.set (Value.ofNat D) v).set (Value.ofNat A) (Value.ofNat (encrypt (codes 0))),
    c := Value.ofNat (A + 1), d := Value.ofNat (D + 1) }
  have hr₁ : step1 s = some s₁ := by
    have hh := step1_crazy (s := s) (code := codes 0)
      (by rw [hc]; simpa using hdec 0 (by omega))
      (by rw [hd, hc]; exact ofNat_ne (by omega))
      (by rw [hc]; simpa using hprint 0 (by omega))
    simpa only [hc, hd, succ_ofNat] using hh
  have hf₁ (x : Value) (hxD : x ≠ Value.ofNat D) (hxA : x ≠ Value.ofNat A) :
      s₁.mem.get x = s.mem.get x := by
    dsimp [s₁]
    rw [get_set_ne _ hxA.symm, get_set_ne _ hxD.symm]
  have hptr₁ : s₁.mem.get s₁.d = Value.ofNat E := by
    change s₁.mem.get (Value.ofNat (D + 1)) = _
    rw [hf₁ _ (ofNat_ne (by omega)) (ofNat_ne (by omega)), hptr]
  let s₂ : State := { s₁ with
    mem := s₁.mem.set (Value.ofNat (A + 1)) (Value.ofNat (encrypt (codes 1))),
    c := Value.ofNat (A + 2), d := Value.ofNat (E + 1) }
  have hr₂ : step1 s₁ = some s₂ := by
    have hh := step1_movd (s := s₁) (code := codes 1)
      (by change decode (s₁.mem.get (Value.ofNat (A + 1))) _ = _
          rw [hf₁ _ (ofNat_ne (by omega)) (ofNat_ne (by omega))]
          simpa using hdec 1 (by omega))
      (by change printableCode? (s₁.mem.get (Value.ofNat (A + 1))) = _
          rw [hf₁ _ (ofNat_ne (by omega)) (ofNat_ne (by omega))]
          exact hprint 1 (by omega))
    rw [hptr₁, if_neg (by exact Nat.not_lt.mpr hwidth), if_neg (by exact Nat.not_lt.mpr hwidth)] at hh
    simpa only [show s₁.c = Value.ofNat (A + 1) from rfl, succ_ofNat,
      show A + 1 + 1 = A + 2 by omega] using hh
  have hf₂ (x : Value) (hxD : x ≠ Value.ofNat D) (hx₀ : x ≠ Value.ofNat A)
      (hx₁ : x ≠ Value.ofNat (A + 1)) : s₂.mem.get x = s.mem.get x := by
    change (s₁.mem.set (Value.ofNat (A + 1)) _).get x = _
    rw [get_set_ne _ hx₁.symm, hf₁ x hxD hx₀]
  have hvalue₂ : s₂.mem.get s₂.d = s.mem.get (Value.ofNat (E + 1)) := by
    exact hf₂ _ (ofNat_ne hED) (ofNat_ne (by have := hE 0 (by omega); omega))
      (ofNat_ne (hE 1 (by omega)))
  let t : State := { s₂ with
    a := result,
    mem := (s₂.mem.set (Value.ofNat (E + 1)) result).set
      (Value.ofNat (A + 2)) (Value.ofNat (encrypt (codes 2))),
    c := Value.ofNat (A + 3), d := Value.ofNat (E + 2) }
  have hrt : step1 s₂ = some t := by
    have hh := step1_crazy (s := s₂) (code := codes 2)
      (by change decode (s₂.mem.get (Value.ofNat (A + 2))) _ = _
          rw [hf₂ _ (ofNat_ne (by omega)) (ofNat_ne (by omega)) (ofNat_ne (by omega))]
          simpa using hdec 2 (by omega))
      (ofNat_ne (hE 2 (by omega)))
      (by change printableCode? (s₂.mem.get (Value.ofNat (A + 2))) = _
          rw [hf₂ _ (ofNat_ne (by omega)) (ofNat_ne (by omega)) (ofNat_ne (by omega))]
          exact hprint 2 (by omega))
    rw [hvalue₂] at hh
    simpa only [show s₂.c = Value.ofNat (A + 2) from rfl,
      show s₂.d = Value.ofNat (E + 1) from rfl, succ_ofNat,
      show A + 2 + 1 = A + 3 by omega, show E + 1 + 1 = E + 2 by omega] using hh
  refine ⟨t, ?_, rfl, rfl, rfl, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · change (step1 s).bind (fun u => (step1 u).bind (fun v => (step1 v).bind some)) = _
    rw [hr₁, Option.bind_some, hr₂, Option.bind_some, hrt, Option.bind_some]
  · change ((s₂.mem.set (Value.ofNat (E + 1)) result).set _ _).get _ = _
    rw [get_set_ne _ (ofNat_ne (Ne.symm (hE 2 (by omega)))), get_set_self]
  · dsimp [t, s₂, s₁]
    rw [get_set_ne _ (ofNat_ne (by omega)), get_set_ne _ (ofNat_ne hED),
      get_set_ne _ (ofNat_ne (by omega)), get_set_ne _ (ofNat_ne (by omega)), get_set_self]
  · intro x hxD hxE hx
    change ((s₂.mem.set (Value.ofNat (E + 1)) result).set _ _).get x = _
    rw [get_set_ne _ (Ne.symm (hx 2 (by omega))), get_set_ne _ hxE.symm]
    exact hf₂ x hxD (by simpa using hx 0 (by omega)) (hx 1 (by omega))

end Langlib.Computability.Unshackled.Runtime
