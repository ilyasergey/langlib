import Langlib.Computability.MalbolgeUnshackled.Runtime
import Langlib.Computability.MalbolgeUnshackled.Rotation

/-!
# An executable rotation loop with a reusable pointer reset

One pass executes six MU instructions: a rotate with restoration and return,
then a pointer reset with restoration and return. Both code blocks and all
return-table entries survive every pass. The loop operates on a fixed cell
and preserves the rotation width. The number of passes below is a proof
index; a runtime marker test and an exit branch still need to be attached.
-/

namespace Langlib.Computability.Unshackled.Runtime.RotationLoop

open Langlib.Common Langlib.MalbolgeUnshackled

/-- Fixed code and return records. The mutable operand is at 3000; the
printable landing cells at 152 and 247 are not executed. -/
def cells : List (Nat × Nat) :=
  [(153, 74), (154, 38), (248, 74), (249, 37),
   (2998, 248), (2999, 152), (3001, 153), (3002, 247), (3003, 2997)]

def Static (m : Memory) : Prop :=
  ∀ a v, (a, v) ∈ cells → m.get (Value.ofNat a) = Value.ofNat v

private theorem static_disjoint {a v : Nat} (h : (a, v) ∈ cells) :
    a ≠ 3000 ∧ a ≠ 152 ∧ a ≠ 247 := by
  have ha : a ∈ cells.map Prod.fst := List.mem_map.mpr ⟨(a,v), h, rfl⟩
  simp [cells] at ha
  rcases ha with h | h | h | h | h | h | h | h | h <;> omega

theorem Static.frame {m m' : Memory} (h : Static m)
    (hf : ∀ x, x ≠ Value.ofNat 3000 → x ≠ Value.ofNat 152 → x ≠ Value.ofNat 247 →
      m'.get x = m.get x) : Static m' := by
  intro a v ha
  have hd := static_disjoint ha
  rw [hf _ (ofNat_ne hd.1) (ofNat_ne hd.2.1) (ofNat_ne hd.2.2)]
  exact h a v ha

/-- A callable loop header, with the current operand named explicitly. -/
structure Ready (w : Nat) (v : Value) (s : State) : Prop where
  code : s.c = Value.ofNat 153
  data : s.d = Value.ofNat 3000
  width : s.rotWidth = w
  maxWidth : (Value.ofNat 2997).width ≤ s.maxWidth
  operand : s.mem.get (Value.ofNat 3000) = v
  static : Static s.mem
  landing₀ : ∃ k, printableCode? (s.mem.get (Value.ofNat 152)) = some k
  landing₁ : ∃ k, printableCode? (s.mem.get (Value.ofNat 247)) = some k

private theorem encrypted_printable {v : Value} {k : Nat}
    (h : printableCode? v = some k) :
    printableCode? (Value.ofNat (encrypt k)) = some (encrypt k) := by
  have hb := printableCode?_bounds h
  have he := encrypt_range hb.1 hb.2
  exact printableCode?_ofNat he.1 he.2

set_option maxHeartbeats 1000000 in
/-- One complete pass is six actual interpreter steps, without a supplied
step-existence hypothesis. In particular it restores both working cells
and the pointer reset does not change the rotation width. -/
theorem pass {w : Nat} {v : Value} {s : State} (h : Ready w v s) :
    ∃ t, run? 6 s = some t ∧ Ready w (Value.rot w v) t ∧
      (∀ x, x ≠ Value.ofNat 3000 → x ≠ Value.ofNat 152 → x ≠ Value.ofNat 247 →
        t.mem.get x = s.mem.get x) ∧
      t.input = s.input ∧ t.output = s.output ∧ t.outClosed = s.outClosed := by
  obtain ⟨k₀, hk₀⟩ := h.landing₀
  obtain ⟨k₁, hk₁⟩ := h.landing₁
  obtain ⟨s₁, hr₁, ha₁, hc₁, hd₁, ht₁, hv₁, _, _, hf₁, hi₁, ho₁, hx₁, hw₁, hm₁⟩ :=
    work_call .rotate h.code h.data (by omega) (by omega) (by omega)
      (fun i hi => by omega)
      (h.static 153 74 (by decide))
      (by rw [decode_at_ofNat (by omega) (by omega)]; decide)
      (by rw [h.static 154 38 (by decide), decode_at_ofNat (by omega) (by omega)]; decide)
      (h.static 3001 153 (by decide)) (h.static 3002 247 (by decide)) hk₁
  have st₁ : Static s₁.mem := h.static.frame (fun x hx _ ht => hf₁ x hx ht)
  have hl₀ : printableCode? (s₁.mem.get (Value.ofNat 152)) = some k₀ := by
    rw [hf₁ _ (by decide) (by decide)]
    exact hk₀
  obtain ⟨t, hr₂, ha₂, hc₂, hd₂, ht₂, _, _, hf₂, hi₂, ho₂, hx₂, hw₂, hm₂⟩ :=
    movd_call hc₁
      (by rw [hd₁]; exact st₁ 3003 2997 (by decide))
      (by rw [hm₁]; exact h.maxWidth)
      (by omega) (by omega) (by omega)
      (st₁ 248 74 (by decide))
      (by rw [decode_at_ofNat (by omega) (by omega)]; decide)
      (by rw [st₁ 249 37 (by decide), decode_at_ofNat (by omega) (by omega)]; decide)
      (st₁ 2998 248 (by decide)) (st₁ 2999 152 (by decide)) hl₀
  have hf : ∀ x, x ≠ Value.ofNat 3000 → x ≠ Value.ofNat 152 → x ≠ Value.ofNat 247 →
      t.mem.get x = s.mem.get x := by
    intro x hx hp hq
    rw [hf₂ x hp, hf₁ x hx hq]
  refine ⟨t, ?_, ?_, hf, hi₂.trans hi₁, ho₂.trans ho₁, hx₂.trans hx₁⟩
  · rw [show (6 : Nat) = 3 + 3 from rfl, run?_add, hr₁, Option.bind_some]
    exact hr₂
  · refine ⟨hc₂, hd₂, hw₂.trans (hw₁.trans h.width), ?_, ?_, h.static.frame hf, ?_, ?_⟩
    · rw [hm₂, hm₁]; exact h.maxWidth
    · rw [hf₂ _ (by decide), hv₁, ha₁, h.width, h.operand]
      rfl
    · refine ⟨encrypt k₀, ?_⟩
      rw [ht₂]
      exact encrypted_printable hk₀
    · refine ⟨encrypt k₁, ?_⟩
      rw [hf₂ _ (by decide), ht₁]
      exact encrypted_printable hk₁

/-- Repeated passes are real runs of the same finite code, even when the
number of passes is larger than any compile-time bound. This theorem does
not insert a runtime exit test. -/
theorem passes {w : Nat} {v : Value} {s : State} (h : Ready w v s) (n : Nat) :
    ∃ t, run? (6 * n) s = some t ∧ Ready w (rotateTimes w n v) t ∧
      (∀ x, x ≠ Value.ofNat 3000 → x ≠ Value.ofNat 152 → x ≠ Value.ofNat 247 →
        t.mem.get x = s.mem.get x) ∧
      t.input = s.input ∧ t.output = s.output ∧ t.outClosed = s.outClosed := by
  induction n with
  | zero => exact ⟨s, rfl, h, fun _ _ _ _ => rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨u, hu, hru, hfu, hiu, hou, hxu⟩ := ih
    obtain ⟨t, ht, hrt, hft, hit, hot, hxt⟩ := pass hru
    refine ⟨t, ?_, hrt, ?_, hit.trans hiu, hot.trans hou, hxt.trans hxu⟩
    · rw [Nat.mul_succ, run?_add, hu, Option.bind_some]
      exact ht
    · intro x hx hp hq
      rw [hft x hx hp hq, hfu x hx hp hq]

/-- At exactly a full window of passes, the operand and callable layout
are restored. The accumulator and landing-cell encryption phases need not
be the same as on entry. -/
theorem full_cycle {w : Nat} {v : Value} {s : State} (h : Ready w v s)
    (hv : v.Normalized) (hw : v.width ≤ w) :
    ∃ t, run? (6 * w) s = some t ∧ Ready w v t ∧
      (∀ x, x ≠ Value.ofNat 3000 → x ≠ Value.ofNat 152 → x ≠ Value.ofNat 247 →
        t.mem.get x = s.mem.get x) ∧
      t.input = s.input ∧ t.output = s.output ∧ t.outClosed = s.outClosed := by
  simpa only [rotateTimes_full_cycle hv hw] using passes h w

end Langlib.Computability.Unshackled.Runtime.RotationLoop
