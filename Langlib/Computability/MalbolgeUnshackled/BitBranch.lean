import Langlib.Computability.MalbolgeUnshackled.LowTrit

/-!
# A reusable branch through the natural bits zero and one

Jumping through zero reaches a no-op at address one, then a stable jump at
two; jumping through one reaches the stable jump directly. The optional
no-op advances the data pointer to the other continuation record. On both
paths address one is encrypted exactly once, within its no-op orbit.
This requires initialized low memory, not the loader's initial code there.
-/
namespace Langlib.Computability.Unshackled.Runtime.BitBranch
open Langlib.Common Langlib.MalbolgeUnshackled Routing

structure Layout (m : Memory) : Prop where
  zero : ∃ k, printableCode? (m.get (Value.ofNat 0)) = some k
  one : ∃ k, (k = 74 ∨ k = 70) ∧ m.get (Value.ofNat 1) = Value.ofNat k
  jump : m.get (Value.ofNat 2) = Value.ofNat 96

theorem nop_phase {k : Nat} (h : k = 74 ∨ k = 70) :
    decode (Value.ofNat k) (Value.ofNat 1).modClass = .nop ∧
    printableCode? (Value.ofNat k) = some k ∧ (encrypt k = 74 ∨ encrypt k = 70) := by
  rcases h with rfl | rfl <;> decide

theorem nop_not_loadable {k : Nat} (h : k = 74 ∨ k = 70) :
    Instr.ofOpcode? ((k + 1) % 94) = none := by
  rcases h with rfl | rfl <;> decide

def prefixMemory (m : Memory) (b : Bool) (k0 k1 : Nat) : Memory :=
  (if b then m else m.set (Value.ofNat 0) (Value.ofNat (encrypt k0))).set
    (Value.ofNat 1) (Value.ofNat (encrypt k1))

private theorem prefix_frame (m : Memory) (b : Bool) (k0 k1 : Nat) (x : Value)
    (h0 : x ≠ Value.ofNat 0) (h1 : x ≠ Value.ofNat 1) :
    (prefixMemory m b k0 k1).get x = m.get x := by
  cases b <;> simp [prefixMemory,get_set_ne,h0.symm,h1.symm]

private theorem prefix_layout {m : Memory} (h : Layout m) (b : Bool) {k0 k1 : Nat}
    (h0 : printableCode? (m.get (Value.ofNat 0)) = some k0)
    (hk : k1 = 74 ∨ k1 = 70) : Layout (prefixMemory m b k0 k1) := by
  constructor
  · cases b
    · simp only [prefixMemory,Bool.false_eq_true,if_false,get_set_nat,reduceIte]
      exact printable_after h0
    · simpa [prefixMemory,get_set_nat] using h.zero
  · exact ⟨encrypt k1,(nop_phase hk).2.2,get_set_self _ _ _⟩
  · rw [prefix_frame _ _ _ _ _ (by decide) (by decide)]; exact h.jump

/-- The conditional prefix reaches the same stable jump, with different
positions in the two-entry continuation record. -/
private theorem branch_prefix {s : State} {C D k0 k1 : Nat} (b : Bool)
    (hc : s.c = Value.ofNat C) (hd : s.d = Value.ofNat D)
    (hj : decode (s.mem.get (Value.ofNat C)) (Value.ofNat C).modClass = .jmp)
    (hv : s.mem.get (Value.ofNat D) = LowTrit.bit b)
    (h0 : printableCode? (s.mem.get (Value.ofNat 0)) = some k0)
    (hk : k1 = 74 ∨ k1 = 70) (h1 : s.mem.get (Value.ofNat 1) = Value.ofNat k1) :
    run? (if b then 1 else 2) s = some { s with
      mem := prefixMemory s.mem b k0 k1,
      c := Value.ofNat 2, d := Value.ofNat (D + if b then 1 else 2) } := by
  cases b
  · let u : State := { s with
      mem := s.mem.set (Value.ofNat 0) (Value.ofNat (encrypt k0)),
      c := Value.ofNat 1, d := Value.ofNat (D + 1) }
    have hs : step1 s = some u := jump hc hd hj hv h0
    have hu : step1 u = some { u with
        mem := u.mem.set (Value.ofNat 1) (Value.ofNat (encrypt k1)),
        c := Value.ofNat 2, d := Value.ofNat (D + 2) } := by
      have hh := noop (s := u) (C := 1) (D := D + 1) rfl rfl
        (by simp [u,get_set_nat,h1]; exact (nop_phase hk).1)
        (by simp [u,get_set_nat,h1]; exact (nop_phase hk).2.1)
      simpa only [Nat.add_assoc] using hh
    change (step1 s).bind (fun t => (step1 t).bind some) = _
    rw [hs,Option.bind_some,hu,Option.bind_some]
    rfl
  · have hs := jump hc hd hj hv (by simpa only [↓reduceIte] using h1 ▸ (nop_phase hk).2.1)
    change (step1 s).bind some = _
    rw [hs,Option.bind_some]
    rfl

def Destinations (m : Memory) (T0 T1 : Nat) : Prop :=
  ∀ a ∈ ([T0,T1] : List Nat), ∃ k, printableCode? (m.get (Value.ofNat a)) = some k

structure Trace (T0 T1 n : Nat) (s t : State) : Prop where
  run : run? n s = some t
  layout : Layout t.mem
  destinations : Destinations t.mem T0 T1
  frame : ∀ x, x ≠ Value.ofNat 0 → x ≠ Value.ofNat 1 →
    x ≠ Value.ofNat T0 → x ≠ Value.ofNat T1 → t.mem.get x = s.mem.get x
  acc : t.a = s.a
  width : t.rotWidth = s.rotWidth
  maxWidth : t.maxWidth = s.maxWidth
  input : t.input = s.input
  output : t.output = s.output
  outClosed : t.outClosed = s.outClosed

/-- A real two/three-step branch. The flag and continuation records are
preserved provided the caller places them outside the stated write frame.
Both branch destinations remain printable, and low-memory code stays callable. -/
theorem call {s : State} {C D T0 T1 : Nat} (b : Bool) (h : Layout s.mem)
    (hc : s.c = Value.ofNat C) (hd : s.d = Value.ofNat D) (hD : 3 ≤ D)
    (hj : decode (s.mem.get (Value.ofNat C)) (Value.ofNat C).modClass = .jmp)
    (hv : s.mem.get (Value.ofNat D) = LowTrit.bit b)
    (htrue : s.mem.get (Value.ofNat (D + 1)) = Value.ofNat T1)
    (hfalse : s.mem.get (Value.ofNat (D + 2)) = Value.ofNat T0)
    (hT0 : 3 ≤ T0) (hT1 : 3 ≤ T1) (hTargets : Destinations s.mem T0 T1) :
    ∃ t, Trace T0 T1 (if b then 2 else 3) s t ∧
      t.c = Value.ofNat ((if b then T1 else T0) + 1) ∧
      t.d = Value.ofNat (D + if b then 2 else 3) := by
  obtain ⟨k0,h0⟩ := h.zero
  obtain ⟨k1,hk,h1⟩ := h.one
  let u : State := { s with
    mem := prefixMemory s.mem b k0 k1,
    c := Value.ofNat 2, d := Value.ofNat (D + if b then 1 else 2) }
  have hu : run? (if b then 1 else 2) s = some u := branch_prefix b hc hd hj hv h0 hk h1
  have hul : Layout u.mem := prefix_layout h b h0 hk
  let target := if b then T1 else T0
  have htarget : 3 ≤ target := by dsimp [target]; split <;> assumption
  have htargetmem : u.mem.get (Value.ofNat target) = s.mem.get (Value.ofNat target) :=
    prefix_frame _ _ _ _ _ (ofNat_ne (by omega)) (ofNat_ne (by omega))
  obtain ⟨kt,hkt⟩ := hTargets target (by cases b <;> simp [target])
  let t : State := { u with
    mem := u.mem.set (Value.ofNat target) (Value.ofNat (encrypt kt)),
    c := Value.ofNat (target + 1), d := Value.ofNat (D + if b then 2 else 3) }
  have ht : step1 u = some t := by
    have hh := jump (s := u) (C := 2) (D := D + if b then 1 else 2) (T := target) rfl rfl
      (by rw [hul.jump]; decide)
      (by rw [prefix_frame _ _ _ _ _ (ofNat_ne (by cases b <;> simp))
          (ofNat_ne (by cases b <;> simp; omega))]
          cases b <;> assumption)
      (by rw [htargetmem]; exact hkt)
    cases b <;> simpa [t,Nat.add_assoc] using hh
  have hf x (hx : x ≠ Value.ofNat target) : t.mem.get x = u.mem.get x := get_set_ne _ hx.symm _
  have htf x (hx0 : x ≠ Value.ofNat 0) (hx1 : x ≠ Value.ofNat 1)
      (hxT : x ≠ Value.ofNat target) : t.mem.get x = s.mem.get x := by
    rw [hf x hxT]; exact prefix_frame _ _ _ _ x hx0 hx1
  have htl : Layout t.mem := by
    constructor
    · rw [hf _ (ofNat_ne (by omega))]; exact hul.zero
    · rw [hf _ (ofNat_ne (by omega))]; exact hul.one
    · rw [hf _ (ofNat_ne (by omega))]; exact hul.jump
  refine ⟨t,⟨?_,htl,?_,?_,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl,rfl⟩
  · have he : (if b then 2 else 3) = (if b then 1 else 2) + 1 := by cases b <;> rfl
    rw [he,run?_add,hu,Option.bind_some]
    change (step1 u).bind some = _
    rw [ht,Option.bind_some]
  · intro a ha
    by_cases he : a = target
    · subst a
      rw [show t.mem.get (Value.ofNat target) = Value.ofNat (encrypt kt) from get_set_self _ _ _]
      exact printable_after hkt
    · have hb : 3 ≤ a := by simp at ha; rcases ha with rfl | rfl <;> assumption
      rw [htf _ (ofNat_ne (by omega)) (ofNat_ne (by omega)) (ofNat_ne he)]
      exact hTargets a ha
  · intro x hx0 hx1 hxT0 hxT1
    exact htf x hx0 hx1 (by cases b <;> assumption)

end Langlib.Computability.Unshackled.Runtime.BitBranch
