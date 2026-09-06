import Langlib.Computability.MalbolgeUnshackled.Runtime

/-! Natural-address control steps, including their concrete memory updates.
Shared by the marker and width-growth routes. -/
namespace Langlib.Computability.Unshackled.Runtime.Routing
open Langlib.Common Langlib.MalbolgeUnshackled

theorem get_set_nat (m : Memory) (a b : Nat) (v : Value) :
    (m.set (Value.ofNat a) v).get (Value.ofNat b) =
      if a = b then v else m.get (Value.ofNat b) := by
  by_cases h : a = b
  · subst b; simp [get_set_self]
  · rw [if_neg h, get_set_ne _ (ofNat_ne h)]

theorem jump {s : State} {C D T k : Nat}
    (hc : s.c = Value.ofNat C) (hd : s.d = Value.ofNat D)
    (hj : decode (s.mem.get (Value.ofNat C)) (Value.ofNat C).modClass = .jmp)
    (hp : s.mem.get (Value.ofNat D) = Value.ofNat T)
    (hk : printableCode? (s.mem.get (Value.ofNat T)) = some k) :
    step1 s = some { s with
      mem := s.mem.set (Value.ofNat T) (Value.ofNat (encrypt k)),
      c := Value.ofNat (T + 1), d := Value.ofNat (D + 1) } := by
  have hh := step1_jmp (s := s) (by rw [hc]; exact hj)
    (by rw [hd, hp]; exact hk)
  simpa only [hd, hp, succ_ofNat] using hh

theorem move {s : State} {C D T k : Nat}
    (hc : s.c = Value.ofNat C) (hd : s.d = Value.ofNat D)
    (hj : decode (s.mem.get (Value.ofNat C)) (Value.ofNat C).modClass = .movd)
    (hp : s.mem.get (Value.ofNat D) = Value.ofNat T)
    (hk : printableCode? (s.mem.get (Value.ofNat C)) = some k)
    (hw : (Value.ofNat T).width ≤ s.maxWidth) :
    step1 s = some { s with
      mem := s.mem.set (Value.ofNat C) (Value.ofNat (encrypt k)),
      c := Value.ofNat (C + 1), d := Value.ofNat (T + 1) } := by
  have hh := step1_movd (s := s) (by rw [hc]; exact hj) (by rw [hc]; exact hk)
  rw [hd, hp, if_neg (by omega), if_neg (by omega)] at hh
  simpa only [hc, succ_ofNat] using hh

theorem noop {s : State} {C D k : Nat}
    (hc : s.c = Value.ofNat C) (hd : s.d = Value.ofNat D)
    (hj : decode (s.mem.get (Value.ofNat C)) (Value.ofNat C).modClass = .nop)
    (hk : printableCode? (s.mem.get (Value.ofNat C)) = some k) :
    step1 s = some { s with
      mem := s.mem.set (Value.ofNat C) (Value.ofNat (encrypt k)),
      c := Value.ofNat (C + 1), d := Value.ofNat (D + 1) } := by
  have hh := step1_nop (s := s) (by rw [hc]; exact hj) (by rw [hc]; exact hk)
  simpa only [hc, hd, succ_ofNat] using hh

theorem printable_after {v : Value} {k : Nat}
    (h : printableCode? v = some k) :
    ∃ j, printableCode? (Value.ofNat (encrypt k)) = some j := by
  have hb := printableCode?_bounds h
  have he := encrypt_range hb.1 hb.2
  exact ⟨encrypt k, printableCode?_ofNat he.1 he.2⟩

end Langlib.Computability.Unshackled.Runtime.Routing
