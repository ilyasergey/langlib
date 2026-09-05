import Langlib.Computability.MalbolgeUnshackled

/-!
# Reusable MU runtime operations

Fixed-cell counters need repeatable operations on their cells. A working
instruction is followed by a stable jump. The first jump encrypts the
working cell a second time, restoring its two-cycle word; the second jump
returns to the continuation. Unlike a no-op sweep, the specification below
accounts for the changed data operand and preserves the return table.
-/

namespace Langlib.Computability.Unshackled.Runtime

open Langlib.Common Langlib.MalbolgeUnshackled

/-- The two instructions that update both the accumulator and an operand. -/
inductive WorkOp where
  | crazy | rotate
  deriving DecidableEq, Repr

def WorkOp.instr : WorkOp → Instr
  | .crazy => .crazy
  | .rotate => .rotr

def WorkOp.apply : WorkOp → Nat → Value → Value → Value
  | .crazy, _, a, v => Value.crz a v
  | .rotate, w, _, v => Value.rot w v

/-- One actual machine step, including encryption and pointer increments. -/
theorem work_step (op : WorkOp) {s : State} {code : Nat}
    (hdec : decode (s.mem.get s.c) s.c.modClass = op.instr)
    (hsep : s.c ≠ s.d)
    (hcode : printableCode? (s.mem.get s.c) = some code) :
    step1 s = some { s with
      a := op.apply s.rotWidth s.a (s.mem.get s.d),
      mem := (s.mem.set s.d (op.apply s.rotWidth s.a (s.mem.get s.d))).set s.c
        (Value.ofNat (encrypt code)), c := s.c.succ, d := s.d.succ } := by
  cases op with
  | crazy => exact step1_crazy hdec hsep.symm hcode
  | rotate =>
    apply step1_eq hdec (by decide) (by decide) rfl
    rw [get_set_ne _ hsep.symm]
    exact hcode

set_option maxHeartbeats 800000 in
/-- Execute a work instruction and two stable jumps. The working word is
restored, the operand has its specified new value, and only the operand
and the printable return landing cell may differ from the entry memory.

`A` and `A+1` are the working and jumping code cells. The operand record
at `D` contains `[value, A, T]`. Execution resumes at `T+1`, since a jump
encrypts its landing cell and then increments the code pointer. -/
theorem work_call (op : WorkOp) {s : State} {A D T wt : Nat}
    (hc : s.c = Value.ofNat A) (hd : s.d = Value.ofNat D)
    (hsep : A + 2 ≤ D)
    (hTA : T ≠ A) (hTJ : T ≠ A + 1)
    (hTD : ∀ i < 3, T ≠ D + i)
    (hwork : s.mem.get (Value.ofNat A) = Value.ofNat 74)
    (hdec : decode (Value.ofNat 74) (Value.ofNat A).modClass = op.instr)
    (hjump : decode (s.mem.get (Value.ofNat (A + 1)))
      (Value.ofNat (A + 1)).modClass = .jmp)
    (hrestore : s.mem.get (Value.ofNat (D + 1)) = Value.ofNat A)
    (hreturn : s.mem.get (Value.ofNat (D + 2)) = Value.ofNat T)
    (hlanding : printableCode? (s.mem.get (Value.ofNat T)) = some wt) :
    ∃ t, run? 3 s = some t
      ∧ t.a = op.apply s.rotWidth s.a (s.mem.get (Value.ofNat D))
      ∧ t.c = Value.ofNat (T + 1)
      ∧ t.d = Value.ofNat (D + 3)
      ∧ t.mem.get (Value.ofNat T) = Value.ofNat (encrypt wt)
      ∧ t.mem.get (Value.ofNat D) = t.a
      ∧ t.mem.get (Value.ofNat A) = Value.ofNat 74
      ∧ decode (t.mem.get (Value.ofNat (A + 1))) (Value.ofNat (A + 1)).modClass = .jmp
      ∧ (∀ x, x ≠ Value.ofNat D → x ≠ Value.ofNat T → t.mem.get x = s.mem.get x)
      ∧ t.input = s.input ∧ t.output = s.output ∧ t.outClosed = s.outClosed
      ∧ t.rotWidth = s.rotWidth ∧ t.maxWidth = s.maxWidth := by
  let v := op.apply s.rotWidth s.a (s.mem.get (Value.ofNat D))
  let s₁ : State := { s with
    a := v,
    mem := (s.mem.set (Value.ofNat D) v).set (Value.ofNat A) (Value.ofNat 70),
    c := Value.ofNat (A + 1), d := Value.ofNat (D + 1) }
  have h₁ : step1 s = some s₁ := by
    have h := work_step op (code := 74) (by rw [hc, hwork]; exact hdec)
      (by rw [hc, hd]; exact ofNat_ne (by omega))
      (by rw [hc, hwork]; exact printableCode?_ofNat (by omega) (by omega))
    simpa only [hc, hd, succ_ofNat, encrypt_seventyfour] using h
  have hJ₁ : s₁.mem.get (Value.ofNat (A + 1)) = s.mem.get (Value.ofNat (A + 1)) := by
    dsimp [s₁]
    rw [get_set_ne _ (ofNat_ne (by omega)), get_set_ne _ (ofNat_ne (by omega))]
  have hD₁ : s₁.mem.get s₁.d = Value.ofNat A := by
    dsimp [s₁]
    rw [get_set_ne _ (ofNat_ne (by omega)), get_set_ne _ (ofNat_ne (by omega))]
    exact hrestore
  have hA₁ : s₁.mem.get (Value.ofNat A) = Value.ofNat 70 := get_set_self _ _ _
  let s₂ : State := { s₁ with
    mem := s₁.mem.set (Value.ofNat A) (Value.ofNat 74),
    c := Value.ofNat (A + 1), d := Value.ofNat (D + 2) }
  have h₂ : step1 s₁ = some s₂ := by
    have h := step1_jmp (s := s₁) (code := 70)
      (by change decode (s₁.mem.get (Value.ofNat (A + 1))) _ = _; rw [hJ₁]; exact hjump)
      (by rw [hD₁, hA₁]; exact printableCode?_ofNat (by omega) (by omega))
    rw [hD₁] at h
    simpa only [encrypt_seventy, show s₁.d = Value.ofNat (D + 1) from rfl,
      succ_ofNat, show D + 1 + 1 = D + 2 by omega] using h
  have hframe₂ : ∀ x, x ≠ Value.ofNat D → s₂.mem.get x = s.mem.get x := by
    intro x hx
    by_cases ha : x = Value.ofNat A
    · subst x
      rw [show s₂.mem.get (Value.ofNat A) = Value.ofNat 74 from get_set_self _ _ _, hwork]
    · dsimp [s₂, s₁]
      rw [get_set_ne _ (Ne.symm ha), get_set_ne _ (Ne.symm ha), get_set_ne _ hx.symm]
  have hJ₂ : s₂.mem.get (Value.ofNat (A + 1)) = s.mem.get (Value.ofNat (A + 1)) :=
    hframe₂ _ (ofNat_ne (by omega))
  have hD₂ : s₂.mem.get s₂.d = Value.ofNat T := by
    change s₂.mem.get (Value.ofNat (D + 2)) = _
    rw [hframe₂ _ (ofNat_ne (by omega)), hreturn]
  have hT₂ : s₂.mem.get (Value.ofNat T) = s.mem.get (Value.ofNat T) :=
    hframe₂ _ (ofNat_ne (by have := hTD 0 (by omega); omega))
  let s₃ : State := { s₂ with
    mem := s₂.mem.set (Value.ofNat T) (Value.ofNat (encrypt wt)),
    c := Value.ofNat (T + 1), d := Value.ofNat (D + 3) }
  have h₃ : step1 s₂ = some s₃ := by
    have h := step1_jmp (s := s₂) (code := wt)
      (by change decode (s₂.mem.get (Value.ofNat (A + 1))) _ = _; rw [hJ₂]; exact hjump)
      (by rw [hD₂, hT₂]; exact hlanding)
    rw [hD₂] at h
    simpa only [show s₂.d = Value.ofNat (D + 2) from rfl,
      succ_ofNat, show D + 2 + 1 = D + 3 by omega] using h
  have hframe₃ : ∀ x, x ≠ Value.ofNat D → x ≠ Value.ofNat T →
      s₃.mem.get x = s.mem.get x := by
    intro x hxD hxT
    change (s₂.mem.set (Value.ofNat T) _).get x = _
    rw [get_set_ne _ hxT.symm]
    exact hframe₂ x hxD
  refine ⟨s₃, ?_, rfl, rfl, rfl, get_set_self _ _ _, ?_, ?_, ?_, hframe₃, rfl, rfl, rfl, rfl, rfl⟩
  · change (step1 s).bind (fun t => (step1 t).bind (fun u => (step1 u).bind (fun v => some v))) = _
    rw [h₁, Option.bind_some, h₂, Option.bind_some, h₃, Option.bind_some]
  · dsimp [s₃, s₂, s₁]
    rw [get_set_ne _ (ofNat_ne (by have := hTD 0 (by omega); omega)),
      get_set_ne _ (ofNat_ne (by omega)), get_set_ne _ (ofNat_ne (by omega)), get_set_self]
  · rw [hframe₃ _ (ofNat_ne (by omega)) (ofNat_ne hTA.symm), hwork]
  · rw [hframe₃ _ (ofNat_ne (by omega)) (ofNat_ne hTJ.symm)]
    exact hjump

set_option maxHeartbeats 800000 in
/-- An ordinary pointer reset followed by restoration and return. The
width bound prevents an unexpected change of rotation width during a scan.
The destination record holds its restoration and return targets at `D+1`
and `D+2`; execution resumes with the data pointer at `D+3`. -/
theorem movd_call {s : State} {A D T wt : Nat}
    (hc : s.c = Value.ofNat A) (hsource : s.mem.get s.d = Value.ofNat D)
    (hwidth : (Value.ofNat D).width ≤ s.maxWidth)
    (hsep : A + 2 ≤ D)
    (hTA : T ≠ A) (hTJ : T ≠ A + 1)
    (hwork : s.mem.get (Value.ofNat A) = Value.ofNat 74)
    (hdec : decode (Value.ofNat 74) (Value.ofNat A).modClass = .movd)
    (hjump : decode (s.mem.get (Value.ofNat (A + 1)))
      (Value.ofNat (A + 1)).modClass = .jmp)
    (hrestore : s.mem.get (Value.ofNat (D + 1)) = Value.ofNat A)
    (hreturn : s.mem.get (Value.ofNat (D + 2)) = Value.ofNat T)
    (hlanding : printableCode? (s.mem.get (Value.ofNat T)) = some wt) :
    ∃ t, run? 3 s = some t
      ∧ t.a = s.a
      ∧ t.c = Value.ofNat (T + 1)
      ∧ t.d = Value.ofNat (D + 3)
      ∧ t.mem.get (Value.ofNat T) = Value.ofNat (encrypt wt)
      ∧ t.mem.get (Value.ofNat A) = Value.ofNat 74
      ∧ decode (t.mem.get (Value.ofNat (A + 1))) (Value.ofNat (A + 1)).modClass = .jmp
      ∧ (∀ x, x ≠ Value.ofNat T → t.mem.get x = s.mem.get x)
      ∧ t.input = s.input ∧ t.output = s.output ∧ t.outClosed = s.outClosed
      ∧ t.rotWidth = s.rotWidth ∧ t.maxWidth = s.maxWidth := by
  let s₁ : State := { s with
    mem := s.mem.set (Value.ofNat A) (Value.ofNat 70),
    c := Value.ofNat (A + 1), d := Value.ofNat (D + 1) }
  have h₁ : step1 s = some s₁ := by
    have h := step1_movd (s := s) (code := 74)
      (by rw [hc, hwork]; exact hdec)
      (by rw [hc, hwork]; exact printableCode?_ofNat (by omega) (by omega))
    rw [hsource, if_neg (by omega), if_neg (by omega)] at h
    simpa only [hc, succ_ofNat, encrypt_seventyfour] using h
  have hJ₁ : s₁.mem.get (Value.ofNat (A + 1)) = s.mem.get (Value.ofNat (A + 1)) := by
    dsimp [s₁]
    rw [get_set_ne _ (ofNat_ne (by omega))]
  have hD₁ : s₁.mem.get s₁.d = Value.ofNat A := by
    dsimp [s₁]
    rw [get_set_ne _ (ofNat_ne (by omega))]
    exact hrestore
  have hA₁ : s₁.mem.get (Value.ofNat A) = Value.ofNat 70 := get_set_self _ _ _
  let s₂ : State := { s₁ with
    mem := s₁.mem.set (Value.ofNat A) (Value.ofNat 74),
    c := Value.ofNat (A + 1), d := Value.ofNat (D + 2) }
  have h₂ : step1 s₁ = some s₂ := by
    have h := step1_jmp (s := s₁) (code := 70)
      (by change decode (s₁.mem.get (Value.ofNat (A + 1))) _ = _; rw [hJ₁]; exact hjump)
      (by rw [hD₁, hA₁]; exact printableCode?_ofNat (by omega) (by omega))
    rw [hD₁] at h
    simpa only [encrypt_seventy, show s₁.d = Value.ofNat (D + 1) from rfl,
      succ_ofNat, show D + 1 + 1 = D + 2 by omega] using h
  have hframe₂ : ∀ x, s₂.mem.get x = s.mem.get x := by
    intro x
    by_cases ha : x = Value.ofNat A
    · subst x
      rw [show s₂.mem.get (Value.ofNat A) = Value.ofNat 74 from get_set_self _ _ _, hwork]
    · dsimp [s₂, s₁]
      rw [get_set_ne _ (Ne.symm ha), get_set_ne _ (Ne.symm ha)]
  have hJ₂ : s₂.mem.get (Value.ofNat (A + 1)) = s.mem.get (Value.ofNat (A + 1)) :=
    hframe₂ _
  have hD₂ : s₂.mem.get s₂.d = Value.ofNat T := by
    change s₂.mem.get (Value.ofNat (D + 2)) = _
    rw [hframe₂ _, hreturn]
  have hT₂ : s₂.mem.get (Value.ofNat T) = s.mem.get (Value.ofNat T) :=
    hframe₂ _
  let s₃ : State := { s₂ with
    mem := s₂.mem.set (Value.ofNat T) (Value.ofNat (encrypt wt)),
    c := Value.ofNat (T + 1), d := Value.ofNat (D + 3) }
  have h₃ : step1 s₂ = some s₃ := by
    have h := step1_jmp (s := s₂) (code := wt)
      (by change decode (s₂.mem.get (Value.ofNat (A + 1))) _ = _; rw [hJ₂]; exact hjump)
      (by rw [hD₂, hT₂]; exact hlanding)
    rw [hD₂] at h
    simpa only [show s₂.d = Value.ofNat (D + 2) from rfl,
      succ_ofNat, show D + 2 + 1 = D + 3 by omega] using h
  have hframe₃ : ∀ x, x ≠ Value.ofNat T →
      s₃.mem.get x = s.mem.get x := by
    intro x hxT
    change (s₂.mem.set (Value.ofNat T) _).get x = _
    rw [get_set_ne _ hxT.symm]
    exact hframe₂ x
  refine ⟨s₃, ?_, rfl, rfl, rfl, get_set_self _ _ _, ?_, ?_, hframe₃, rfl, rfl, rfl, rfl, rfl⟩
  · change (step1 s).bind (fun t => (step1 t).bind (fun u => (step1 u).bind (fun v => some v))) = _
    rw [h₁, Option.bind_some, h₂, Option.bind_some, h₃, Option.bind_some]
  · rw [hframe₃ _ (ofNat_ne hTA.symm), hwork]
  · rw [hframe₃ _ (ofNat_ne hTJ.symm)]
    exact hjump

end Langlib.Computability.Unshackled.Runtime
