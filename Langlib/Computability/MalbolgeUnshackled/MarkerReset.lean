import Langlib.Computability.MalbolgeUnshackled.Marker

/-!
# A reusable marker reset

Six working calls, four pointer resets, and two visits to a two-phase
router regenerate one in cell 3200. The router changes from move to no-op
and back; no return record is rewritten. All resident constants survive.
-/

namespace Langlib.Computability.Unshackled.Runtime.MarkerReset

open Langlib.Common Langlib.MalbolgeUnshackled
open Marker

def landings : List Nat := [247, 269, 529, 1299]

def cells : List (Nat × Value) :=
  ([(153,74), (154,38), (248,74), (249,37), (270,74), (271,109), (531,37),
    (3001,153), (3002,247), (3003,3197), (3198,248), (3199,269),
    (3201,270), (3202,529), (3203,3398), (3204,1299),
    (3399,269), (3401,270), (3402,247), (3403,3497),
    (3498,248), (3499,269), (3501,270), (3502,247), (3503,3597),
    (3598,248), (3599,269), (3601,270), (3602,247), (3603,3197)] : List (Nat × Nat)).map
    (fun (a,v) => (a, Value.ofNat v)) ++
    [(3000, ones), (3400, ones), (3500, Value.ofNat 2), (3600, mask)]

def Protected (x : Value) : Prop :=
  x ≠ Value.ofNat 3200 ∧ x ≠ Value.ofNat 530 ∧
    ∀ a ∈ landings, x ≠ Value.ofNat a

private theorem protected_cells : ∀ e ∈ cells, Protected (Value.ofNat e.1) := by
  unfold cells Protected landings
  decide

private theorem landing_bounds {a : Nat} (h : a ∈ landings) :
    a < 3000 ∧ a ≠ 530 ∧ a ≠ 153 ∧ a ≠ 154 ∧ a ≠ 248 ∧ a ≠ 249 ∧ a ≠ 270 ∧ a ≠ 271 := by
  simp [landings] at h
  omega

structure Resident (m : Memory) : Prop where
  static : ∀ a v, (a,v) ∈ cells → m.get (Value.ofNat a) = v
  landing : ∀ a ∈ landings, ∃ k, printableCode? (m.get (Value.ofNat a)) = some k

private theorem Resident.frame {m m' : Memory} (h : Resident m)
    (hf : ∀ x, Protected x → m'.get x = m.get x)
    (hl : ∀ a ∈ landings, ∃ k, printableCode? (m'.get (Value.ofNat a)) = some k) :
    Resident m' := by
  refine ⟨?_, hl⟩
  intro a v ha
  rw [hf _ (protected_cells (a,v) ha)]
  exact h.static a v ha

/-- A state at a named point in the reset, with explicit marker and router
phase. `false` is the initial move phase; `true` is the no-op phase. -/
structure At (w : Nat) (a v : Value) (phase : Bool) (c d : Nat) (s : State) : Prop where
  resident : Resident s.mem
  code : s.c = Value.ofNat c
  data : s.d = Value.ofNat d
  acc : s.a = a
  width : s.rotWidth = w
  bound : 8 ≤ s.maxWidth
  marker : s.mem.get (Value.ofNat 3200) = v
  router : s.mem.get (Value.ofNat 530) = Value.ofNat (if phase then 70 else 74)

/-- The execution and frame information common to every segment. -/
structure Segment (n : Nat) (s t : State) : Prop where
  run : run? n s = some t
  frame : ∀ x, Protected x → t.mem.get x = s.mem.get x
  maxWidth : t.maxWidth = s.maxWidth
  input : t.input = s.input
  output : t.output = s.output
  outClosed : t.outClosed = s.outClosed

private theorem Segment.trans {m n : Nat} {s u t : State}
    (h : Segment m s u) (h' : Segment n u t) : Segment (m + n) s t := by
  refine ⟨?_, fun x hx => (h'.frame x hx).trans (h.frame x hx),
    h'.maxWidth.trans h.maxWidth, h'.input.trans h.input,
    h'.output.trans h.output, h'.outClosed.trans h.outClosed⟩
  rw [run?_add, h.run, Option.bind_some, h'.run]

private theorem encrypted_printable {v : Value} {k : Nat}
    (h : printableCode? v = some k) :
    printableCode? (Value.ofNat (encrypt k)) = some (encrypt k) := by
  have hb := printableCode?_bounds h
  have he := encrypt_range hb.1 hb.2
  exact printableCode?_ofNat he.1 he.2

set_option maxHeartbeats 1000000 in
private theorem work {s : State} {w A D T : Nat} {a v q : Value} {phase : Bool}
    (h : At w a v phase A D s) (op : WorkOp)
    (hA : (A = 153 ∧ op = .rotate) ∨ (A = 270 ∧ op = .crazy))
    (hD : 3000 ≤ D) (hT : T ∈ landings)
    (hr : (D + 1, Value.ofNat A) ∈ cells) (ht : (D + 2, Value.ofNat T) ∈ cells)
    (hq : s.mem.get (Value.ofNat D) = q)
    (hkeep : D = 3200 ∨ op.apply w a q = q) :
    ∃ t, Segment 3 s t ∧
      At w (op.apply w a q) (if D = 3200 then op.apply w a q else v)
        phase (T + 1) (D + 3) t := by
  have hTb := landing_bounds hT
  have hAb : A = 153 ∨ A = 270 := hA.imp And.left And.left
  obtain ⟨k, hk⟩ := h.resident.landing T hT
  obtain ⟨t, hrun, ha, hc, hd, hland, hoperand, _, _, hf, hi, ho, hx, hw, hm⟩ :=
    work_call op h.code h.data (by omega) (by omega) (by omega)
      (fun i hi => by omega)
      (by rcases hAb with rfl | rfl <;> exact h.resident.static _ _ (by decide))
      (by rcases hA with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide)
      (by rcases hAb with rfl | rfl
          · rw [h.resident.static 154 (Value.ofNat 38) (by decide)]; decide
          · rw [h.resident.static 271 (Value.ofNat 109) (by decide)]; decide)
      (h.resident.static _ _ hr) (h.resident.static _ _ ht) hk
  have ha' : t.a = op.apply w a q := by rw [ha, h.width, h.acc, hq]
  have hf' : ∀ x, Protected x → t.mem.get x = s.mem.get x := by
    intro x hp
    by_cases hxD : x = Value.ofNat D
    · subst x
      rcases hkeep with hD' | hv
      · subst D; exact absurd rfl hp.1
      · rw [hoperand, ha', hv, hq]
    · exact hf x hxD (hp.2.2 T hT)
  have hl' : ∀ b ∈ landings, ∃ k, printableCode? (t.mem.get (Value.ofNat b)) = some k := by
    intro b hb
    by_cases hbT : b = T
    · subst b; refine ⟨encrypt k, ?_⟩; rw [hland]; exact encrypted_printable hk
    · rw [hf _ (ofNat_ne (by have := (landing_bounds hb).1; omega)) (ofNat_ne hbT)]
      exact h.resident.landing b hb
  refine ⟨t, ⟨hrun, hf', hm, hi, ho, hx⟩,
    h.resident.frame hf' hl', hc, hd, ha', hw.trans h.width, ?_, ?_, ?_⟩
  · rw [hm]; exact h.bound
  · by_cases hDm : D = 3200
    · subst D; simpa using hoperand.trans ha'
    · rw [if_neg hDm, hf _ (ofNat_ne (Ne.symm hDm)) (ofNat_ne (by omega)), h.marker]
  · rw [hf _ (ofNat_ne (by omega)) (ofNat_ne (Ne.symm hTb.2.1)), h.router]

set_option maxHeartbeats 1000000 in
private theorem reset {s : State} {w D P : Nat} {a v : Value} {phase : Bool}
    (h : At w a v phase 248 P s)
    (hD : 3000 ≤ D ∧ D ≤ 3600)
    (hptr : (P, Value.ofNat (D - 3)) ∈ cells)
    (hr : (D - 2, Value.ofNat 248) ∈ cells)
    (ht : (D - 1, Value.ofNat 269) ∈ cells) :
    ∃ t, Segment 3 s t ∧ At w a v phase 270 D t := by
  obtain ⟨k, hk⟩ := h.resident.landing 269 (by decide)
  have hwide : (Value.ofNat (D - 3)).width ≤ 8 := by
    apply width_ofNat_le
    have : 3 ^ 8 = 6561 := by decide
    omega
  obtain ⟨t, hrun, ha, hc, hd, hland, _, _, hf, hi, ho, hx, hw, hm⟩ :=
    movd_call h.code (by rw [h.data]; exact h.resident.static _ _ hptr)
      (Nat.le_trans hwide h.bound) (by omega) (by omega) (by omega)
      (h.resident.static 248 _ (by decide)) (by decide)
      (by rw [h.resident.static 249 (Value.ofNat 37) (by decide)]; decide)
      (by simpa only [show D - 3 + 1 = D - 2 by omega] using h.resident.static _ _ hr)
      (by simpa only [show D - 3 + 2 = D - 1 by omega] using h.resident.static _ _ ht) hk
  have hf' : ∀ x, Protected x → t.mem.get x = s.mem.get x :=
    fun x hp => hf x (hp.2.2 269 (by decide))
  have hl' : ∀ b ∈ landings, ∃ k, printableCode? (t.mem.get (Value.ofNat b)) = some k := by
    intro b hb
    by_cases h269 : b = 269
    · subst b; refine ⟨encrypt k, ?_⟩; rw [hland]; exact encrypted_printable hk
    · rw [hf _ (ofNat_ne h269)]; exact h.resident.landing b hb
  refine ⟨t, ⟨hrun, hf', hm, hi, ho, hx⟩,
    h.resident.frame hf' hl', hc, ?_, ha.trans h.acc, hw.trans h.width, ?_, ?_, ?_⟩
  · simpa only [show D - 3 + 3 = D by omega] using hd
  · rw [hm]; exact h.bound
  · rw [hf _ (by decide), h.marker]
  · rw [hf _ (by decide), h.router]

set_option maxHeartbeats 1000000 in
/-- One visit to the move/no-op router. Two visits restore its original
phase while selecting different code and data continuations. -/
private theorem route {s : State} {w : Nat} {a v : Value} {phase : Bool}
    (h : At w a v phase 530 3203 s) :
    ∃ t, Segment 2 s t ∧
      At w a v (!phase) (if phase then 1300 else 270) (if phase then 3205 else 3400) t := by
  let T := if phase then 1299 else 269
  have hT : T ∈ landings := by cases phase <;> decide
  have hTb := landing_bounds hT
  obtain ⟨k, hk⟩ := h.resident.landing T hT
  let s₁ : State := { s with
    mem := s.mem.set (Value.ofNat 530) (Value.ofNat (if phase then 74 else 70)),
    c := Value.ofNat 531, d := Value.ofNat (if phase then 3204 else 3399) }
  have hr₁ : step1 s = some s₁ := by
    cases phase with
    | false =>
      have hp : s.mem.get s.d = Value.ofNat 3398 := by
        rw [h.data]; exact h.resident.static _ _ (by decide)
      have hh := step1_movd (s := s) (code := 74)
        (by rw [h.code, h.router]; decide)
        (by rw [h.code, h.router]; decide)
      have hb : (Value.ofNat 3398).width ≤ s.maxWidth := h.bound
      rw [hp, if_neg (by omega), if_neg (by omega), h.code] at hh
      exact hh
    | true =>
      have hh := step1_nop (s := s) (code := 70)
        (by rw [h.code, h.router]; decide)
        (by rw [h.code, h.router]; decide)
      rw [h.code, h.data] at hh
      exact hh
  have hf₁ (x : Value) (hx : x ≠ Value.ofNat 530) : s₁.mem.get x = s.mem.get x :=
    get_set_ne _ hx.symm _
  have hj : decode (s₁.mem.get s₁.c) s₁.c.modClass = .jmp := by
    change decode (s₁.mem.get (Value.ofNat 531)) _ = _
    rw [hf₁ _ (by decide), h.resident.static 531 (Value.ofNat 37) (by decide)]
    change decode (Value.ofNat 37) (Value.ofNat 531).modClass = .jmp
    decide
  have hp : s₁.mem.get s₁.d = Value.ofNat T := by
    cases phase with
    | false =>
      change s₁.mem.get (Value.ofNat 3399) = Value.ofNat 269
      rw [hf₁ _ (by decide)]
      exact h.resident.static _ _ (by decide)
    | true =>
      change s₁.mem.get (Value.ofNat 3204) = Value.ofNat 1299
      rw [hf₁ _ (by decide)]
      exact h.resident.static _ _ (by decide)
  let t : State := { s₁ with
    mem := s₁.mem.set (Value.ofNat T) (Value.ofNat (encrypt k)),
    c := Value.ofNat (T + 1), d := Value.ofNat (if phase then 3205 else 3400) }
  have hrt : step1 s₁ = some t := by
    have hh := step1_jmp hj (code := k)
      (by rw [hp, hf₁ _ (ofNat_ne hTb.2.1)]; exact hk)
    rw [hp] at hh
    cases phase <;> simpa [t, s₁, T, succ_ofNat] using hh
  have hft (x : Value) (hx : x ≠ Value.ofNat T) : t.mem.get x = s₁.mem.get x :=
    get_set_ne _ hx.symm _
  have hf : ∀ x, Protected x → t.mem.get x = s.mem.get x := by
    intro x hx
    rw [hft x (hx.2.2 T hT), hf₁ x hx.2.1]
  have hl : ∀ b ∈ landings, ∃ k, printableCode? (t.mem.get (Value.ofNat b)) = some k := by
    intro b hb
    by_cases hbT : b = T
    · subst b
      refine ⟨encrypt k, ?_⟩
      rw [get_set_self]
      exact encrypted_printable hk
    · rw [hft _ (ofNat_ne hbT), hf₁ _ (ofNat_ne (landing_bounds hb).2.1)]
      exact h.resident.landing b hb
  refine ⟨t, ⟨?_, hf, rfl, rfl, rfl, rfl⟩,
    h.resident.frame hf hl, ?_, rfl, h.acc, h.width, h.bound, ?_, ?_⟩
  · change (step1 s).bind (fun u => (step1 u).bind some) = _
    rw [hr₁, Option.bind_some, hrt, Option.bind_some]
  · cases phase <;> rfl
  · rw [hft _ (ofNat_ne (by omega)), hf₁ _ (by decide), h.marker]
  · rw [hft _ (ofNat_ne (Ne.symm hTb.2.1)), get_set_self]
    cases phase <;> rfl

set_option maxHeartbeats 1500000 in
/-- Thirty-four actual steps regenerate one and restore the resident
constants and router phase. The entry marker can be arbitrarily wide;
only its trit alphabet is constrained. The incoming accumulator is arbitrary. -/
theorem call {s : State} {w : Nat} {a v : Value}
    (h : At w a v false 153 3000 s) (hv : ZeroOne v) :
    ∃ t, Segment 34 s t ∧ At w (Value.ofNat 1) (Value.ofNat 1) false 1300 3205 t := by
  obtain ⟨s₃, hs₃, h₃⟩ := work (T := 247) h .rotate (by simp) (by omega) (by decide)
    (by decide) (by decide) (h.resident.static 3000 ones (by decide))
    (Or.inr (rotate_ones w))
  have h₃' : At w ones v false 248 3003 s₃ := by
    simpa only [WorkOp.apply, rotate_ones, if_neg (by decide : ¬ (3000 = 3200))] using h₃
  obtain ⟨s₆, hs₆, h₆⟩ := reset h₃' (D := 3200) (by omega) (by decide) (by decide) (by decide)
  obtain ⟨s₉, hs₉, h₉⟩ := work (T := 529) h₆ .crazy (by simp) (by omega) (by decide)
    (by decide) (by decide) h₆.marker (Or.inl rfl)
  have h₉' : At w Value.zero Value.zero false 530 3203 s₉ := by
    simpa only [WorkOp.apply, if_pos rfl, ite_true, clear hv] using h₉
  obtain ⟨s₁₁, hs₁₁, h₁₁⟩ := route h₉'
  change At w Value.zero Value.zero true 270 3400 s₁₁ at h₁₁
  obtain ⟨s₁₄, hs₁₄, h₁₄⟩ := work (T := 247) h₁₁ .crazy (by simp) (by omega) (by decide)
    (by decide) (by decide) (h₁₁.resident.static 3400 ones (by decide))
    (Or.inr constants.1)
  have h₁₄' : At w ones Value.zero true 248 3403 s₁₄ := by
    simpa only [WorkOp.apply, constants.1, if_neg (by decide : ¬ (3400 = 3200))] using h₁₄
  obtain ⟨s₁₇, hs₁₇, h₁₇⟩ := reset h₁₄' (D := 3500) (by omega) (by decide) (by decide) (by decide)
  obtain ⟨s₂₀, hs₂₀, h₂₀⟩ := work (T := 247) h₁₇ .crazy (by simp) (by omega) (by decide)
    (by decide) (by decide) (h₁₇.resident.static 3500 (Value.ofNat 2) (by decide))
    (Or.inr constants.2.1)
  have h₂₀' : At w (Value.ofNat 2) Value.zero true 248 3503 s₂₀ := by
    simpa only [WorkOp.apply, constants.2.1, if_neg (by decide : ¬ (3500 = 3200))] using h₂₀
  obtain ⟨s₂₃, hs₂₃, h₂₃⟩ := reset h₂₀' (D := 3600) (by omega) (by decide) (by decide) (by decide)
  obtain ⟨s₂₆, hs₂₆, h₂₆⟩ := work (T := 247) h₂₃ .crazy (by simp) (by omega) (by decide)
    (by decide) (by decide) (h₂₃.resident.static 3600 mask (by decide))
    (Or.inr constants.2.2.1)
  have h₂₆' : At w mask Value.zero true 248 3603 s₂₆ := by
    simpa only [WorkOp.apply, constants.2.2.1, if_neg (by decide : ¬ (3600 = 3200))] using h₂₆
  obtain ⟨s₂₉, hs₂₉, h₂₉⟩ := reset h₂₆' (D := 3200) (by omega) (by decide) (by decide) (by decide)
  obtain ⟨s₃₂, hs₃₂, h₃₂⟩ := work (T := 529) h₂₉ .crazy (by simp) (by omega) (by decide)
    (by decide) (by decide) h₂₉.marker (Or.inl rfl)
  have h₃₂' : At w (Value.ofNat 1) (Value.ofNat 1) true 530 3203 s₃₂ := by
    simpa only [WorkOp.apply, constants.2.2.2, if_pos rfl, ite_true] using h₃₂
  obtain ⟨t, ht, hat⟩ := route h₃₂'
  refine ⟨t, ?_, hat⟩
  exact hs₃.trans (hs₆.trans (hs₉.trans (hs₁₁.trans (hs₁₄.trans (hs₁₇.trans
    (hs₂₀.trans (hs₂₃.trans (hs₂₆.trans (hs₂₉.trans (hs₃₂.trans ht))))))))))

/-- In particular, the reset accepts a marker rotated to any position,
independently of the working width at which the reset is called. -/
theorem call_power {s : State} {w k : Nat} {a : Value}
    (h : At w a (Value.ofNat (3 ^ k)) false 153 3000 s) :
    ∃ t, Segment 34 s t ∧ At w (Value.ofNat 1) (Value.ofNat 1) false 1300 3205 t :=
  call h (zeroOne_power k)

end Langlib.Computability.Unshackled.Runtime.MarkerReset
