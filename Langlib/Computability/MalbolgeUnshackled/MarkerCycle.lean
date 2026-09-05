import Langlib.Computability.MalbolgeUnshackled.MarkerReset

/-!
# Repeating rotation and reset on the same marker

A nine-step rotation route uses the reset's landing at 529 as its working
instruction. A seven-step return route closes the cycle. The same physical
marker, constants and return records support every iteration.
-/

namespace Langlib.Computability.Unshackled.Runtime.MarkerCycle

open Langlib.Common Langlib.MalbolgeUnshackled
open Marker

private theorem get_set_nat (m : Memory) (a b : Nat) (v : Value) :
    (m.set (Value.ofNat a) v).get (Value.ofNat b) =
      if a = b then v else m.get (Value.ofNat b) := by
  by_cases h : a = b
  · subst b; simp [get_set_self]
  · rw [if_neg h, get_set_ne _ (ofNat_ne h)]

private theorem jump {s : State} {C D T k : Nat}
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

private theorem move {s : State} {C D T k : Nat}
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

private theorem noop {s : State} {C D k : Nat}
    (hc : s.c = Value.ofNat C) (hd : s.d = Value.ofNat D)
    (hj : decode (s.mem.get (Value.ofNat C)) (Value.ofNat C).modClass = .nop)
    (hk : printableCode? (s.mem.get (Value.ofNat C)) = some k) :
    step1 s = some { s with
      mem := s.mem.set (Value.ofNat C) (Value.ofNat (encrypt k)),
      c := Value.ofNat (C + 1), d := Value.ofNat (D + 1) } := by
  have hh := step1_nop (s := s) (by rw [hc]; exact hj) (by rw [hc]; exact hk)
  simpa only [hc, hd, succ_ofNat] using hh

def cells : List (Nat × Nat) :=
  [(110,82), (272,247), (273,2995), (2996,248), (2997,529), (2999,152),
   (1300,114), (3205,247), (3206,3194), (3195,248), (3196,525)]

def landings : List Nat := [109, 152, 525]

def noops : List Nat := [526, 527, 528]

/-- Additional static routing records and the three initialized no-ops. -/
structure Links (m : Memory) : Prop where
  static : ∀ a v, (a,v) ∈ cells → m.get (Value.ofNat a) = Value.ofNat v
  landing : ∀ a ∈ landings, ∃ k, printableCode? (m.get (Value.ofNat a)) = some k
  nops : ∀ a ∈ noops, ∃ k, (k = 74 ∨ k = 70) ∧ m.get (Value.ofNat a) = Value.ofNat k

/-- Possible changes over one complete cycle. The rotor and router are
restored exactly and so are absent from this list. -/
def changed : List Nat := [3200, 109, 152, 247, 269, 525, 526, 527, 528, 1299]

structure Segment (n : Nat) (s t : State) : Prop where
  run : run? n s = some t
  frame : ∀ x, (∀ a ∈ changed, x ≠ Value.ofNat a) → t.mem.get x = s.mem.get x
  width : t.rotWidth = s.rotWidth
  maxWidth : t.maxWidth = s.maxWidth
  input : t.input = s.input
  output : t.output = s.output
  outClosed : t.outClosed = s.outClosed

private theorem Segment.trans {m n : Nat} {s u t : State}
    (h : Segment m s u) (h' : Segment n u t) : Segment (m + n) s t := by
  refine ⟨?_, fun x hx => (h'.frame x hx).trans (h.frame x hx),
    h'.width.trans h.width, h'.maxWidth.trans h.maxWidth, h'.input.trans h.input,
    h'.output.trans h.output, h'.outClosed.trans h.outClosed⟩
  rw [run?_add, h.run, Option.bind_some, h'.run]

private theorem printable_after {v : Value} {k : Nat}
    (h : printableCode? v = some k) :
    ∃ j, printableCode? (Value.ofNat (encrypt k)) = some j := by
  have hb := printableCode?_bounds h
  have he := encrypt_range hb.1 hb.2
  exact ⟨encrypt k, printableCode?_ofNat he.1 he.2⟩

set_option maxHeartbeats 2000000 in
/-- Rotate the shared marker and enter reset, restoring both working words.
The adjacent record remains the reset's crazy-operation record throughout. -/
theorem rotate {s : State} {w : Nat} {a v : Value}
    (h : MarkerReset.At w a v false 529 3200 s)
    (hl : Links s.mem) (hr : s.mem.get (Value.ofNat 529) = Value.ofNat 74) :
    ∃ t, Segment 9 s t ∧
      MarkerReset.At w (Value.rot w v) (Value.rot w v) false 153 3000 t ∧
      Links t.mem ∧ t.mem.get (Value.ofNat 529) = Value.ofNat 74 := by
  obtain ⟨k109, hk109⟩ := hl.landing 109 (by decide)
  obtain ⟨k152, hk152⟩ := hl.landing 152 (by decide)
  obtain ⟨k247, hk247⟩ := h.resident.landing 247 (by decide)
  have h3201 := h.resident.static 3201 (Value.ofNat 270) (by decide)
  have h271 := h.resident.static 271 (Value.ofNat 109) (by decide)
  have h531 := h.resident.static 531 (Value.ofNat 37) (by decide)
  have h248 := h.resident.static 248 (Value.ofNat 74) (by decide)
  have h249 := h.resident.static 249 (Value.ofNat 37) (by decide)
  have h110 := hl.static 110 82 (by decide)
  have h272 := hl.static 272 247 (by decide)
  have h273 := hl.static 273 2995 (by decide)
  have h2996 := hl.static 2996 248 (by decide)
  have h2997 := hl.static 2997 529 (by decide)
  have h2999 := hl.static 2999 152 (by decide)
  have h530 : s.mem.get (Value.ofNat 530) = Value.ofNat 74 := h.router
  let s1 : State := { s with
    mem := ((s.mem.set (Value.ofNat 3200) (Value.rot w v)).set (Value.ofNat 529) (Value.ofNat 70)),
    c := Value.ofNat 530, d := Value.ofNat 3201, a := Value.rot w v }
  have hs1 : step1 s = some s1 := by
    have hh := work_step .rotate (s := s) (code := 74)
      (by rw [h.code, hr]; decide)
      (by rw [h.code, h.data]; decide)
      (by rw [h.code, hr]; decide)
    simpa only [s1, h.code, h.data, h.width, h.marker, WorkOp.apply, encrypt_seventyfour, succ_ofNat] using hh
  let s2 : State := { s1 with
    mem := (s1.mem.set (Value.ofNat 530) (Value.ofNat 70)),
    c := Value.ofNat 531, d := Value.ofNat 271 }
  have hs2 : step1 s1 = some s2 := by
    have hh := move (s := s1) (C := 530) (D := 3201) (T := 270) (k := 74) rfl rfl
      (by simp [s1, get_set_nat, h530]; decide)
      (by simp [s1, get_set_nat, h3201])
      (by simp [s1, get_set_nat, h530]; decide)
      (show (Value.ofNat 270).width ≤ s.maxWidth from by have := h.bound; change 6 ≤ s.maxWidth; omega)
    exact hh
  let s3 : State := { s2 with
    mem := (s2.mem.set (Value.ofNat 109) (Value.ofNat (encrypt k109))),
    c := Value.ofNat 110, d := Value.ofNat 272 }
  have hs3 : step1 s2 = some s3 := by
    have hh := jump (s := s2) (C := 531) (D := 271) (T := 109) (k := k109) rfl rfl
      (by simp [s1, s2, get_set_nat, h531]; decide)
      (by simp [s1, s2, get_set_nat, h271])
      (by simp [s1, s2, get_set_nat, hk109])
    exact hh
  let s4 : State := { s3 with
    mem := (s3.mem.set (Value.ofNat 247) (Value.ofNat (encrypt k247))),
    c := Value.ofNat 248, d := Value.ofNat 273 }
  have hs4 : step1 s3 = some s4 := by
    have hh := jump (s := s3) (C := 110) (D := 272) (T := 247) (k := k247) rfl rfl
      (by simp [s1, s2, s3, get_set_nat, h110]; decide)
      (by simp [s1, s2, s3, get_set_nat, h272])
      (by simp [s1, s2, s3, get_set_nat, hk247])
    exact hh
  let s5 : State := { s4 with
    mem := (s4.mem.set (Value.ofNat 248) (Value.ofNat 70)),
    c := Value.ofNat 249, d := Value.ofNat 2996 }
  have hs5 : step1 s4 = some s5 := by
    have hh := move (s := s4) (C := 248) (D := 273) (T := 2995) (k := 74) rfl rfl
      (by simp [s1, s2, s3, s4, get_set_nat, h248]; decide)
      (by simp [s1, s2, s3, s4, get_set_nat, h273])
      (by simp [s1, s2, s3, s4, get_set_nat, h248]; decide)
      (show (Value.ofNat 2995).width ≤ s.maxWidth from by have := h.bound; change 8 ≤ s.maxWidth; omega)
    exact hh
  let s6 : State := { s5 with
    mem := (s5.mem.set (Value.ofNat 248) (Value.ofNat 74)),
    c := Value.ofNat 249, d := Value.ofNat 2997 }
  have hs6 : step1 s5 = some s6 := by
    have hh := jump (s := s5) (C := 249) (D := 2996) (T := 248) (k := 70) rfl rfl
      (by simp [s1, s2, s3, s4, s5, get_set_nat, h249]; decide)
      (by simp [s1, s2, s3, s4, s5, get_set_nat, h2996])
      (by simp [s1, s2, s3, s4, s5, get_set_nat]; decide)
    exact hh
  let s7 : State := { s6 with
    mem := (s6.mem.set (Value.ofNat 529) (Value.ofNat 74)),
    c := Value.ofNat 530, d := Value.ofNat 2998 }
  have hs7 : step1 s6 = some s7 := by
    have hh := jump (s := s6) (C := 249) (D := 2997) (T := 529) (k := 70) rfl rfl
      (by simp [s1, s2, s3, s4, s5, s6, get_set_nat, h249]; decide)
      (by simp [s1, s2, s3, s4, s5, s6, get_set_nat, h2997])
      (by simp [s1, s2, s3, s4, s5, s6, get_set_nat]; decide)
    exact hh
  let s8 : State := { s7 with
    mem := (s7.mem.set (Value.ofNat 530) (Value.ofNat 74)),
    c := Value.ofNat 531, d := Value.ofNat 2999 }
  have hs8 : step1 s7 = some s8 := by
    have hh := noop (s := s7) (C := 530) (D := 2998) (k := 70) rfl rfl
      (by simp [s1, s2, s3, s4, s5, s6, s7, get_set_nat]; decide)
      (by simp [s1, s2, s3, s4, s5, s6, s7, get_set_nat]; decide)
    exact hh
  let s9 : State := { s8 with
    mem := (s8.mem.set (Value.ofNat 152) (Value.ofNat (encrypt k152))),
    c := Value.ofNat 153, d := Value.ofNat 3000 }
  have hs9 : step1 s8 = some s9 := by
    have hh := jump (s := s8) (C := 531) (D := 2999) (T := 152) (k := k152) rfl rfl
      (by simp [s1, s2, s3, s4, s5, s6, s7, s8, get_set_nat, h531]; decide)
      (by simp [s1, s2, s3, s4, s5, s6, s7, s8, get_set_nat, h2999])
      (by simp [s1, s2, s3, s4, s5, s6, s7, s8, get_set_nat, hk152])
    exact hh
  have hf : ∀ x, (∀ b ∈ ([3200,109,152,247] : List Nat), x ≠ Value.ofNat b) →
      s9.mem.get x = s.mem.get x := by
    intro x hx
    have h3200 := hx 3200 (by simp)
    have h109 := hx 109 (by simp)
    have h152 := hx 152 (by simp)
    have h247 := hx 247 (by simp)
    by_cases h529 : x = Value.ofNat 529
    · subst x
      simp [s9,s8,s7,s6,s5,s4,s3,s2,s1,get_set_nat,hr]
    by_cases h530' : x = Value.ofNat 530
    · subst x
      simp [s9,s8,s7,s6,s5,s4,s3,s2,s1,get_set_nat,h530]
    by_cases h248' : x = Value.ofNat 248
    · subst x
      simp [s9,s8,s7,s6,s5,s4,s3,s2,s1,get_set_nat,h248]
    simp [s9,s8,s7,s6,s5,s4,s3,s2,s1,get_set_ne,Ne.symm h3200,Ne.symm h109,
      Ne.symm h152,Ne.symm h247,Ne.symm h529,Ne.symm h530',Ne.symm h248']
  have hres : MarkerReset.Resident s9.mem := by
    constructor
    · intro b v hb
      have hdis : ∀ e ∈ MarkerReset.cells, ∀ z ∈ ([3200,109,152,247] : List Nat), e.1 ≠ z := by
        unfold MarkerReset.cells; decide
      rw [hf _ (fun z hz => ofNat_ne (hdis (b,v) hb z hz))]
      exact h.resident.static b v hb
    · intro b hb
      by_cases he : b = 247
      · subst b
        have heq : s9.mem.get (Value.ofNat 247) = Value.ofNat (encrypt k247) := by
          simp [s9,s8,s7,s6,s5,s4,s3,s2,s1,get_set_nat]
        rw [heq]; exact printable_after hk247
      · have hd : ∀ z ∈ ([3200,109,152,247] : List Nat), b ≠ z := by
          intro z hz
          simp at hz
          simp [MarkerReset.landings] at hb
          omega
        rw [hf _ (fun z hz => ofNat_ne (hd z hz))]
        exact h.resident.landing b hb
  have hlinks : Links s9.mem := by
    constructor
    · intro b v hb
      have hdis : ∀ e ∈ cells, ∀ z ∈ ([3200,109,152,247] : List Nat), e.1 ≠ z := by
        unfold cells; decide
      rw [hf _ (fun z hz => ofNat_ne (hdis (b,v) hb z hz))]
      exact hl.static b v hb
    · intro b hb
      simp [landings] at hb
      rcases hb with rfl | rfl | rfl
      · have heq : s9.mem.get (Value.ofNat 109) = Value.ofNat (encrypt k109) := by
          simp [s9,s8,s7,s6,s5,s4,s3,s2,s1,get_set_nat]
        rw [heq]; exact printable_after hk109
      · have heq : s9.mem.get (Value.ofNat 152) = Value.ofNat (encrypt k152) := by
          simp [s9,s8,s7,s6,s5,s4,s3,s2,s1,get_set_nat]
        rw [heq]; exact printable_after hk152
      · rw [hf _ (by intro z hz; simp at hz; exact ofNat_ne (by omega))]
        exact hl.landing 525 (by decide)
    · intro b hb
      obtain ⟨k,hk,hv⟩ := hl.nops b hb
      refine ⟨k,hk,?_⟩
      rw [hf _ (by intro z hz; simp at hz; simp [noops] at hb; exact ofNat_ne (by omega)),hv]
  refine ⟨s9, ⟨?_, ?_, rfl,rfl,rfl,rfl,rfl⟩,
    ⟨hres,rfl,rfl,rfl,h.width,h.bound,?_,?_⟩, hlinks, ?_⟩
  · change (step1 s).bind (fun t => run? 8 t) = _
    rw [hs1,Option.bind_some]
    change (step1 s1).bind (fun t => run? 7 t) = _
    rw [hs2,Option.bind_some]
    change (step1 s2).bind (fun t => run? 6 t) = _
    rw [hs3,Option.bind_some]
    change (step1 s3).bind (fun t => run? 5 t) = _
    rw [hs4,Option.bind_some]
    change (step1 s4).bind (fun t => run? 4 t) = _
    rw [hs5,Option.bind_some]
    change (step1 s5).bind (fun t => run? 3 t) = _
    rw [hs6,Option.bind_some]
    change (step1 s6).bind (fun t => run? 2 t) = _
    rw [hs7,Option.bind_some]
    change (step1 s7).bind (fun t => run? 1 t) = _
    rw [hs8,Option.bind_some]
    change (step1 s8).bind some = _
    rw [hs9,Option.bind_some]
  · intro x hx
    have hsub : ∀ z ∈ ([3200,109,152,247] : List Nat), z ∈ changed := by decide
    exact hf x (fun z hz => hx z (hsub z hz))
  · simp [s9,s8,s7,s6,s5,s4,s3,s2,s1,get_set_nat]
  · simp [s9,s8,s7,s6,s5,s4,s3,s2,s1,get_set_nat]
  · simp [s9,s8,s7,s6,s5,s4,s3,s2,s1,get_set_nat]

theorem nop_phase {b k : Nat} (hb : b ∈ noops) (hk : k = 74 ∨ k = 70) :
    decode (Value.ofNat k) (Value.ofNat b).modClass = .nop ∧
      printableCode? (Value.ofNat k) = some k ∧ (encrypt k = 74 ∨ encrypt k = 70) := by
  simp [noops] at hb
  rcases hb with rfl | rfl | rfl <;> rcases hk with rfl | rfl <;> decide

/-- Both phases require runtime initialization at these addresses. -/
theorem nop_not_loadable {b k : Nat} (hb : b ∈ noops) (hk : k = 74 ∨ k = 70) :
    Instr.ofOpcode? ((k + b) % 94) = none := by
  simp [noops] at hb
  rcases hb with rfl | rfl | rfl <;> rcases hk with rfl | rfl <;> decide

set_option maxHeartbeats 2000000 in
/-- Return from reset to the rotation entry. Each no-op flips within a
closed orbit; no operand or return record is modified. -/
theorem return_to_rotation {s : State} {w : Nat} {a v : Value}
    (h : MarkerReset.At w a v false 1300 3205 s)
    (hl : Links s.mem) (hr : s.mem.get (Value.ofNat 529) = Value.ofNat 74) :
    ∃ t, Segment 7 s t ∧ MarkerReset.At w a v false 529 3200 t ∧
      Links t.mem ∧ t.mem.get (Value.ofNat 529) = Value.ofNat 74 := by
  obtain ⟨k247, hk247⟩ := h.resident.landing 247 (by decide)
  obtain ⟨k525, hk525⟩ := hl.landing 525 (by decide)
  obtain ⟨k526, hp526, hv526⟩ := hl.nops 526 (by decide)
  obtain ⟨k527, hp527, hv527⟩ := hl.nops 527 (by decide)
  obtain ⟨k528, hp528, hv528⟩ := hl.nops 528 (by decide)
  have h248 := h.resident.static 248 (Value.ofNat 74) (by decide)
  have h249 := h.resident.static 249 (Value.ofNat 37) (by decide)
  have h1300 := hl.static 1300 114 (by decide)
  have h3205 := hl.static 3205 247 (by decide)
  have h3206 := hl.static 3206 3194 (by decide)
  have h3195 := hl.static 3195 248 (by decide)
  have h3196 := hl.static 3196 525 (by decide)
  let s1 : State := { s with
    mem := s.mem.set (Value.ofNat 247) (Value.ofNat (encrypt k247)),
    c := Value.ofNat 248, d := Value.ofNat 3206 }
  have hs1 : step1 s = some s1 := by
    have hh := jump (s := s) (C := 1300) (D := 3205) (T := 247) (k := k247) h.code h.data
      (by simp [h1300]; decide)
      (by simp [h3205])
      (by simp [hk247])
    exact hh
  let s2 : State := { s1 with
    mem := s1.mem.set (Value.ofNat 248) (Value.ofNat (70)),
    c := Value.ofNat 249, d := Value.ofNat 3195 }
  have hs2 : step1 s1 = some s2 := by
    have hh := move (s := s1) (C := 248) (D := 3206) (T := 3194) (k := 74) rfl rfl
      (by simp [s1, get_set_nat, h248]; decide)
      (by simp [s1, get_set_nat, h3206])
      (by simp [s1, get_set_nat, h248]; decide) h.bound
    exact hh
  let s3 : State := { s2 with
    mem := s2.mem.set (Value.ofNat 248) (Value.ofNat (74)),
    c := Value.ofNat 249, d := Value.ofNat 3196 }
  have hs3 : step1 s2 = some s3 := by
    have hh := jump (s := s2) (C := 249) (D := 3195) (T := 248) (k := 70) rfl rfl
      (by simp [s1, s2, get_set_nat, h249]; decide)
      (by simp [s1, s2, get_set_nat, h3195])
      (by simp [s1, s2, get_set_nat]; decide)
    exact hh
  let s4 : State := { s3 with
    mem := s3.mem.set (Value.ofNat 525) (Value.ofNat (encrypt k525)),
    c := Value.ofNat 526, d := Value.ofNat 3197 }
  have hs4 : step1 s3 = some s4 := by
    have hh := jump (s := s3) (C := 249) (D := 3196) (T := 525) (k := k525) rfl rfl
      (by simp [s1, s2, s3, get_set_nat, h249]; decide)
      (by simp [s1, s2, s3, get_set_nat, h3196])
      (by simp [s1, s2, s3, get_set_nat, hk525])
    exact hh
  let s5 : State := { s4 with
    mem := s4.mem.set (Value.ofNat 526) (Value.ofNat (encrypt k526)),
    c := Value.ofNat 527, d := Value.ofNat 3198 }
  have hs5 : step1 s4 = some s5 := by
    have hh := noop (s := s4) (C := 526) (D := 3197) (k := k526) rfl rfl
      (by simp [s1, s2, s3, s4, get_set_nat, hv526]; exact (nop_phase (b := 526)
      (by decide) hp526).1)
      (by simp [s1, s2, s3, s4, get_set_nat, hv526]; exact (nop_phase (b := 526)
      (by decide) hp526).2.1)
    exact hh
  let s6 : State := { s5 with
    mem := s5.mem.set (Value.ofNat 527) (Value.ofNat (encrypt k527)),
    c := Value.ofNat 528, d := Value.ofNat 3199 }
  have hs6 : step1 s5 = some s6 := by
    have hh := noop (s := s5) (C := 527) (D := 3198) (k := k527) rfl rfl
      (by simp [s1, s2, s3, s4, s5, get_set_nat, hv527]; exact (nop_phase (b := 527)
      (by decide) hp527).1)
      (by simp [s1, s2, s3, s4, s5, get_set_nat, hv527]; exact (nop_phase (b := 527)
      (by decide) hp527).2.1)
    exact hh
  let s7 : State := { s6 with
    mem := s6.mem.set (Value.ofNat 528) (Value.ofNat (encrypt k528)),
    c := Value.ofNat 529, d := Value.ofNat 3200 }
  have hs7 : step1 s6 = some s7 := by
    have hh := noop (s := s6) (C := 528) (D := 3199) (k := k528) rfl rfl
      (by simp [s1, s2, s3, s4, s5, s6, get_set_nat, hv528]; exact (nop_phase (b := 528)
      (by decide) hp528).1)
      (by simp [s1, s2, s3, s4, s5, s6, get_set_nat, hv528]; exact (nop_phase (b := 528)
      (by decide) hp528).2.1)
    exact hh
  have hf : ∀ x, (∀ b ∈ ([247,525,526,527,528] : List Nat), x ≠ Value.ofNat b) →
      s7.mem.get x = s.mem.get x := by
    intro x hx
    have h247 := hx 247 (by simp)
    have h525 := hx 525 (by simp)
    have h526 := hx 526 (by simp)
    have h527 := hx 527 (by simp)
    have h528 := hx 528 (by simp)
    by_cases he : x = Value.ofNat 248
    · subst x; simp [s7,s6,s5,s4,s3,s2,s1,get_set_nat,h248]
    simp [s7,s6,s5,s4,s3,s2,s1,get_set_ne,Ne.symm he,Ne.symm h247,
      Ne.symm h525,Ne.symm h526,Ne.symm h527,Ne.symm h528]
  have hres : MarkerReset.Resident s7.mem := by
    constructor
    · intro b v hb
      have hdis : ∀ e ∈ MarkerReset.cells, ∀ z ∈ ([247,525,526,527,528] : List Nat), e.1 ≠ z := by
        unfold MarkerReset.cells; decide
      rw [hf _ (fun z hz => ofNat_ne (hdis (b,v) hb z hz))]
      exact h.resident.static b v hb
    · intro b hb
      by_cases he : b = 247
      · subst b
        have heq : s7.mem.get (Value.ofNat 247) = Value.ofNat (encrypt k247) := by
          simp [s7,s6,s5,s4,s3,s2,s1,get_set_nat]
        rw [heq]; exact printable_after hk247
      · have hd : ∀ z ∈ ([247,525,526,527,528] : List Nat), b ≠ z := by
          intro z hz; simp at hz; simp [MarkerReset.landings] at hb; omega
        rw [hf _ (fun z hz => ofNat_ne (hd z hz))]
        exact h.resident.landing b hb
  have hlinks : Links s7.mem := by
    constructor
    · intro b v hb
      have hdis : ∀ e ∈ cells, ∀ z ∈ ([247,525,526,527,528] : List Nat), e.1 ≠ z := by
        unfold cells; decide
      rw [hf _ (fun z hz => ofNat_ne (hdis (b,v) hb z hz))]
      exact hl.static b v hb
    · intro b hb
      by_cases he : b = 525
      · subst b
        have heq : s7.mem.get (Value.ofNat 525) = Value.ofNat (encrypt k525) := by
          simp [s7,s6,s5,s4,s3,s2,s1,get_set_nat]
        rw [heq]; exact printable_after hk525
      · have hd : ∀ z ∈ ([247,525,526,527,528] : List Nat), b ≠ z := by
          intro z hz; simp at hz; simp [landings] at hb; omega
        rw [hf _ (fun z hz => ofNat_ne (hd z hz))]
        exact hl.landing b hb
    · intro b hb
      simp [noops] at hb
      rcases hb with rfl | rfl | rfl
      · exact ⟨encrypt k526, (nop_phase (b := 526) (by decide) hp526).2.2, by simp [s7,s6,s5,s4,s3,s2,s1,get_set_nat]⟩
      · exact ⟨encrypt k527, (nop_phase (b := 527) (by decide) hp527).2.2, by simp [s7,s6,s5,s4,s3,s2,s1,get_set_nat]⟩
      · exact ⟨encrypt k528, (nop_phase (b := 528) (by decide) hp528).2.2, by simp [s7,s6,s5,s4,s3,s2,s1,get_set_nat]⟩
  refine ⟨s7, ⟨?_, ?_, rfl,rfl,rfl,rfl,rfl⟩,
    ⟨hres,rfl,rfl,h.acc,h.width,h.bound,?_,?_⟩, hlinks, ?_⟩
  · change (step1 s).bind (fun t => run? 6 t) = _
    rw [hs1,Option.bind_some]
    change (step1 s1).bind (fun t => run? 5 t) = _
    rw [hs2,Option.bind_some]
    change (step1 s2).bind (fun t => run? 4 t) = _
    rw [hs3,Option.bind_some]
    change (step1 s3).bind (fun t => run? 3 t) = _
    rw [hs4,Option.bind_some]
    change (step1 s4).bind (fun t => run? 2 t) = _
    rw [hs5,Option.bind_some]
    change (step1 s5).bind (fun t => run? 1 t) = _
    rw [hs6,Option.bind_some]
    change (step1 s6).bind some = _
    rw [hs7,Option.bind_some]
  · intro x hx
    have hsub : ∀ z ∈ ([247,525,526,527,528] : List Nat), z ∈ changed := by decide
    exact hf x (fun z hz => hx z (hsub z hz))
  · rw [hf _ (by intro z hz; simp at hz; exact ofNat_ne (by omega))]; exact h.marker
  · rw [hf _ (by intro z hz; simp at hz; exact ofNat_ne (by omega))]; exact h.router
  · rw [hf _ (by intro z hz; simp at hz; exact ofNat_ne (by omega))]; exact hr

private theorem Links.reset_frame {s t : State} {n : Nat}
    (h : Links s.mem) (hs : MarkerReset.Segment n s t) : Links t.mem := by
  have hc : ∀ e ∈ cells, MarkerReset.Protected (Value.ofNat e.1) := by
    unfold cells MarkerReset.Protected MarkerReset.landings; decide
  have hl : ∀ b ∈ landings, MarkerReset.Protected (Value.ofNat b) := by
    unfold landings MarkerReset.Protected MarkerReset.landings; decide
  have hn : ∀ b ∈ noops, MarkerReset.Protected (Value.ofNat b) := by
    unfold noops MarkerReset.Protected MarkerReset.landings; decide
  constructor
  · intro b v hb; rw [hs.frame _ (hc (b,v) hb)]; exact h.static b v hb
  · intro b hb; rw [hs.frame _ (hl b hb)]; exact h.landing b hb
  · intro b hb
    obtain ⟨k,hk,hv⟩ := h.nops b hb
    exact ⟨k,hk, by rw [hs.frame _ (hn b hb), hv]⟩

/-- The rotation entry, with the same marker equal to one on every visit. -/
structure Ready (w : Nat) (s : State) : Prop where
  state : MarkerReset.At w (Value.ofNat 1) (Value.ofNat 1) false 529 3200 s
  links : Links s.mem
  rotor : s.mem.get (Value.ofNat 529) = Value.ofNat 74

/-- Fifty real steps rotate, reset and return, with the whole calling
invariant restored. The width is arbitrary and does not change. -/
theorem cycle {s : State} {w : Nat} (h : Ready w s) (hw : 1 ≤ w) :
    ∃ t, Segment 50 s t ∧ Ready w t := by
  obtain ⟨u,hu,hat,hl,hr⟩ := rotate h.state h.links h.rotor
  have hv : ZeroOne (Value.rot w (Value.ofNat 1)) := by
    rw [rot_one w hw]; exact zeroOne_power (w - 1)
  obtain ⟨v,hvseg,hvat,hvr⟩ := MarkerReset.call_rotator hat hv hr
  have hseg : Segment 34 u v := by
    refine ⟨hvseg.run, ?_, hvat.width.trans hat.width.symm, hvseg.maxWidth,
      hvseg.input, hvseg.output, hvseg.outClosed⟩
    intro x hx
    by_cases he : x = Value.ofNat 529
    · subst x; rw [hvr,hr]
    by_cases he' : x = Value.ofNat 530
    · subst x; rw [hvat.router,hat.router]
    apply hvseg.frame x
    refine ⟨hx 3200 (by decide), he', ?_⟩
    intro b hb
    simp [MarkerReset.landings] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hx 247 (by decide)
    · exact hx 269 (by decide)
    · exact he
    · exact hx 1299 (by decide)
  obtain ⟨t,ht,htat,htl,htr⟩ := return_to_rotation hvat (hl.reset_frame hvseg) hvr
  exact ⟨t, hu.trans (hseg.trans ht), ⟨htat,htl,htr⟩⟩

/-- Arbitrarily many cycles of one finite resident program. The count is
a proof index; this program deliberately has no exit branch. -/
theorem repeat_cycles {s : State} {w : Nat} (h : Ready w s) (hw : 1 ≤ w) (n : Nat) :
    ∃ t, Segment (50 * n) s t ∧ Ready w t := by
  induction n with
  | zero => exact ⟨s, ⟨rfl,fun _ _ => rfl,rfl,rfl,rfl,rfl,rfl⟩,h⟩
  | succ n ih =>
    obtain ⟨u,hu,hur⟩ := ih
    obtain ⟨t,ht,htr⟩ := cycle hur hw
    exact ⟨t, by simpa only [Nat.mul_succ] using hu.trans ht, htr⟩

/-- Every fuel prefix survives, including prefixes inside a cycle. -/
theorem neverHalts {s : State} {w : Nat} (h : Ready w s) (hw : 1 ≤ w) (fuel : Nat) :
    (exec fuel s).2 = .outOfFuel := by
  obtain ⟨t,ht,_⟩ := repeat_cycles h hw (fuel + 1)
  have he : 50 * (fuel + 1) = fuel + (50 * (fuel + 1) - fuel) := by omega
  have hrun := ht.run
  rw [he, run?_add] at hrun
  cases hp : run? fuel s with
  | none => simp [hp] at hrun
  | some u => rw [exec_of_run? hp]

/-- Natural source operands used to initialize the three no-ops and
load the all-ones constant. The operational write primitive is
`Runtime.initialize_cell`; full source reachability is tested separately. -/
theorem initializer_values :
    Value.crz (Value.crz Value.zero (Value.ofNat 6617)) (Value.ofNat 127) = Value.ofNat 74 ∧
    Value.crz (Value.crz (Value.ofNat 74) (Value.ofNat 6598)) (Value.ofNat 2224) = Value.ofNat 74 ∧
    Value.crz (Value.crz (Value.ofNat 74) (Value.ofNat 6598)) (Value.ofNat 2467) = Value.ofNat 74 ∧
    Value.crz (Value.ofNat 74) (Value.ofNat 317) = ones := by decide

end Langlib.Computability.Unshackled.Runtime.MarkerCycle
