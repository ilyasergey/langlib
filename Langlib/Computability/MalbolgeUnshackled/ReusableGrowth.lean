import Langlib.Computability.MalbolgeUnshackled.Growth

/-!
# Reusable width growth

The two moves at 436 and 440 alternate with no-ops. A jump back to 436
restores the first move without executing it; a four-no-op sweep restores
the second. The three intervening cells use a closed five-word encryption
orbit, all of whose phases are no-ops at these addresses. Eleven actual
steps grow, restore the working code, and return. The source operand is
preserved, so a caller must supply a new rotated one for its next growth.
-/

namespace Langlib.Computability.Unshackled.Runtime.ReusableGrowth

open Langlib.Common Langlib.MalbolgeUnshackled

/-- All phases are printable and decode to no-ops at 437, 438 and 439. -/
def nopCycle : List Nat := [41, 102, 96, 60, 51]

theorem nopCycle_closed {k : Nat} (hk : k ∈ nopCycle) :
    33 ≤ k ∧ k ≤ 126 ∧ encrypt k ∈ nopCycle := by
  simp [nopCycle] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl <;> decide

theorem nopCycle_decode {k : Nat} (hk : k ∈ nopCycle) (i : Fin 3) :
    decode (Value.ofNat k) (Value.ofNat (437 + i.val)).modClass = .nop := by
  have hi := i.isLt
  have hi' : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
  simp [nopCycle] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl <;>
    rcases hi' with h | h | h <;> rw [h] <;> decide

/-- These no-op phases cannot be placed directly in a loaded source at
these addresses. They are produced by the initializer after loading. -/
theorem nopCycle_not_loadable {k : Nat} (hk : k ∈ nopCycle) (i : Fin 3) :
    Instr.ofOpcode? ((k + (437 + i.val)) % 94) = none := by
  have hi := i.isLt
  have hi' : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
  simp [nopCycle] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl <;>
    rcases hi' with h | h | h <;> rw [h] <;> decide

/-- The working phases are exact; the three no-op phases may vary. -/
structure Code (m : Memory) : Prop where
  first : m.get (Value.ofNat 436) = Value.ofNat 74
  last : m.get (Value.ofNat 440) = Value.ofNat 70
  jump : m.get (Value.ofNat 441) = Value.ofNat 33
  noops : ∀ i : Fin 3, ∃ k, k ∈ nopCycle ∧
    m.get (Value.ofNat (437 + i.val)) = Value.ofNat k

private theorem succ_iterate_nat (n k : Nat) :
    (Value.succ^[k]) (Value.ofNat n) = Value.ofNat (n + k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, succ_ofNat]
    simp only [Nat.add_assoc]

set_option maxHeartbeats 1500000 in
/-- Grow once and restore the callable code in eleven interpreter steps.
The distant read is an extensional hypothesis, preserved by finite frames;
it does not require allocating a fresh return table at each width. Only
three no-op phases and the printable landing word can differ on return. -/
theorem call {s : State} {w T wt : Nat}
    (hc : s.c = Value.ofNat 436) (hw : s.rotWidth = w) (hwmin : 10 ≤ w)
    (hm : s.maxWidth < w)
    (hsource : s.mem.get s.d = Value.rot w (Value.ofNat 1))
    (hread : s.mem.get (Value.ofNat (3 ^ (w - 1) + 4)) = Value.ofNat 5001)
    (hcode : Code s.mem)
    (hrestore : s.mem.get (Value.ofNat 5002) = Value.ofNat 436)
    (hreturn : s.mem.get (Value.ofNat 5007) = Value.ofNat T)
    (hlanding : printableCode? (s.mem.get (Value.ofNat T)) = some wt)
    (hT : ∀ i < 6, T ≠ 436 + i) :
    ∃ t, run? 11 s = some t ∧ t.c = Value.ofNat (T + 1)
      ∧ t.d = Value.ofNat 5008 ∧ t.rotWidth = 2 * w ∧ t.maxWidth = w
      ∧ t.a = s.a ∧ t.mem.get (Value.ofNat T) = Value.ofNat (encrypt wt) ∧ Code t.mem
      ∧ (∀ x, x ≠ Value.ofNat T → (∀ i : Fin 3, x ≠ Value.ofNat (437 + i.val)) →
        t.mem.get x = s.mem.get x)
      ∧ t.input = s.input ∧ t.output = s.output ∧ t.outClosed = s.outClosed := by
  choose ks hks hvals using hcode.noops
  let phaseWord (i : Nat) : Nat := ks ⟨(i - 1) % 3, Nat.mod_lt _ (by omega)⟩
  let codes (i : Nat) : Nat := if i = 0 then 74 else if i = 4 then 70 else phaseWord i
  have hn : ∀ i : Fin 3, codes (1 + i.val) = ks i := by
    intro i
    have hi := i.isLt
    dsimp [codes, phaseWord]
    rw [if_neg (by omega), if_neg (by omega)]
    congr 1
    apply Fin.ext
    simp [Nat.mod_eq_of_lt hi]
  have hsmall : 9 ≤ w - 1 := by omega
  have hpow : 3 ^ 9 ≤ 3 ^ (w - 1) := Nat.pow_le_pow_right (by omega) hsmall
  have hfar : 436 + 4 < 3 ^ (w - 1) + 4 := by change 19683 ≤ 3 ^ (w - 1) at hpow; omega
  obtain ⟨s₅, hr₅, hc₅, hd₅, hw₅, hm₅, ha₅, hcells₅, hf₅, hi₅, ho₅, hx₅⟩ :=
    grow_return_of_read codes hc hw (by omega) hm hsource hfar hread
      (by change 8 ≤ w; omega)
      (fun i hi => by
        by_cases h0 : i = 0
        · subst i; rw [hcode.first]; decide
        by_cases h4 : i = 4
        · subst i; rw [hcode.last]; decide
        let j : Fin 3 := ⟨i - 1, by omega⟩
        have ha : 436 + i = 437 + j.val := by dsimp [j]; omega
        rw [ha, hvals j, nopCycle_decode (hks j), if_neg (by omega)])
      (fun i hi => by
        by_cases h0 : i = 0
        · subst i; rw [hcode.first]; change printableCode? (Value.ofNat 74) = some 74; decide
        by_cases h4 : i = 4
        · subst i; rw [hcode.last]; change printableCode? (Value.ofNat 70) = some 70; decide
        let j : Fin 3 := ⟨i - 1, by omega⟩
        have ha : 436 + i = 437 + j.val := by dsimp [j]; omega
        have hj : i = 1 + j.val := by dsimp [j]; omega
        rw [ha, hvals j, hj, hn]
        exact printableCode?_ofNat (nopCycle_closed (hks j)).1 (nopCycle_closed (hks j)).2.1)
  have hfirst₅ : s₅.mem.get (Value.ofNat 436) = Value.ofNat 70 := hcells₅ 0 (by omega)
  have hlast₅ : s₅.mem.get (Value.ofNat 440) = Value.ofNat 74 := hcells₅ 4 (by omega)
  have hnoop₅ (i : Fin 3) :
      s₅.mem.get (Value.ofNat (437 + i.val)) = Value.ofNat (encrypt (ks i)) := by
    simpa only [show 436 + (1 + i.val) = 437 + i.val by omega, hn] using
      hcells₅ (1 + i.val) (by have := i.isLt; omega)
  have hJ₅ : s₅.mem.get (Value.ofNat 441) = Value.ofNat 33 := by
    rw [hf₅ _ (fun i hi => ofNat_ne (by omega)), hcode.jump]
  have hD₅ : s₅.mem.get s₅.d = Value.ofNat 436 := by
    rw [hd₅, show (Value.ofNat 5001).succ = Value.ofNat 5002 from rfl,
      hf₅ _ (fun i hi => ofNat_ne (by omega)), hrestore]
  let s₆ : State := { s₅ with
    mem := s₅.mem.set (Value.ofNat 436) (Value.ofNat 74),
    c := Value.ofNat 437, d := Value.ofNat 5003 }
  have hr₆ : step1 s₅ = some s₆ := by
    have hh := step1_jmp (s := s₅) (code := 70)
      (by rw [hc₅, hJ₅]; decide)
      (by rw [hD₅, hfirst₅]; decide)
    rw [hD₅, hd₅] at hh
    exact hh
  have hf₆ (x : Value) (hx : x ≠ Value.ofNat 436) : s₆.mem.get x = s₅.mem.get x :=
    get_set_ne _ hx.symm _
  let back (i : Nat) := if i = 3 then 74 else encrypt (ks ⟨i % 3, Nat.mod_lt _ (by omega)⟩)
  have hb (i : Fin 3) : back i.val = encrypt (ks i) := by
    dsimp [back]
    rw [if_neg (by have := i.isLt; omega)]
    congr 2
    apply Fin.ext
    exact Nat.mod_eq_of_lt i.isLt
  obtain ⟨s₁₀, hr₁₀, ha₁₀, hc₁₀, hd₁₀, hcells₁₀, hf₁₀, hi₁₀, ho₁₀, hx₁₀, hw₁₀, hm₁₀⟩ :=
    nop_run 4 back (s₀ := s₆) (c₀ := 437) rfl
      (fun i hi => by
        rw [hf₆ _ (ofNat_ne (by omega))]
        by_cases h3 : i = 3
        · subst i; rw [hlast₅]; decide
        let j : Fin 3 := ⟨i, by omega⟩
        rw [hnoop₅ j]
        exact nopCycle_decode (nopCycle_closed (hks j)).2.2 j)
      (fun i hi => by
        rw [hf₆ _ (ofNat_ne (by omega))]
        by_cases h3 : i = 3
        · subst i; rw [hlast₅]; change printableCode? (Value.ofNat 74) = some 74; decide
        let j : Fin 3 := ⟨i, by omega⟩
        rw [hnoop₅ j, hb j]
        have hh := nopCycle_closed (nopCycle_closed (hks j)).2.2
        exact printableCode?_ofNat hh.1 hh.2.1)
  have hJ₁₀ : s₁₀.mem.get (Value.ofNat 441) = Value.ofNat 33 := by
    rw [hf₁₀ _ (fun i hi => ofNat_ne (by omega)), hf₆ _ (by decide), hJ₅]
  have hD₁₀ : s₁₀.mem.get s₁₀.d = Value.ofNat T := by
    rw [hd₁₀]
    change s₁₀.mem.get ((Value.succ^[4]) (Value.ofNat 5003)) = _
    rw [succ_iterate_nat, hf₁₀ _ (fun i hi => ofNat_ne (by omega)), hf₆ _ (by decide),
      hf₅ _ (fun i hi => ofNat_ne (by omega)), hreturn]
  have hfT : s₁₀.mem.get (Value.ofNat T) = s.mem.get (Value.ofNat T) := by
    rw [hf₁₀ _ (fun i hi => ofNat_ne (by have := hT (i + 1) (by omega); omega)),
      hf₆ _ (ofNat_ne (by have := hT 0 (by omega); omega)),
      hf₅ _ (fun i hi => ofNat_ne (hT i (by omega)))]
  let t : State := { s₁₀ with
    mem := s₁₀.mem.set (Value.ofNat T) (Value.ofNat (encrypt wt)),
    c := Value.ofNat (T + 1), d := Value.ofNat 5008 }
  have hrt : step1 s₁₀ = some t := by
    have hh := step1_jmp (s := s₁₀) (code := wt)
      (by rw [hc₁₀, hJ₁₀]; decide)
      (by rw [hD₁₀, hfT]; exact hlanding)
    rw [hD₁₀, hd₁₀] at hh
    simpa only [show s₆.d = Value.ofNat 5003 from rfl, succ_iterate_nat, succ_ofNat] using hh
  have hft (x : Value) (hx : x ≠ Value.ofNat T) : t.mem.get x = s₁₀.mem.get x :=
    get_set_ne _ hx.symm _
  have hf : ∀ x, x ≠ Value.ofNat T → (∀ i : Fin 3, x ≠ Value.ofNat (437 + i.val)) →
      t.mem.get x = s.mem.get x := by
    intro x hx ht
    rw [hft x hx]
    by_cases h436 : x = Value.ofNat 436
    · subst x
      rw [hf₁₀ _ (fun i hi => ofNat_ne (by omega)), get_set_self, hcode.first]
    by_cases h440 : x = Value.ofNat 440
    · subst x
      rw [hcode.last]
      exact hcells₁₀ 3 (by omega)
    rw [hf₁₀ _ (fun i hi => by
      by_cases h3 : i = 3
      · subst i; exact h440
      exact ht ⟨i, by omega⟩), hf₆ x h436, hf₅ _ (fun i hi => by
      by_cases h0 : i = 0
      · subst i; exact h436
      by_cases h4 : i = 4
      · subst i; exact h440
      simpa only [show 437 + (i - 1) = 436 + i by omega] using ht ⟨i - 1, by omega⟩)]
  refine ⟨t, ?_, rfl, rfl, hw₁₀.trans hw₅, hm₁₀.trans hm₅,
    ha₁₀.trans ha₅, get_set_self _ _ _, ?_, hf, hi₁₀.trans hi₅, ho₁₀.trans ho₅, hx₁₀.trans hx₅⟩
  · rw [show (11 : Nat) = 5 + (1 + (4 + 1)) from rfl, run?_add, hr₅,
      Option.bind_some, run?_add, run?_one, hr₆, Option.bind_some,
      run?_add, hr₁₀, Option.bind_some, run?_one, hrt]
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hf _ (ofNat_ne (by have := hT 0 (by omega); omega))
        (fun i => ofNat_ne (by omega)), hcode.first]
    · rw [hf _ (ofNat_ne (by have := hT 4 (by omega); omega))
        (fun i => ofNat_ne (by have := i.isLt; omega)), hcode.last]
    · rw [hf _ (ofNat_ne (by have := hT 5 (by omega); omega))
        (fun i => ofNat_ne (by have := i.isLt; omega)), hcode.jump]
    · intro i
      refine ⟨encrypt (encrypt (ks i)), (nopCycle_closed (nopCycle_closed (hks i)).2.2).2.2, ?_⟩
      rw [hft _ (ofNat_ne (by have := hT (1 + i.val) (by have := i.isLt; omega); omega))]
      simpa only [hb i] using hcells₁₀ i.val (by have := i.isLt; omega)

/-- The example's last two source characters land at 7000 and 7001.
The penultimate address determines the fill phase. -/
theorem seed_return :
    (restTable (Value.ofNat 5001) (Value.ofNat 5001) 7000).getD 1 Value.zero =
      Value.ofNat 5001 := by decide

/-- Every future growth address returns the same fixed pointer. Only one
residue of distant memory is constrained, using the actual seeded fill. -/
def Returns (m : Memory) : Prop :=
  ∀ w, 10 ≤ w → m.get (Value.ofNat (3 ^ (w - 1) + 4)) = Value.ofNat 5001

private theorem remote_large {w : Nat} (hw : 10 ≤ w) :
    7002 ≤ 3 ^ (w - 1) + 4 := by
  have hh := Nat.pow_le_pow_right (n := 3) (by omega : 0 < 3) (by omega : 9 ≤ w - 1)
  change 19683 ≤ 3 ^ (w - 1) at hh
  omega

/-- Finite source overrides and the canonical fill establish `Returns`.
This does not assume blank distant memory or allocate remote return tables. -/
theorem Returns.of_fill {m : Memory}
    (hrest : m.rest = restTable (Value.ofNat 5001) (Value.ofNat 5001) 7000)
    (hfinite : ∀ n, 7002 ≤ n → ¬ m.cells.contains (Value.ofNat n)) : Returns m := by
  intro w hw
  rw [get_of_not_mem (hfinite _ (remote_large hw)), growth_fill m (by omega),
    hrest, seed_return]

/-- The footprint of a growth call preserves all future return reads,
including those much wider than the call just completed. -/
theorem Returns.frame {m m' : Memory} {T : Nat} (h : Returns m) (hT : T < 7002)
    (hf : ∀ x, x ≠ Value.ofNat T → (∀ i : Fin 3, x ≠ Value.ofNat (437 + i.val)) →
      m'.get x = m.get x) : Returns m' := by
  intro w hw
  have hlarge := remote_large hw
  rw [hf _ (ofNat_ne (by omega)) (fun i => ofNat_ne (by have := i.isLt; omega))]
  exact h w hw

/-- The complete resident growth service: code, unconsumed return table,
printable continuation landing, and reads for every future width. -/
structure Resident (m : Memory) : Prop where
  code : Code m
  returns : Returns m
  restore : m.get (Value.ofNat 5002) = Value.ofNat 436
  target : m.get (Value.ofNat 5007) = Value.ofNat 1199
  landing : ∃ k, printableCode? (m.get (Value.ofNat 1199)) = some k

/-- The service returns with its full invariant, not just its current code
words. The caller still has to supply a rotated one at the next width. -/
theorem call_resident {s : State} {w : Nat} (h : Resident s.mem)
    (hc : s.c = Value.ofNat 436) (hw : s.rotWidth = w) (hwmin : 10 ≤ w)
    (hm : s.maxWidth < w)
    (hsource : s.mem.get s.d = Value.rot w (Value.ofNat 1)) :
    ∃ t, run? 11 s = some t ∧ t.c = Value.ofNat 1200 ∧ t.d = Value.ofNat 5008
      ∧ t.rotWidth = 2 * w ∧ t.maxWidth = w ∧ t.a = s.a ∧ Resident t.mem
      ∧ (∀ x, x ≠ Value.ofNat 1199 → (∀ i : Fin 3, x ≠ Value.ofNat (437 + i.val)) →
        t.mem.get x = s.mem.get x)
      ∧ t.input = s.input ∧ t.output = s.output ∧ t.outClosed = s.outClosed := by
  obtain ⟨k, hk⟩ := h.landing
  obtain ⟨t, hr, hc', hd', hw', hm', ha, hl, hcode, hf, hi, ho, hx⟩ :=
    call hc hw hwmin hm hsource (h.returns w hwmin) h.code h.restore h.target hk
      (fun i hi => by omega)
  refine ⟨t, hr, hc', hd', hw', hm', ha, ?_, hf, hi, ho, hx⟩
  refine ⟨hcode, h.returns.frame (by decide) hf, ?_, ?_, ?_⟩
  · rw [hf _ (by decide) (fun i => ofNat_ne (by have := i.isLt; omega))]
    exact h.restore
  · rw [hf _ (by decide) (fun i => ofNat_ne (by have := i.isLt; omega))]
    exact h.target
  · refine ⟨encrypt k, ?_⟩
    rw [hl]
    have hb := printableCode?_bounds hk
    have he := encrypt_range hb.1 hb.2
    exact printableCode?_ofNat he.1 he.2

/-- Exact values synthesized by the example's three initialization pairs.
Each pair writes its second result to one of the no-op cells. -/
theorem initializer_values :
    Value.crz (Value.crz (Value.ofNat 0) (Value.ofNat 2265)) (Value.ofNat 2267) = Value.ofNat 41 ∧
    Value.crz (Value.crz (Value.ofNat 41) (Value.ofNat 217)) (Value.ofNat 180) = Value.ofNat 102 ∧
    Value.crz (Value.crz (Value.ofNat 102) (Value.ofNat 6561)) (Value.ofNat 6567) = Value.ofNat 96 := by
  decide

end Langlib.Computability.Unshackled.Runtime.ReusableGrowth
