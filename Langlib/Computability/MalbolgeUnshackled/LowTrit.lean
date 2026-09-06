import Langlib.Computability.MalbolgeUnshackled.Marker
import Langlib.Computability.MalbolgeUnshackled.PaddedCrazy

/-!
# A low-trit test with restorable scratch

Two crazy operations extract the low trit of a zero/one marker. The second
scratch cell can already contain either bit; it needs no separate clearing.
Running the same operations with an all-ones accumulator restores the first
scratch and leaves one in the second. The operational calls below restore
code and records, while naming both scratch values explicitly.
-/
namespace Langlib.Computability.Unshackled.Runtime.LowTrit
open Langlib.Common Langlib.MalbolgeUnshackled Routing

/-- Twos everywhere except the low trit. -/
def mask : Value := Value.mk' .t2 [.t0]
def bit (b : Bool) : Value := Value.ofNat (if b then 1 else 0)
def spent (b : Bool) : Value := Value.mk' .t2 [if b then .t0 else .t1]
def low (v : Value) : Bool := v.trit 0 == .t1

/-- All higher zero/one trits collapse to two in the first scratch. -/
theorem extract_first {v : Value} (hv : Marker.ZeroOne v) :
    Value.crz v mask = spent (low v) := by
  apply ext_of_trits (crz_normalized _ _) (Value.normalized_mk' _ _)
  · rw [crz_lead, hv.1]; rfl
  · intro i
    rw [crz_trit]
    simp only [mask, trit_mk']
    cases i with
    | zero =>
      have hh := hv.2 0
      cases he : v.trit 0 <;> simp_all [low, crzTrit]
    | succ i =>
      have hh := hv.2 (i + 1)
      cases he : v.trit (i + 1) <;> simp_all [crzTrit]

/-- The previous result bit is a valid operand for the next extraction. -/
theorem extract_second (b old : Bool) : Value.crz (spent b) (bit old) = bit b := by
  cases b <;> cases old <;> decide

theorem extract {v : Value} (hv : Marker.ZeroOne v) (old : Bool) :
    Value.crz (Value.crz v mask) (bit old) = bit (low v) := by
  rw [extract_first hv, extract_second]

/-- Both paths restore the mask using the same accumulator and instructions. -/
theorem reset_first (b : Bool) : Value.crz Marker.ones (spent b) = mask := by
  cases b <;> decide

theorem reset_second (b : Bool) : Value.crz mask (bit b) = bit true := by
  cases b <;> decide

/-- Every position of a rotating one-marker satisfies the extractor's
zero/one precondition, for arbitrarily many rotations. -/
theorem marker_zeroOne {w : Nat} (hw : 0 < w) (n : Nat) :
    Marker.ZeroOne (rotateTimes w n (Value.ofNat 1)) := by
  let xs := Value.padTo w .t0 (Value.ofNat 1).low
  have hlen : xs.length = w := length_padTo _ _ _ (by change 1 ≤ w; omega)
  have he := rotateTimes_window .t0 xs n
  have hpad : Value.mk' .t0 xs = Value.ofNat 1 :=
    window_eq (show (Value.ofNat 1).Normalized from by unfold Value.Normalized; decide) w
  rw [hlen,hpad] at he
  refine ⟨by rw [he]; rfl,?_⟩
  intro i
  rw [he,trit_mk']
  have hm : ∀ t ∈ xs.rotate n, t ≠ Trit.t2 := by
    intro t ht
    rw [List.mem_rotate] at ht
    simp [xs,Value.padTo,Value.ofNat,Value.natTrits,Value.natTritsAux] at ht
    rcases ht with rfl | ⟨_,rfl⟩ <;> decide
  have hget : ∀ (l : List Trit), (∀ t ∈ l, t ≠ Trit.t2) → ∀ i, l.getD i .t0 ≠ .t2 := by
    intro l hl i
    induction l generalizing i with
    | nil => simp
    | cons t ts ih =>
      cases i with
      | zero => exact hl t (by simp)
      | succ i => exact ih (fun t ht => hl t (by simp [ht])) i
  exact hget _ hm i

/-- The arithmetic exit test agrees with the marker's rotation period. -/
theorem low_marker {w : Nat} (hw : 0 < w) (n : Nat) :
    low (rotateTimes w n (Value.ofNat 1)) = (n % w == 0) := by
  rw [low, marker_low hw]
  split <;> simp_all

def cells : List (Nat × Nat) :=
  [(270,74),(271,109),(248,74),(249,37),
   (4001,270),(4002,247),(4003,4197),(4198,248),(4199,269),
   (4201,270),(4202,599)]

def landings : List Nat := [247,269,599]
def writes : List Nat := [4000,4200] ++ landings

structure Resident (m : Memory) : Prop where
  static : ∀ a v, (a,v) ∈ cells → m.get (Value.ofNat a) = Value.ofNat v
  landing : ∀ a ∈ landings, ∃ k, printableCode? (m.get (Value.ofNat a)) = some k

private theorem Resident.frame {m m' : Memory} (h : Resident m)
    (hf : ∀ x, (∀ a ∈ writes, x ≠ Value.ofNat a) → m'.get x = m.get x)
    (hl : ∀ a ∈ landings, ∃ k, printableCode? (m'.get (Value.ofNat a)) = some k) :
    Resident m' := by
  refine ⟨?_,hl⟩
  intro a v ha
  have hd : ∀ e ∈ cells, ∀ a ∈ writes, e.1 ≠ a := by unfold cells writes landings; decide
  rw [hf _ (fun b hb => ofNat_ne (hd (a,v) ha b hb))]
  exact h.static a v ha

structure Trace (s t : State) : Prop where
  run : run? 9 s = some t
  resident : Resident t.mem
  code : t.c = Value.ofNat 600
  data : t.d = Value.ofNat 4203
  first : t.mem.get (Value.ofNat 4000) = Value.crz s.a (s.mem.get (Value.ofNat 4000))
  second : t.mem.get (Value.ofNat 4200) =
    Value.crz (Value.crz s.a (s.mem.get (Value.ofNat 4000))) (s.mem.get (Value.ofNat 4200))
  acc : t.a = t.mem.get (Value.ofNat 4200)
  frame : ∀ x, (∀ a ∈ writes, x ≠ Value.ofNat a) → t.mem.get x = s.mem.get x
  width : t.rotWidth = s.rotWidth
  maxWidth : t.maxWidth = s.maxWidth
  input : t.input = s.input
  output : t.output = s.output
  outClosed : t.outClosed = s.outClosed

/-- The same nine real instructions implement extraction and scratch reset.
No precondition on either arithmetic operand is hidden in the resident code. -/
theorem pair_call {s : State} (h : Resident s.mem)
    (hc : s.c = Value.ofNat 270) (hd : s.d = Value.ofNat 4000)
    (hm : 8 ≤ s.maxWidth) : ∃ t, Trace s t := by
  obtain ⟨k247,h247⟩ := h.landing 247 (by decide)
  obtain ⟨k269,h269⟩ := h.landing 269 (by decide)
  obtain ⟨k599,h599⟩ := h.landing 599 (by decide)
  obtain ⟨u,hu,hua,huc,hud,hut,huv,_,_,huf,hui,huo,hux,huw,hum⟩ :=
    work_call .crazy hc hd (by decide) (by decide) (by decide) (by intro i hi; omega)
      (h.static 270 74 (by decide)) (by decide)
      (by rw [h.static 271 109 (by decide)]; decide)
      (h.static 4001 270 (by decide)) (h.static 4002 247 (by decide)) h247
  have huFrame : ∀ x, (∀ a ∈ writes, x ≠ Value.ofNat a) → u.mem.get x = s.mem.get x :=
    fun x hx => huf x (hx 4000 (by decide)) (hx 247 (by decide))
  have hur : Resident u.mem := h.frame huFrame (by
    intro a ha
    simp [landings] at ha
    rcases ha with rfl | rfl | rfl
    · rw [hut]; exact printable_after h247
    · rw [huf _ (by decide) (by decide)]; exact ⟨k269,h269⟩
    · rw [huf _ (by decide) (by decide)]; exact ⟨k599,h599⟩)
  obtain ⟨v,hv,hva,hvc,hvd,hvt,_,_,hvf,hvi,hvo,hvx,hvw,hvm⟩ :=
    movd_call huc (by rw [hud]; exact hur.static 4003 4197 (by decide))
      (by rw [hum]; exact hm) (by decide) (by decide) (by decide)
      (hur.static 248 74 (by decide)) (by decide)
      (by rw [hur.static 249 37 (by decide)]; decide)
      (hur.static 4198 248 (by decide)) (hur.static 4199 269 (by decide))
      (by rw [huf _ (by decide) (by decide)]; exact h269)
  have hvFrame : ∀ x, (∀ a ∈ writes, x ≠ Value.ofNat a) → v.mem.get x = u.mem.get x :=
    fun x hx => hvf x (hx 269 (by decide))
  have hvr : Resident v.mem := hur.frame hvFrame (by
    intro a ha
    by_cases he : a = 269
    · subst a; rw [hvt]; exact printable_after h269
    · rw [hvf _ (ofNat_ne he)]; exact hur.landing a ha)
  obtain ⟨t,ht,hta,htc,htd,htt,htv,_,_,htf,hti,hto,htx,htw,htm⟩ :=
    work_call .crazy hvc hvd (by decide) (by decide) (by decide) (by intro i hi; omega)
      (hvr.static 270 74 (by decide)) (by decide)
      (by rw [hvr.static 271 109 (by decide)]; decide)
      (hvr.static 4201 270 (by decide)) (hvr.static 4202 599 (by decide))
      (by rw [hvf _ (by decide),huf _ (by decide) (by decide)]; exact h599)
  have htFrame : ∀ x, (∀ a ∈ writes, x ≠ Value.ofNat a) → t.mem.get x = v.mem.get x :=
    fun x hx => htf x (hx 4200 (by decide)) (hx 599 (by decide))
  have htr : Resident t.mem := hvr.frame htFrame (by
    intro a ha
    by_cases he : a = 599
    · subst a; rw [htt]; exact printable_after h599
    · rw [htf _ (ofNat_ne (by simp [landings] at ha; omega)) (ofNat_ne he)]
      exact hvr.landing a ha)
  refine ⟨t,⟨?_,htr,htc,htd,?_,?_,htv.symm,?_,htw.trans (hvw.trans huw),
    htm.trans (hvm.trans hum),hti.trans (hvi.trans hui),
    hto.trans (hvo.trans huo),htx.trans (hvx.trans hux)⟩⟩
  · change run? (3 + (3 + 3)) s = some t
    rw [run?_add,hu,Option.bind_some,run?_add,hv,Option.bind_some,ht]
  · rw [htf _ (by decide) (by decide),hvf _ (by decide),huv,hua]; rfl
  · rw [htv,hta,hva,hua,hvf _ (by decide),huf _ (by decide) (by decide)]; rfl
  · intro x hx; rw [htFrame x hx,hvFrame x hx,huFrame x hx]

/-- Extract the marker's low bit, preserving the callable code and records. -/
theorem test {s : State} (h : Resident s.mem)
    (hc : s.c = Value.ofNat 270) (hd : s.d = Value.ofNat 4000) (hm : 8 ≤ s.maxWidth)
    (hv : Marker.ZeroOne s.a) (hmask : s.mem.get (Value.ofNat 4000) = mask)
    (old : Bool) (hbit : s.mem.get (Value.ofNat 4200) = bit old) :
    ∃ t, Trace s t ∧ t.a = bit (low s.a) ∧
      t.mem.get (Value.ofNat 4000) = spent (low s.a) ∧
      t.mem.get (Value.ofNat 4200) = bit (low s.a) := by
  obtain ⟨t,ht⟩ := pair_call h hc hd hm
  have hb : t.mem.get (Value.ofNat 4200) = bit (low s.a) := by
    rw [ht.second,hmask,hbit,extract hv]
  exact ⟨t,ht,ht.acc.trans hb,by rw [ht.first,hmask,extract_first hv],hb⟩

/-- An actual extractor call on the rotating marker returns one exactly
at a multiple of the working width. Connecting that bit to dispatch is a
separate control-flow obligation. -/
theorem test_marker {s : State} (hw : 0 < s.rotWidth) (n : Nat)
    (h : Resident s.mem) (hc : s.c = Value.ofNat 270) (hd : s.d = Value.ofNat 4000)
    (hm : 8 ≤ s.maxWidth) (ha : s.a = rotateTimes s.rotWidth n (Value.ofNat 1))
    (hmask : s.mem.get (Value.ofNat 4000) = mask)
    (old : Bool) (hbit : s.mem.get (Value.ofNat 4200) = bit old) :
    ∃ t, Trace s t ∧ t.a = bit (n % s.rotWidth == 0) ∧
      t.mem.get (Value.ofNat 4000) = spent (n % s.rotWidth == 0) ∧
      t.mem.get (Value.ofNat 4200) = bit (n % s.rotWidth == 0) := by
  have hv : Marker.ZeroOne s.a := by rw [ha]; exact marker_zeroOne hw n
  simpa only [ha,low_marker hw] using test h hc hd hm hv hmask old hbit

/-- Reload all-ones before this call to restore both scratch operands. The
caller must execute the load, for example a working rotation call on the
all-ones cell, justified by `Marker.rotate_ones`. -/
theorem reset {s : State} (h : Resident s.mem)
    (hc : s.c = Value.ofNat 270) (hd : s.d = Value.ofNat 4000) (hm : 8 ≤ s.maxWidth)
    (ha : s.a = Marker.ones) (b old : Bool)
    (hmask : s.mem.get (Value.ofNat 4000) = spent b)
    (hbit : s.mem.get (Value.ofNat 4200) = bit old) :
    ∃ t, Trace s t ∧ t.mem.get (Value.ofNat 4000) = mask ∧
      t.mem.get (Value.ofNat 4200) = bit true ∧ t.a = bit true := by
  obtain ⟨t,ht⟩ := pair_call h hc hd hm
  have hb : t.mem.get (Value.ofNat 4200) = bit true := by
    rw [ht.second,ha,hmask,hbit,reset_first,reset_second]
  exact ⟨t,ht,by rw [ht.first,ha,hmask,reset_first],hb,ht.acc.trans hb⟩

/-- The fourteen-step variant extracts the marker bit while retaining two
independent branch continuations beside the result. Unlike the nine-step
routine, it uses padded work records and no intermediate pointer reset. -/
theorem test_padded {s : State} {D T kt k363 : Nat}
    (h : PaddedCrazy.Code s.mem) (hc : s.c = Value.ofNat 364) (hd : s.d = Value.ofNat D)
    (hD : 368 ≤ D) (hT : T < 364)
    (hr1 : s.mem.get (Value.ofNat (D + 3)) = Value.ofNat 364)
    (ht1 : s.mem.get (Value.ofNat (D + 6)) = Value.ofNat 363)
    (hr2 : s.mem.get (Value.ofNat (D + 10)) = Value.ofNat 364)
    (ht2 : s.mem.get (Value.ofNat (D + 13)) = Value.ofNat T)
    (h363 : printableCode? (s.mem.get (Value.ofNat 363)) = some k363)
    (hlanding : printableCode? (s.mem.get (Value.ofNat T)) = some kt)
    (hw : 0 < s.rotWidth) (n : Nat)
    (ha : s.a = rotateTimes s.rotWidth n (Value.ofNat 1))
    (hmask : s.mem.get (Value.ofNat D) = mask) (old : Bool)
    (hbit : s.mem.get (Value.ofNat (D + 7)) = bit old) :
    ∃ t, run? 14 s = some t ∧ PaddedCrazy.Code t.mem ∧
      t.a = bit (n % s.rotWidth == 0) ∧
      t.mem.get (Value.ofNat D) = spent (n % s.rotWidth == 0) ∧
      t.mem.get (Value.ofNat (D + 7)) = bit (n % s.rotWidth == 0) ∧
      t.c = Value.ofNat (T + 1) ∧ t.d = Value.ofNat (D + 14) ∧
      t.mem.get (Value.ofNat (D + 8)) = s.mem.get (Value.ofNat (D + 8)) ∧
      t.mem.get (Value.ofNat (D + 9)) = s.mem.get (Value.ofNat (D + 9)) ∧
      (∀ x, x ≠ Value.ofNat D → x ≠ Value.ofNat (D + 7) →
        x ≠ Value.ofNat 363 → x ≠ Value.ofNat T → t.mem.get x = s.mem.get x) ∧
      (∃ k, printableCode? (t.mem.get (Value.ofNat 363)) = some k) ∧
      (∃ k, printableCode? (t.mem.get (Value.ofNat T)) = some k) ∧
      t.rotWidth = s.rotWidth ∧ t.maxWidth = s.maxWidth ∧
      t.input = s.input ∧ t.output = s.output ∧ t.outClosed = s.outClosed := by
  obtain ⟨t,hr,hcode,hfirst,hacc,hsecond,hcc,hdc,hb1,hb2,hframe,hl1,hl2,hw',hm,hi,ho,hx⟩ :=
    PaddedCrazy.pair_call h hc hd hD hT hr1 ht1 hr2 ht2 h363 hlanding
  have hv : Marker.ZeroOne s.a := by rw [ha]; exact marker_zeroOne hw n
  have hb : low s.a = (n % s.rotWidth == 0) := by rw [ha,low_marker hw]
  rw [hmask,extract_first hv,hb] at hfirst
  rw [hmask,hbit,extract hv,hb] at hacc
  exact ⟨t,hr,hcode,hacc,hfirst,hsecond.trans hacc,hcc,hdc,hb1,hb2,hframe,hl1,hl2,hw',hm,hi,ho,hx⟩

end Langlib.Computability.Unshackled.Runtime.LowTrit
