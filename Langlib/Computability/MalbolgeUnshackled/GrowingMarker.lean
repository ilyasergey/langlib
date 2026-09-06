import Langlib.Computability.MalbolgeUnshackled.MarkerCycle
import Langlib.Computability.MalbolgeUnshackled.ReusableGrowth

/-!
# Repeated width growth using one marker

Rotate, enter growth, return to reset, and regenerate one at the new width.
The finite resident program and its distant return reads survive every call.
-/
namespace Langlib.Computability.Unshackled.Runtime.GrowingMarker
open Langlib.Common Langlib.MalbolgeUnshackled Routing

-- All no-op addresses introduced by the two connecting routes.
def noops : List Nat :=
  [146,147,148,149,150,151,152,429,430,431,432,433,434,435,1400,1401,1402,1403]

def orbit (a : Nat) : List Nat :=
  if a = 435 ∨ a = 1402 then ReusableGrowth.nopCycle else [74,70]

theorem orbit_valid : ∀ a ∈ noops, ∀ k ∈ orbit a,
    decode (Value.ofNat k) (Value.ofNat a).modClass = .nop ∧
      printableCode? (Value.ofNat k) = some k ∧ encrypt k ∈ orbit a := by
  unfold noops orbit ReusableGrowth.nopCycle
  decide

theorem orbit_not_loadable : ∀ a ∈ noops, ∀ k ∈ orbit a,
    Instr.ofOpcode? ((k + a) % 94) = none := by
  unfold noops orbit ReusableGrowth.nopCycle
  decide

def Noops (m : Memory) : Prop :=
  ∀ a ∈ noops, ∃ k, k ∈ orbit a ∧ m.get (Value.ofNat a) = Value.ofNat k

def records : List (Nat × Nat) :=
  [(1404,104),(3004,247),(3005,3190),(3191,248),(3192,428),
   (1200,120),(5008,247),(5009,2990),(2991,248),(2992,145)]

def landings : List Nat := [145,428]

structure Extras (m : Memory) : Prop where
  static : ∀ a v, (a,v) ∈ records → m.get (Value.ofNat a) = Value.ofNat v
  nops : Noops m
  landing : ∀ a ∈ landings, ∃ k, printableCode? (m.get (Value.ofNat a)) = some k

structure Context (m : Memory) : Prop where
  reset : MarkerReset.Resident m
  links : MarkerCycle.Links m 1399
  growth : ReusableGrowth.Resident m
  extras : Extras m
  rotor : m.get (Value.ofNat 529) = Value.ofNat 74
  router : m.get (Value.ofNat 530) = Value.ofNat 74

/-- Only these cells can change during the connecting routes. -/
def bridgeWrites : List Nat := [145,247,428] ++ noops

def Frame (writes : List Nat) (m m' : Memory) : Prop :=
  ∀ x, (∀ a ∈ writes, x ≠ Value.ofNat a) → m'.get x = m.get x

private theorem frame_read {writes : List Nat} {m m' : Memory} {a : Nat}
    (h : Frame writes m m') (ha : a ∉ writes) : m'.get (Value.ofNat a) = m.get (Value.ofNat a) :=
  h _ (fun b hb => ofNat_ne (by intro he; subst b; exact ha hb))

private theorem distant_bound {w : Nat} (hw : 10 ≤ w) :
    19687 ≤ 3 ^ (w - 1) + 4 := by
  have hp := Nat.pow_le_pow_right (n := 3) (by omega : 0 < 3) (by omega : 9 ≤ w - 1)
  change 19683 ≤ 3 ^ (w - 1) at hp
  omega

private theorem growth_frame {writes : List Nat} {m m' : Memory}
    (h : ReusableGrowth.Resident m) (hf : Frame writes m m')
    (hsmall : ∀ a ∈ writes, a < 19687)
    (hfixed : ∀ a ∈ ([436,437,438,439,440,441,5002,5007,1199] : List Nat), a ∉ writes) :
    ReusableGrowth.Resident m' := by
  have hr a ha := frame_read hf (hfixed a ha)
  refine ⟨⟨?_,?_,?_,?_⟩,?_,?_,?_,?_⟩
  · rw [hr 436 (by decide)]; exact h.code.first
  · rw [hr 440 (by decide)]; exact h.code.last
  · rw [hr 441 (by decide)]; exact h.code.jump
  · intro i
    obtain ⟨k,hk,hv⟩ := h.code.noops i
    refine ⟨k,hk,?_⟩
    rw [hr (437 + i.val) (by have := i.isLt; simp; omega),hv]
  · intro w hw
    rw [frame_read hf (by intro hh; have := hsmall _ hh; have := distant_bound hw; omega)]
    exact h.returns w hw
  · rw [hr 5002 (by decide)]; exact h.restore
  · rw [hr 5007 (by decide)]; exact h.target
  · rw [hr 1199 (by decide)]; exact h.landing

private theorem extras_frame {writes : List Nat} {m m' : Memory}
    (h : Extras m) (hf : Frame writes m m')
    (hc : ∀ e ∈ records, e.1 ∉ writes)
    (hn : ∀ a ∈ noops, a ∉ writes) (hl : ∀ a ∈ landings, a ∉ writes) : Extras m' := by
  constructor
  · intro a v ha; rw [frame_read hf (hc (a,v) ha)]; exact h.static a v ha
  · intro a ha
    obtain ⟨k,hk,hv⟩ := h.nops a ha
    exact ⟨k,hk,by rw [frame_read hf (hn a ha),hv]⟩
  · intro a ha; rw [frame_read hf (hl a ha)]; exact h.landing a ha

private theorem Context.bridge_frame {m m' : Memory} (h : Context m)
    (hf : Frame bridgeWrites m m') (hn : Noops m')
    (hl : ∀ a ∈ ([145,247,428] : List Nat), ∃ k, printableCode? (m'.get (Value.ofNat a)) = some k) :
    Context m' := by
  have hreset : MarkerReset.Resident m' := by
    constructor
    · intro a v ha
      have hd : ∀ e ∈ MarkerReset.cells, e.1 ∉ bridgeWrites := by
        unfold MarkerReset.cells bridgeWrites noops; decide
      rw [frame_read hf (hd (a,v) ha)]
      exact h.reset.static a v ha
    · intro a ha
      by_cases he : a = 247
      · subst a; exact hl 247 (by decide)
      · have hd : a ∉ bridgeWrites := by
          simp [MarkerReset.landings] at ha
          simp [bridgeWrites,noops]
          omega
        rw [frame_read hf hd]
        exact h.reset.landing a ha
  have hlinks : MarkerCycle.Links m' 1399 := by
    constructor
    · intro a v ha
      have hd : ∀ e ∈ MarkerCycle.cells 1399, e.1 ∉ bridgeWrites := by
        unfold MarkerCycle.cells bridgeWrites noops; decide
      rw [frame_read hf (hd (a,v) ha)]
      exact h.links.static a v ha
    · intro a ha
      have hd : ∀ a ∈ MarkerCycle.landings 1399, a ∉ bridgeWrites := by
        unfold MarkerCycle.landings bridgeWrites noops; decide
      rw [frame_read hf (hd a ha)]
      exact h.links.landing a ha
    · intro a ha
      have hd : ∀ a ∈ MarkerCycle.noops, a ∉ bridgeWrites := by
        unfold MarkerCycle.noops bridgeWrites noops; decide
      obtain ⟨k,hk,hv⟩ := h.links.nops a ha
      exact ⟨k,hk,by rw [frame_read hf (hd a ha),hv]⟩
  have hextra : Extras m' := by
    refine ⟨?_,hn,?_⟩
    · intro a v ha
      have hd : ∀ e ∈ records, e.1 ∉ bridgeWrites := by
        unfold records bridgeWrites noops; decide
      rw [frame_read hf (hd (a,v) ha)]
      exact h.extras.static a v ha
    · intro a ha
      exact hl a (by simp [landings] at ha; simp; omega)
  refine ⟨hreset,hlinks,?_,hextra,?_,?_⟩
  · exact growth_frame h.growth hf (by unfold bridgeWrites noops; decide)
      (by unfold bridgeWrites noops; decide)
  · rw [frame_read hf (by decide)]; exact h.rotor
  · rw [frame_read hf (by decide)]; exact h.router

/-- A bridge preserves both widths, the accumulator, marker and all I/O. -/
structure Segment (n : Nat) (s t : State) : Prop where
  run : run? n s = some t
  context : Context t.mem
  frame : Frame bridgeWrites s.mem t.mem
  acc : t.a = s.a
  width : t.rotWidth = s.rotWidth
  maxWidth : t.maxWidth = s.maxWidth
  input : t.input = s.input
  output : t.output = s.output
  outClosed : t.outClosed = s.outClosed

private theorem Segment.trans {m n : Nat} {s u t : State}
    (h : Segment m s u) (h' : Segment n u t) : Segment (m + n) s t := by
  refine ⟨?_,h'.context,fun x hx => (h'.frame x hx).trans (h.frame x hx),
    h'.acc.trans h.acc,h'.width.trans h.width,h'.maxWidth.trans h.maxWidth,
    h'.input.trans h.input,h'.output.trans h.output,h'.outClosed.trans h.outClosed⟩
  rw [run?_add,h.run,Option.bind_some,h'.run]

private theorem successor_iterate (d n : Nat) :
    (Value.succ^[n]) (Value.ofNat d) = Value.ofNat (d + n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',ih,succ_ofNat,Nat.add_assoc]

set_option maxHeartbeats 1000000 in
private theorem nops_run {s : State} {A D n : Nat} (h : Context s.mem)
    (hc : s.c = Value.ofNat A) (hd : s.d = Value.ofNat D)
    (hblock : ∀ i < n, A + i ∈ noops) :
    ∃ t, Segment n s t ∧ t.c = Value.ofNat (A + n) ∧ t.d = Value.ofNat (D + n) := by
  have hv : ∀ i : Fin n, ∃ k, k ∈ orbit (A + i.val) ∧
      s.mem.get (Value.ofNat (A + i.val)) = Value.ofNat k :=
    fun i => h.extras.nops _ (hblock i.val i.isLt)
  choose ks hks hvals using hv
  let codes (i : Nat) := if hi : i < n then ks ⟨i,hi⟩ else 74
  have hcodes (i : Fin n) : codes i.val = ks i := by simp [codes,i.isLt]
  obtain ⟨t,hr,ha,hc',hd',hvals',hf,hi,ho,hx,hw,hm⟩ :=
    nop_run n codes hc
      (fun i hi => by rw [hvals ⟨i,hi⟩]; exact (orbit_valid _ (hblock i hi) _ (hks ⟨i,hi⟩)).1)
      (fun i hi => by
        rw [hvals ⟨i,hi⟩,hcodes ⟨i,hi⟩]
        exact (orbit_valid _ (hblock i hi) _ (hks ⟨i,hi⟩)).2.1)
  have hframe : Frame bridgeWrites s.mem t.mem := by
    intro x hx
    exact hf x (fun i hi => hx _ (List.mem_append_right _ (hblock i hi)))
  have hn : Noops t.mem := by
    intro a hab
    by_cases hin : A ≤ a ∧ a < A + n
    · let i : Fin n := ⟨a - A,by omega⟩
      have he : A + i.val = a := by dsimp [i]; omega
      refine ⟨encrypt (ks i),(orbit_valid _ hab _ (by rw [← he]; exact hks i)).2.2,?_⟩
      simpa only [hcodes i,he] using hvals' i.val i.isLt
    · rw [hf _ (fun i hi => ofNat_ne (by omega))]
      exact h.extras.nops a hab
  have hl : ∀ a ∈ ([145,247,428] : List Nat), ∃ k, printableCode? (t.mem.get (Value.ofNat a)) = some k := by
    intro a hab
    have hd : ∀ a ∈ ([145,247,428] : List Nat), a ∉ noops := by unfold noops; decide
    rw [hf _ (fun i hi => ofNat_ne (by intro he; have := hblock i hi; rw [← he] at this; exact hd a hab this))]
    simp at hab
    rcases hab with rfl | rfl | rfl
    · exact h.extras.landing 145 (by decide)
    · exact h.reset.landing 247 (by decide)
    · exact h.extras.landing 428 (by decide)
  refine ⟨t,⟨hr,h.bridge_frame hframe hn hl,hframe,ha,hw,hm,hi,ho,hx⟩,hc',?_⟩
  rw [hd',hd,successor_iterate]

private theorem Context.printable {m : Memory} (h : Context m) {a : Nat}
    (ha : a ∈ ([145,247,428] : List Nat)) : ∃ k, printableCode? (m.get (Value.ofNat a)) = some k := by
  simp at ha
  rcases ha with rfl | rfl | rfl
  · exact h.extras.landing 145 (by decide)
  · exact h.reset.landing 247 (by decide)
  · exact h.extras.landing 428 (by decide)

private theorem Context.land_frame {m m' : Memory} {T : Nat} (h : Context m)
    (hT : T ∈ ([145,247,428] : List Nat))
    (hf : ∀ x, x ≠ Value.ofNat T → m'.get x = m.get x)
    (hp : ∃ k, printableCode? (m'.get (Value.ofNat T)) = some k) : Context m' := by
  apply h.bridge_frame (fun x hx => hf x (hx T (List.mem_append_left _ hT)))
  · intro a ha
    have hd : ∀ a ∈ noops, ∀ b ∈ ([145,247,428] : List Nat), a ≠ b := by unfold noops; decide
    obtain ⟨k,hk,hv⟩ := h.extras.nops a ha
    exact ⟨k,hk,by rw [hf _ (ofNat_ne (hd a ha T hT)),hv]⟩
  · intro a ha
    by_cases he : a = T
    · subst a; exact hp
    · rw [hf _ (ofNat_ne he)]; exact h.printable ha

private theorem land_jump {s : State} {C D T : Nat} (h : Context s.mem)
    (hc : s.c = Value.ofNat C) (hd : s.d = Value.ofNat D)
    (hj : decode (s.mem.get (Value.ofNat C)) (Value.ofNat C).modClass = .jmp)
    (hp : s.mem.get (Value.ofNat D) = Value.ofNat T)
    (hT : T ∈ ([145,247,428] : List Nat)) :
    ∃ t, Segment 1 s t ∧ t.c = Value.ofNat (T + 1) ∧ t.d = Value.ofNat (D + 1) := by
  obtain ⟨k,hk⟩ := h.printable hT
  let t : State := { s with
    mem := s.mem.set (Value.ofNat T) (Value.ofNat (encrypt k)),
    c := Value.ofNat (T + 1), d := Value.ofNat (D + 1) }
  have hr : step1 s = some t := jump hc hd hj hp hk
  have hf : ∀ x, x ≠ Value.ofNat T → t.mem.get x = s.mem.get x :=
    fun _ hx => get_set_ne _ hx.symm _
  refine ⟨t,⟨?_,h.land_frame hT hf ?_,?_,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl,rfl⟩
  · change (step1 s).bind some = _; rw [hr,Option.bind_some]
  · rw [show t.mem.get (Value.ofNat T) = Value.ofNat (encrypt k) from get_set_self _ _ _]
    exact printable_after hk
  · intro x hx; exact hf x (hx T (List.mem_append_left _ hT))

private theorem pointer_call {s : State} {D P T : Nat} (h : Context s.mem)
    (hc : s.c = Value.ofNat 248) (hd : s.d = Value.ofNat D)
    (hp : s.mem.get (Value.ofNat D) = Value.ofNat P)
    (hwidth : (Value.ofNat P).width ≤ s.maxWidth) (hP : 250 ≤ P)
    (hrestore : s.mem.get (Value.ofNat (P + 1)) = Value.ofNat 248)
    (hreturn : s.mem.get (Value.ofNat (P + 2)) = Value.ofNat T)
    (hT : T = 145 ∨ T = 428) :
    ∃ t, Segment 3 s t ∧ t.c = Value.ofNat (T + 1) ∧ t.d = Value.ofNat (P + 3) := by
  have hT' : T ∈ ([145,247,428] : List Nat) := by simp; omega
  obtain ⟨k,hk⟩ := h.printable hT'
  obtain ⟨t,hr,ha,hc',hd',hv,_,_,hf,hi,ho,hx,hw,hm⟩ :=
    movd_call hc (by rw [hd]; exact hp) hwidth hP (by omega) (by omega)
      (h.reset.static 248 (Value.ofNat 74) (by decide)) (by decide)
      (by rw [h.reset.static 249 (Value.ofNat 37) (by decide)]; decide)
      hrestore hreturn hk
  refine ⟨t,⟨hr,h.land_frame hT' hf ?_,?_,ha,hw,hm,hi,ho,hx⟩,hc',hd'⟩
  · rw [hv]; exact printable_after hk
  · intro x hx; exact hf x (hx T (List.mem_append_left _ hT'))

/-- Fifteen real steps deliver the rotated marker to the growth service. -/
theorem enter_growth {s : State} (h : Context s.mem)
    (hc : s.c = Value.ofNat 1400) (hd : s.d = Value.ofNat 3000) (hm : 8 ≤ s.maxWidth) :
    ∃ t, Segment 15 s t ∧ t.c = Value.ofNat 436 ∧ t.d = Value.ofNat 3200 := by
  obtain ⟨u,hu,hcu,hdu⟩ := nops_run (n := 4) h hc hd
    (by intro i hi; simp [noops]; omega)
  obtain ⟨v,hv,hcv,hdv⟩ := land_jump (T := 247) hu.context hcu hdu
    (by rw [hu.context.extras.static 1404 104 (by decide)]; decide)
    (hu.context.extras.static 3004 247 (by decide)) (by decide)
  have hb : (Value.ofNat 3190).width ≤ v.maxWidth := by
    rw [hv.maxWidth,hu.maxWidth]; exact hm
  obtain ⟨z,hz,hcz,hdz⟩ := pointer_call (P := 3190) (T := 428) hv.context hcv hdv
    (hv.context.extras.static 3005 3190 (by decide)) hb (by decide)
    (hv.context.extras.static 3191 248 (by decide))
    (hv.context.extras.static 3192 428 (by decide)) (Or.inr rfl)
  obtain ⟨t,ht,hct,hdt⟩ := nops_run (n := 7) hz.context hcz hdz
    (by intro i hi; simp [noops]; omega)
  exact ⟨t,hu.trans (hv.trans (hz.trans ht)),hct,hdt⟩

/-- Eleven real steps return from growth to reset without changing the
wide marker. Reset will subsequently regenerate one at the new width. -/
theorem leave_growth {s : State} (h : Context s.mem)
    (hc : s.c = Value.ofNat 1200) (hd : s.d = Value.ofNat 5008) (hm : 8 ≤ s.maxWidth) :
    ∃ t, Segment 11 s t ∧ t.c = Value.ofNat 153 ∧ t.d = Value.ofNat 3000 := by
  obtain ⟨u,hu,hcu,hdu⟩ := land_jump (T := 247) h hc hd
    (by rw [h.extras.static 1200 120 (by decide)]; decide)
    (h.extras.static 5008 247 (by decide)) (by decide)
  have hb : (Value.ofNat 2990).width ≤ u.maxWidth := by rw [hu.maxWidth]; exact hm
  obtain ⟨v,hv,hcv,hdv⟩ := pointer_call (P := 2990) (T := 145) hu.context hcu hdu
    (hu.context.extras.static 5009 2990 (by decide)) hb (by decide)
    (hu.context.extras.static 2991 248 (by decide))
    (hu.context.extras.static 2992 145 (by decide)) (Or.inl rfl)
  obtain ⟨t,ht,hct,hdt⟩ := nops_run (n := 7) hv.context hcv hdv
    (by intro i hi; simp [noops]; omega)
  exact ⟨t,hu.trans (hv.trans ht),hct,hdt⟩

private theorem reset_memory_frame {writes : List Nat} {m m' : Memory}
    (h : MarkerReset.Resident m) (hf : Frame writes m m')
    (hc : ∀ e ∈ MarkerReset.cells, e.1 ∉ writes)
    (hl : ∀ a ∈ MarkerReset.landings, a ∉ writes) : MarkerReset.Resident m' := by
  constructor
  · intro a v ha; rw [frame_read hf (hc (a,v) ha)]; exact h.static a v ha
  · intro a ha; rw [frame_read hf (hl a ha)]; exact h.landing a ha

private theorem links_frame {writes : List Nat} {m m' : Memory}
    (h : MarkerCycle.Links m 1399) (hf : Frame writes m m')
    (hc : ∀ e ∈ MarkerCycle.cells 1399, e.1 ∉ writes)
    (hl : ∀ a ∈ MarkerCycle.landings 1399, a ∉ writes)
    (hn : ∀ a ∈ MarkerCycle.noops, a ∉ writes) : MarkerCycle.Links m' 1399 := by
  constructor
  · intro a v ha; rw [frame_read hf (hc (a,v) ha)]; exact h.static a v ha
  · intro a ha; rw [frame_read hf (hl a ha)]; exact h.landing a ha
  · intro a ha
    obtain ⟨k,hk,hv⟩ := h.nops a ha
    exact ⟨k,hk,by rw [frame_read hf (hn a ha),hv]⟩

private theorem Context.cycle_frame {n : Nat} {s t : State} (h : Context s.mem)
    (hs : MarkerCycle.Segment n s t 1399) (hr : MarkerReset.Resident t.mem)
    (hl : MarkerCycle.Links t.mem 1399)
    (hrot : t.mem.get (Value.ofNat 529) = Value.ofNat 74)
    (hroute : t.mem.get (Value.ofNat 530) = Value.ofNat 74) : Context t.mem := by
  refine ⟨hr,hl,?_,?_,hrot,hroute⟩
  · exact growth_frame h.growth hs.frame (by decide) (by decide)
  · exact extras_frame h.extras hs.frame (by decide) (by decide) (by decide)

def resetWrites : List Nat := [3200,530,247,269,529,1299]
def growthWrites : List Nat := [1199,437,438,439]

private theorem reset_run_frame {n : Nat} {s t : State} (h : MarkerReset.Segment n s t) :
    Frame resetWrites s.mem t.mem := by
  intro x hx
  apply h.frame x
  refine ⟨hx 3200 (by decide),hx 530 (by decide),?_⟩
  intro a ha
  have hh : ∀ a ∈ MarkerReset.landings, a ∈ resetWrites := by decide
  exact hx a (hh a ha)

private theorem Context.reset_frame {n : Nat} {s t : State} (h : Context s.mem)
    (hs : MarkerReset.Segment n s t) (hr : MarkerReset.Resident t.mem)
    (hrot : t.mem.get (Value.ofNat 529) = Value.ofNat 74)
    (hroute : t.mem.get (Value.ofNat 530) = Value.ofNat 74) : Context t.mem := by
  refine ⟨hr,h.links.reset_frame (Or.inr rfl) hs,?_,?_,hrot,hroute⟩
  · exact growth_frame h.growth (reset_run_frame hs) (by decide) (by decide)
  · exact extras_frame h.extras (reset_run_frame hs) (by decide) (by decide) (by decide)

private theorem Context.growth_frame {m m' : Memory} (h : Context m)
    (hf : Frame growthWrites m m') (hg : ReusableGrowth.Resident m') : Context m' := by
  refine ⟨?_,?_,hg,?_,?_,?_⟩
  · exact reset_memory_frame h.reset hf (by decide) (by decide)
  · exact links_frame h.links hf (by decide) (by decide) (by decide)
  · exact extras_frame h.extras hf (by decide) (by decide) (by decide)
  · rw [frame_read hf (by decide)]; exact h.rotor
  · rw [frame_read hf (by decide)]; exact h.router

/-- The finite footprint of a complete growth cycle. All counter cells
outside it and all later distant return reads are preserved. -/
def writes : List Nat := MarkerCycle.changed 1399 ++ bridgeWrites ++ resetWrites ++ growthWrites

structure Trace (n : Nat) (s t : State) : Prop where
  run : run? n s = some t
  frame : Frame writes s.mem t.mem
  input : t.input = s.input
  output : t.output = s.output
  outClosed : t.outClosed = s.outClosed

private theorem Trace.trans {m n : Nat} {s u t : State} (h : Trace m s u) (h' : Trace n u t) :
    Trace (m + n) s t := by
  refine ⟨?_,fun x hx => (h'.frame x hx).trans (h.frame x hx),
    h'.input.trans h.input,h'.output.trans h.output,h'.outClosed.trans h.outClosed⟩
  rw [run?_add,h.run,Option.bind_some,h'.run]

private theorem trace_of {n : Nat} {s t : State} {footprint : List Nat}
    (hr : run? n s = some t) (hf : Frame footprint s.mem t.mem)
    (hi : t.input = s.input) (ho : t.output = s.output) (hx : t.outClosed = s.outClosed)
    (hsub : ∀ a ∈ footprint, a ∈ writes) : Trace n s t :=
  ⟨hr,fun x hx => hf x (fun a ha => hx a (hsub a ha)),hi,ho,hx⟩

private theorem trace_bridge {n : Nat} {s t : State} (h : Segment n s t) : Trace n s t :=
  trace_of h.run h.frame h.input h.output h.outClosed (by decide)

private theorem trace_cycle {n : Nat} {s t : State} (h : MarkerCycle.Segment n s t 1399) : Trace n s t :=
  trace_of h.run h.frame h.input h.output h.outClosed (by decide)

private theorem trace_reset {n : Nat} {s t : State} (h : MarkerReset.Segment n s t) : Trace n s t :=
  trace_of h.run (reset_run_frame h) h.input h.output h.outClosed (by decide)

structure Ready (w : Nat) (s : State) : Prop where
  context : Context s.mem
  code : s.c = Value.ofNat 529
  data : s.d = Value.ofNat 3200
  acc : s.a = Value.ofNat 1
  marker : s.mem.get (Value.ofNat 3200) = Value.ofNat 1
  width : s.rotWidth = w
  bound : 8 ≤ s.maxWidth
  room : s.maxWidth < w
  minimum : 10 ≤ w

private theorem Ready.resetAt {s : State} {w : Nat} (h : Ready w s) :
    MarkerReset.At w (Value.ofNat 1) (Value.ofNat 1) false 529 3200 s :=
  ⟨h.context.reset,h.code,h.data,h.acc,h.width,h.bound,h.marker,h.context.router⟩

/-- Eighty-seven actual instructions double the width, regenerate the same
marker, and return with every resident service callable again. -/
theorem cycle {s : State} {w : Nat} (h : Ready w s) :
    ∃ t, Trace 87 s t ∧ Ready (2 * w) t ∧ t.maxWidth = w := by
  obtain ⟨u,hu,hua,hul,hur⟩ := MarkerCycle.rotate_to h.resetAt h.context.links (Or.inr rfl) h.context.rotor
  have huc := h.context.cycle_frame hu hua.resident hul hur hua.router
  obtain ⟨g,hg,hgc,hgd⟩ := enter_growth huc hua.code hua.data hua.bound
  have hgw : g.rotWidth = w := hg.width.trans hua.width
  have hgm : g.maxWidth < w := by rw [hg.maxWidth,hu.maxWidth]; exact h.room
  have hgv : g.mem.get g.d = Value.rot w (Value.ofNat 1) := by
    rw [hgd,frame_read hg.frame (by decide),hua.marker]
  obtain ⟨v,hvrun,hvc,hvd,hvw,hvm,hva,hvg,hvf,hvi,hvo,hvx⟩ :=
    ReusableGrowth.call_resident hg.context.growth hgc hgw h.minimum hgm hgv
  have hvframe : Frame growthWrites g.mem v.mem := by
    intro x hx
    apply hvf x (hx 1199 (by decide))
    intro i
    have hb : 437 + i.val ∈ growthWrites := by have := i.isLt; simp [growthWrites]; omega
    exact hx _ hb
  have hvcx := hg.context.growth_frame hvframe hvg
  have hvbound : 8 ≤ v.maxWidth := by rw [hvm]; have := h.minimum; omega
  obtain ⟨z,hz,hzc,hzd⟩ := leave_growth hvcx hvc hvd hvbound
  have hzw : z.rotWidth = 2 * w := hz.width.trans hvw
  have hzm : z.maxWidth = w := hz.maxWidth.trans hvm
  have hzv : z.mem.get (Value.ofNat 3200) = Value.rot w (Value.ofNat 1) := by
    rw [frame_read hz.frame (by decide),frame_read hvframe (by decide),← hgd]
    exact hgv
  have hza : MarkerReset.At (2 * w) z.a (Value.rot w (Value.ofNat 1)) false 153 3000 z :=
    ⟨hz.context.reset,hzc,hzd,rfl,hzw,by rw [hzm]; have := h.minimum; omega,hzv,hz.context.router⟩
  have hp : Marker.ZeroOne (Value.rot w (Value.ofNat 1)) := by
    rw [rot_one w (by have := h.minimum; omega)]
    exact Marker.zeroOne_power (w - 1)
  obtain ⟨r,hr,hra,hrr⟩ := MarkerReset.call_rotator hza hp hz.context.rotor
  have hrc := hz.context.reset_frame hr hra.resident hrr hra.router
  obtain ⟨t,ht,hta,htl,htr⟩ := MarkerCycle.return_route hra hrc.links (Or.inr rfl) hrc.rotor
  have htc := hrc.cycle_frame ht hta.resident htl htr hta.router
  have htm : t.maxWidth = w := ht.maxWidth.trans (hr.maxWidth.trans hzm)
  refine ⟨t,?_,⟨htc,hta.code,hta.data,hta.acc,hta.marker,hta.width,hta.bound,?_,?_⟩,htm⟩
  · exact (trace_cycle hu).trans ((trace_bridge hg).trans
      ((trace_of hvrun hvframe hvi hvo hvx (by decide)).trans
      ((trace_bridge hz).trans ((trace_reset hr).trans (trace_cycle ht)))))
  · rw [htm]; have := h.minimum; omega
  · have := h.minimum; omega

/-- One finite program supports arbitrarily many doublings. -/
theorem repeat_cycles {s : State} {w : Nat} (h : Ready w s) (n : Nat) :
    ∃ t, Trace (87 * n) s t ∧ Ready (2 ^ n * w) t := by
  induction n with
  | zero => exact ⟨s,⟨rfl,fun _ _ => rfl,rfl,rfl,rfl⟩,by simpa using h⟩
  | succ n ih =>
    obtain ⟨u,hu,hur⟩ := ih
    obtain ⟨t,ht,htr,_⟩ := cycle hur
    refine ⟨t,by simpa only [Nat.mul_succ] using hu.trans ht,?_⟩
    simpa only [Nat.pow_succ,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using htr

/-- No finite fuel prefix halts or errors. There is no exit test in this
unconditional growth demonstration. -/
theorem neverHalts {s : State} {w : Nat} (h : Ready w s) (fuel : Nat) :
    (exec fuel s).2 = .outOfFuel := by
  obtain ⟨t,ht,_⟩ := repeat_cycles h (fuel + 1)
  have he : 87 * (fuel + 1) = fuel + (87 * (fuel + 1) - fuel) := by omega
  have hr := ht.run
  rw [he,run?_add] at hr
  cases hp : run? fuel s with
  | none => simp [hp] at hr
  | some u => rw [exec_of_run? hp]

/-- Actual runs reach widths above any prescribed bound. This is an
unbounded-resource result, not a universality theorem. -/
theorem unbounded_width {s : State} {w : Nat} (h : Ready w s) (bound : Nat) :
    ∃ n t, run? (87 * n) s = some t ∧ bound ≤ t.rotWidth := by
  have hp : ∀ n : Nat, n ≤ 2 ^ n := by
    intro n
    induction n with
    | zero => decide
    | succ n ih =>
      rw [Nat.pow_succ]
      have hh : 0 < 2 ^ n := Nat.pow_pos (by decide)
      omega
  obtain ⟨t,ht,htr⟩ := repeat_cycles h bound
  refine ⟨bound,t,ht.run,?_⟩
  rw [htr.width]
  have hm := Nat.mul_le_mul_left (2 ^ bound) (show 1 ≤ w by have := h.minimum; omega)
  simpa only [Nat.mul_one] using (hp bound).trans (by simpa only [Nat.mul_one] using hm)

/-- The larger initializer still ends below every permitted remote read.
The penultimate seed address is 12004, with the correct phase modulo six. -/
theorem returns_of_fill {m : Memory}
    (hrest : m.rest = restTable (Value.ofNat 5001) (Value.ofNat 5001) 12004)
    (hfinite : ∀ n, 12006 ≤ n → ¬ m.cells.contains (Value.ofNat n)) :
    ReusableGrowth.Returns m := by
  intro w hw
  rw [get_of_not_mem (hfinite _ (by have := distant_bound hw; omega)),growth_fill m (by omega),hrest]
  decide

/-- Distinct natural-operand synthesis pairs used by the finite startup. -/
def initializerPairs : List (Nat × Nat × Nat × Nat) :=
  [(0,6561,6635,74),
   (74,6567,6569,41),
   (41,6567,6635,74),
   (74,6561,6635,74),
   (74,6751,6729,96),
   (96,6561,6579,102),
   (102,6777,6617,41),
   (41,6561,6563,41)]

/-- The startup's finite arithmetic identities. The complete source-to-Ready
composition is tested by execution, not assumed by the cycle theorem. -/
theorem initializer_values :
    (∀ p ∈ initializerPairs,
      Value.crz (Value.crz (Value.ofNat p.1) (Value.ofNat p.2.1)) (Value.ofNat p.2.2.1) =
        Value.ofNat p.2.2.2) ∧
    Value.crz (Value.ofNat 74) (Value.ofNat 317) = Marker.ones ∧
    Value.crz (Value.crz Marker.ones (Value.ofNat 243)) (Value.ofNat 243) = Marker.ones ∧
    Value.crz (Value.crz Marker.ones (Value.ofNat 245)) (Value.ofNat 243) = Marker.mask := by
  decide

end Langlib.Computability.Unshackled.Runtime.GrowingMarker
