import Langlib.Common.Fuel
import Langlib.Computability.Class
import Langlib.Computability.URM
import Langlib.Languages.Brainfuck

/-!
# Brainfuck is Turing complete

This file compiles an arbitrary unlimited register machine into brainfuck and
proves the simulation, giving `brainfuckComplete : TuringComplete
BrainfuckLang`.

See `docs/computability-brainfuck.md` for the prose account.
-/

namespace Langlib.Computability.URMBrainfuck

open Langlib.Common

/-! ## The counter language

The proof goes through an intermediate language rather than compiling the URM
straight onto the tape. `Cmd` is a register machine with *structured* control:
increment, decrement, emit one output byte, and `loop r b`, which runs `b`
while register `r` is nonzero. It is the machine a brainfuck tape actually
implements, so the second half of the compiler is compositional, and it is a
register machine, so the first half is ordinary arithmetic on `Nat → Nat` with
no tape in sight.

`dec` on a zero register has no rule: the semantics below is a big-step
relation, and a program that decrements a zero register simply has no
derivation. That is exactly the discipline the brainfuck code needs, because
the code emitted for `dec` walks one cell down a unary run and would step onto
the guard row if the run were empty. -/

/-- A counter-machine command. -/
inductive Cmd where
  /-- Increment register `r`. -/
  | inc (r : Nat)
  /-- Decrement register `r`; undefined when `r` holds zero. -/
  | dec (r : Nat)
  /-- Append one byte to the output. -/
  | emit
  /-- While register `r` is nonzero, run `body`. -/
  | loop (r : Nat) (body : List Cmd)
deriving Repr, Inhabited

/-- A counter-machine program. -/
abbrev Code := List Cmd

/-- Registers plus a count of the bytes emitted so far. Only the number of
output bytes matters, because every byte the compiled program emits has the
same value. -/
structure CState where
  regs : Nat → Nat
  out : Nat

namespace CState

def up (s : CState) (r : Nat) : CState :=
  { s with regs := Function.update s.regs r (s.regs r + 1) }

def down (s : CState) (r : Nat) : CState :=
  { s with regs := Function.update s.regs r (s.regs r - 1) }

def emitOne (s : CState) : CState := { s with out := s.out + 1 }

@[simp] theorem up_regs_self (s : CState) (r : Nat) : (s.up r).regs r = s.regs r + 1 := by
  simp [up]

@[simp] theorem up_regs_of_ne (s : CState) {r k : Nat} (h : k ≠ r) :
    (s.up r).regs k = s.regs k := by
  simp [up, Function.update_of_ne h]

@[simp] theorem down_regs_self (s : CState) (r : Nat) : (s.down r).regs r = s.regs r - 1 := by
  simp [down]

@[simp] theorem down_regs_of_ne (s : CState) {r k : Nat} (h : k ≠ r) :
    (s.down r).regs k = s.regs k := by
  simp [down, Function.update_of_ne h]

@[simp] theorem up_out (s : CState) (r : Nat) : (s.up r).out = s.out := rfl
@[simp] theorem down_out (s : CState) (r : Nat) : (s.down r).out = s.out := rfl
@[simp] theorem emitOne_regs (s : CState) : s.emitOne.regs = s.regs := rfl
@[simp] theorem emitOne_out (s : CState) : s.emitOne.out = s.out + 1 := rfl

end CState

/-- Big-step semantics, in continuation-passing form so that it lines up one
for one with brainfuck's `exec`, which also carries the rest of the program as
a list. `R` bounds the register indices: a command mentioning a register at or
beyond `R` has no derivation, which is what keeps the tape layout (`R`
interleaved columns) able to hold every register the program touches. -/
inductive Ev (R : Nat) : Code → CState → CState → Prop where
  | nil {s : CState} : Ev R [] s s
  | inc {r : Nat} {cs : Code} {s t : CState} (h : r < R) :
      Ev R cs (s.up r) t → Ev R (Cmd.inc r :: cs) s t
  | dec {r : Nat} {cs : Code} {s t : CState} (h : r < R) (hnz : s.regs r ≠ 0) :
      Ev R cs (s.down r) t → Ev R (Cmd.dec r :: cs) s t
  | emit {cs : Code} {s t : CState} :
      Ev R cs s.emitOne t → Ev R (Cmd.emit :: cs) s t
  | loopZ {r : Nat} {b cs : Code} {s t : CState} (h : r < R) (hz : s.regs r = 0) :
      Ev R cs s t → Ev R (Cmd.loop r b :: cs) s t
  | loopS {r : Nat} {b cs : Code} {s t : CState} (h : r < R) (hnz : s.regs r ≠ 0) :
      Ev R (b ++ Cmd.loop r b :: cs) s t → Ev R (Cmd.loop r b :: cs) s t

/-- Sequential composition. -/
theorem Ev.append {R : Nat} {c₁ : Code} {s t : CState} (h₁ : Ev R c₁ s t) :
    ∀ {c₂ : Code} {u : CState}, Ev R c₂ t u → Ev R (c₁ ++ c₂) s u := by
  induction h₁ with
  | nil => intro c₂ u h; simpa using h
  | inc h _ ih => intro c₂ u h2; exact Ev.inc h (ih h2)
  | dec h hnz _ ih => intro c₂ u h2; exact Ev.dec h hnz (ih h2)
  | emit _ ih => intro c₂ u h2; exact Ev.emit (ih h2)
  | loopZ h hz _ ih => intro c₂ u h2; exact Ev.loopZ h hz (ih h2)
  | loopS h hnz _ ih =>
    intro c₂ u h2
    refine Ev.loopS h hnz ?_
    have hx := ih h2
    simpa [List.append_assoc] using hx

/-! ## Counter-machine macros

Each macro comes with a lemma of one shape: from any register file `w` it
produces a `w'`, gives the value of every register the macro writes, and says
that every other register is untouched. The frame condition is what makes the
dispatch chain below tractable. -/

/-- `a := 0`. -/
def clear (a : Nat) : Code := [Cmd.loop a [Cmd.dec a]]

theorem clear_spec {R a : Nat} (ha : a < R) :
    ∀ (v : Nat) (s : CState), s.regs a = v →
      ∃ w', Ev R (clear a) s ⟨w', s.out⟩ ∧ w' a = 0 ∧ ∀ r, r ≠ a → w' r = s.regs r := by
  intro v
  induction v with
  | zero =>
    intro s hs
    exact ⟨s.regs, Ev.loopZ ha hs Ev.nil, hs, fun _ _ => rfl⟩
  | succ v ih =>
    intro s hs
    have hnz : s.regs a ≠ 0 := by omega
    have hd : (s.down a).regs a = v := by simp [hs]
    obtain ⟨w', hev, h0, hfr⟩ := ih (s.down a) hd
    refine ⟨w', Ev.loopS ha hnz (Ev.dec ha hnz hev), h0, ?_⟩
    intro r hr
    rw [hfr r hr, CState.down_regs_of_ne s hr]

/-- `b := b + a; a := 0`. -/
def move (a b : Nat) : Code := [Cmd.loop a [Cmd.dec a, Cmd.inc b]]

theorem move_spec {R a b : Nat} (ha : a < R) (hb : b < R) (hab : a ≠ b) :
    ∀ (v : Nat) (s : CState), s.regs a = v →
      ∃ w', Ev R (move a b) s ⟨w', s.out⟩ ∧ w' a = 0 ∧ w' b = s.regs b + v ∧
        ∀ r, r ≠ a → r ≠ b → w' r = s.regs r := by
  intro v
  induction v with
  | zero =>
    intro s hs
    exact ⟨s.regs, Ev.loopZ ha hs Ev.nil, hs, by omega, fun _ _ _ => rfl⟩
  | succ v ih =>
    intro s hs
    have hnz : s.regs a ≠ 0 := by omega
    have hsa : ((s.down a).up b).regs a = v := by
      rw [CState.up_regs_of_ne _ hab, CState.down_regs_self, hs]
      omega
    have hsb : ((s.down a).up b).regs b = s.regs b + 1 := by
      rw [CState.up_regs_self, CState.down_regs_of_ne _ hab.symm]
    obtain ⟨w', hev, h0, hbv, hfr⟩ := ih ((s.down a).up b) hsa
    refine ⟨w', Ev.loopS ha hnz (Ev.dec ha hnz (Ev.inc hb hev)), h0, by omega, ?_⟩
    intro r hra hrb
    rw [hfr r hra hrb, CState.up_regs_of_ne _ hrb, CState.down_regs_of_ne _ hra]

/-- `b := b + a; c := c + a; a := 0`. -/
def move2 (a b c : Nat) : Code := [Cmd.loop a [Cmd.dec a, Cmd.inc b, Cmd.inc c]]

theorem move2_spec {R a b c : Nat} (ha : a < R) (hb : b < R) (hc : c < R)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∀ (v : Nat) (s : CState), s.regs a = v →
      ∃ w', Ev R (move2 a b c) s ⟨w', s.out⟩ ∧ w' a = 0 ∧ w' b = s.regs b + v ∧
        w' c = s.regs c + v ∧ ∀ r, r ≠ a → r ≠ b → r ≠ c → w' r = s.regs r := by
  intro v
  induction v with
  | zero =>
    intro s hs
    exact ⟨s.regs, Ev.loopZ ha hs Ev.nil, hs, by omega, by omega, fun _ _ _ _ => rfl⟩
  | succ v ih =>
    intro s hs
    have hnz : s.regs a ≠ 0 := by omega
    have hsa : (((s.down a).up b).up c).regs a = v := by
      rw [CState.up_regs_of_ne _ hac, CState.up_regs_of_ne _ hab,
        CState.down_regs_self, hs]
      omega
    have hsb : (((s.down a).up b).up c).regs b = s.regs b + 1 := by
      rw [CState.up_regs_of_ne _ hbc, CState.up_regs_self, CState.down_regs_of_ne _ hab.symm]
    have hsc : (((s.down a).up b).up c).regs c = s.regs c + 1 := by
      rw [CState.up_regs_self, CState.up_regs_of_ne _ hbc.symm, CState.down_regs_of_ne _ hac.symm]
    obtain ⟨w', hev, h0, hbv, hcv, hfr⟩ := ih (((s.down a).up b).up c) hsa
    refine ⟨w', Ev.loopS ha hnz (Ev.dec ha hnz (Ev.inc hb (Ev.inc hc hev))), h0,
      by omega, by omega, ?_⟩
    intro r hra hrb hrc
    rw [hfr r hra hrb hrc, CState.up_regs_of_ne _ hrc, CState.up_regs_of_ne _ hrb,
      CState.down_regs_of_ne _ hra]

/-- `b := a`, preserving `a` and clearing scratch `t`. -/
def copy (a b t : Nat) : Code :=
  clear b ++ clear t ++ move2 a b t ++ move t a

theorem copy_spec {R a b t : Nat} (ha : a < R) (hb : b < R) (ht : t < R)
    (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) (s : CState) :
    ∃ w', Ev R (copy a b t) s ⟨w', s.out⟩ ∧
      w' a = s.regs a ∧ w' b = s.regs a ∧ w' t = 0 ∧
      ∀ r, r ≠ a → r ≠ b → r ≠ t → w' r = s.regs r := by
  obtain ⟨w₁, h₁, h₁b, h₁fr⟩ := clear_spec hb (s.regs b) s rfl
  let s₁ : CState := ⟨w₁, s.out⟩
  obtain ⟨w₂, h₂, h₂t, h₂fr⟩ := clear_spec ht (s₁.regs t) s₁ rfl
  let s₂ : CState := ⟨w₂, s.out⟩
  have h₂a : w₂ a = s.regs a := by
    rw [h₂fr a hat]
    simpa [s₁] using h₁fr a hab
  have h₂b : w₂ b = 0 := by
    rw [h₂fr b hbt]
    simpa [s₁] using h₁b
  obtain ⟨w₃, h₃, h₃a, h₃b, h₃t, h₃fr⟩ :=
    move2_spec ha hb ht hab hat hbt (s₂.regs a) s₂ rfl
  let s₃ : CState := ⟨w₃, s.out⟩
  have h₃av : w₃ a = 0 := h₃a
  have h₃bv : w₃ b = s.regs a := by simpa [s₂, h₂b, h₂a] using h₃b
  have h₃tv : w₃ t = s.regs a := by simpa [s₂, h₂t, h₂a] using h₃t
  obtain ⟨w₄, h₄, h₄t, h₄a, h₄fr⟩ :=
    move_spec ht ha hat.symm (s₃.regs t) s₃ rfl
  refine ⟨w₄, ?_, ?_, ?_, h₄t, ?_⟩
  · unfold copy
    exact h₁.append (h₂.append (h₃.append (h₄.append Ev.nil)))
  · rw [h₄a]
    simp [s₃, h₃av, h₃tv]
  · rw [h₄fr b hbt hab.symm]
    simpa [s₃] using h₃bv
  · intro r hra hrb hrt
    rw [h₄fr r hrt hra]
    change w₃ r = s.regs r
    rw [h₃fr r hra hrb hrt]
    change w₂ r = s.regs r
    rw [h₂fr r hrt]
    simpa [s₁] using h₁fr r hrb

/-- Decrement `a` once when it is nonzero.  `gate` is left at one exactly
when `a` was zero; scratch `t` is cleared. -/
def decTest (a t gate : Nat) : Code :=
  [Cmd.inc gate,
    Cmd.loop a ([Cmd.dec a] ++ move a t ++ clear gate)] ++ move t a

theorem decTest_spec {R a t gate : Nat} (ha : a < R) (ht : t < R)
    (hg : gate < R) (hat : a ≠ t) (hag : a ≠ gate) (htg : t ≠ gate)
    (s : CState) (ht₀ : s.regs t = 0) (hg₀ : s.regs gate = 0) :
    ∃ w', Ev R (decTest a t gate) s ⟨w', s.out⟩ ∧
      w' a = s.regs a - 1 ∧ w' t = 0 ∧
      w' gate = (if s.regs a = 0 then 1 else 0) ∧
      ∀ r, r ≠ a → r ≠ t → r ≠ gate → w' r = s.regs r := by
  let sG := s.up gate
  have hGa : sG.regs a = s.regs a := CState.up_regs_of_ne s hag
  have hGt : sG.regs t = 0 := by rw [CState.up_regs_of_ne s htg, ht₀]
  have hGg : sG.regs gate = 1 := by simp [sG, hg₀]
  by_cases hz : s.regs a = 0
  · have hloop : Ev R [Cmd.loop a ([Cmd.dec a] ++ move a t ++ clear gate)] sG sG :=
      Ev.loopZ ha (by rw [hGa, hz]) Ev.nil
    obtain ⟨w', hm, hmt, hma, hmfr⟩ := move_spec ht ha hat.symm (sG.regs t) sG rfl
    refine ⟨w', Ev.inc hg (hloop.append (hm.append Ev.nil)), ?_, hmt, ?_, ?_⟩
    · rw [hma, hGa, hGt, Nat.add_zero, hz]
    · rw [hmfr gate htg.symm hag.symm, hGg, if_pos hz]
    · intro r hra hrt hrg
      rw [hmfr r hrt hra, CState.up_regs_of_ne s hrg]
  · have hsnz : sG.regs a ≠ 0 := by rw [hGa]; exact hz
    let sD := sG.down a
    have hDa : sD.regs a = s.regs a - 1 := by simp [sD, hGa]
    have hDt : sD.regs t = 0 := by
      rw [CState.down_regs_of_ne sG (r := a) (k := t) hat.symm, hGt]
    have hDg : sD.regs gate = 1 := by
      rw [CState.down_regs_of_ne sG (r := a) (k := gate) hag.symm, hGg]
    obtain ⟨wM, hm, hmA, hmT, hmfr⟩ := move_spec ha ht hat (sD.regs a) sD rfl
    let sM : CState := ⟨wM, s.out⟩
    have hMA : sM.regs a = 0 := hmA
    have hMT : sM.regs t = s.regs a - 1 := by simpa [sM, hDt, hDa] using hmT
    have hMG : sM.regs gate = 1 := by
      change wM gate = 1
      rw [hmfr gate hag.symm htg.symm, hDg]
    obtain ⟨wC, hc, hcG, hcfr⟩ := clear_spec hg (sM.regs gate) sM rfl
    let sC : CState := ⟨wC, s.out⟩
    have hCA : sC.regs a = 0 := by
      change wC a = 0
      rw [hcfr a hag, hMA]
    have hCT : sC.regs t = s.regs a - 1 := by
      change wC t = _
      rw [hcfr t htg, hMT]
    have hCG : sC.regs gate = 0 := hcG
    have hloopZ : Ev R [Cmd.loop a ([Cmd.dec a] ++ move a t ++ clear gate)] sC sC :=
      Ev.loopZ ha hCA Ev.nil
    obtain ⟨wF, hf, hfT, hfA, hffr⟩ := move_spec ht ha hat.symm (sC.regs t) sC rfl
    refine ⟨wF, ?_, ?_, hfT, ?_, ?_⟩
    · refine Ev.inc hg (Ev.loopS ha hsnz ?_)
      exact Ev.dec ha hsnz (hm.append (hc.append (hloopZ.append (hf.append Ev.nil))))
    · rw [hfA, hCA, hCT, Nat.zero_add]
    · rw [hffr gate htg.symm hag.symm, hCG, if_neg hz]
    · intro r hra hrt hrg
      rw [hffr r hrt hra]
      change wC r = s.regs r
      rw [hcfr r hrg]
      change wM r = s.regs r
      rw [hmfr r hra hrt]
      rw [CState.down_regs_of_ne sG (r := a) (k := r) hra,
        CState.up_regs_of_ne s hrg]

/-- If the zero-test gate is one, consume it and clear `eq` and `x`.  If the
gate is zero, leave all three registers alone. -/
def failWhen (gate eq x : Nat) : Code :=
  [Cmd.loop gate ([Cmd.dec gate] ++ clear eq ++ clear x)]

theorem failWhen_spec {R gate eq x : Nat} (hg : gate < R) (he : eq < R)
    (hx : x < R) (hge : gate ≠ eq) (hgx : gate ≠ x) (hex : eq ≠ x)
    (s : CState) (hgate : s.regs gate = 0 ∨ s.regs gate = 1) :
    ∃ w', Ev R (failWhen gate eq x) s ⟨w', s.out⟩ ∧ w' gate = 0 ∧
      w' eq = (if s.regs gate = 0 then s.regs eq else 0) ∧
      w' x = (if s.regs gate = 0 then s.regs x else 0) ∧
      ∀ r, r ≠ gate → r ≠ eq → r ≠ x → w' r = s.regs r := by
  rcases hgate with hzero | hone
  · exact ⟨s.regs, Ev.loopZ hg hzero Ev.nil, hzero, by simp [hzero],
      by simp [hzero], fun _ _ _ _ => rfl⟩
  · have hnz : s.regs gate ≠ 0 := by omega
    let sD := s.down gate
    have hDg : sD.regs gate = 0 := by simp [sD, hone]
    have hDe : sD.regs eq = s.regs eq :=
      CState.down_regs_of_ne s hge.symm
    have hDx : sD.regs x = s.regs x :=
      CState.down_regs_of_ne s hgx.symm
    obtain ⟨wE, hE, hEe, hEfr⟩ := clear_spec he (sD.regs eq) sD rfl
    let sE : CState := ⟨wE, s.out⟩
    have hEg : sE.regs gate = 0 := by
      change wE gate = 0
      rw [hEfr gate hge, hDg]
    have hEx : sE.regs x = s.regs x := by
      change wE x = s.regs x
      rw [hEfr x hex.symm, hDx]
    obtain ⟨wX, hX, hXx, hXfr⟩ := clear_spec hx (sE.regs x) sE rfl
    let sX : CState := ⟨wX, s.out⟩
    have hXg : sX.regs gate = 0 := by
      change wX gate = 0
      rw [hXfr gate hgx, hEg]
    have hXe : sX.regs eq = 0 := by
      change wX eq = 0
      rw [hXfr eq hex]
      simpa [sE] using hEe
    have hloopZ : Ev R (failWhen gate eq x) sX sX := Ev.loopZ hg hXg Ev.nil
    refine ⟨wX, Ev.loopS hg hnz (Ev.dec hg hnz
      (hE.append (hX.append hloopZ))), hXg, ?_, ?_, ?_⟩
    · simpa [sX, if_neg hnz] using hXe
    · rw [hXx, if_neg hnz]
    · intro r hrg hre hrx
      rw [hXfr r hrx]
      change wE r = s.regs r
      rw [hEfr r hre]
      exact CState.down_regs_of_ne s hrg

/-- Destructively compare `x` and `y`.  The input flag `eq` must be one;
it is one at the end exactly when the two inputs were equal. -/
def compareLoop (x y tmp gate eq : Nat) : Code :=
  [Cmd.loop x
    ([Cmd.dec x] ++ decTest y tmp gate ++ failWhen gate eq x)] ++
  [Cmd.loop y (clear y ++ clear eq)]

/-- Clear `a` and `b` when `a` is nonzero; otherwise leave both alone. -/
def clearPairWhen (a b : Nat) : Code := [Cmd.loop a (clear a ++ clear b)]

theorem clearPairWhen_spec {R a b : Nat} (ha : a < R) (hb : b < R)
    (hab : a ≠ b) (s : CState) :
    ∃ w', Ev R (clearPairWhen a b) s ⟨w', s.out⟩ ∧ w' a = 0 ∧
      w' b = (if s.regs a = 0 then s.regs b else 0) ∧
      ∀ r, r ≠ a → r ≠ b → w' r = s.regs r := by
  by_cases hz : s.regs a = 0
  · exact ⟨s.regs, Ev.loopZ ha hz Ev.nil, hz, by simp [hz], fun _ _ _ => rfl⟩
  · obtain ⟨w₁, h₁, h₁a, h₁fr⟩ := clear_spec ha (s.regs a) s rfl
    let s₁ : CState := ⟨w₁, s.out⟩
    have h₁b : s₁.regs b = s.regs b := by
      change w₁ b = s.regs b
      exact h₁fr b hab.symm
    obtain ⟨w₂, h₂, h₂b, h₂fr⟩ := clear_spec hb (s₁.regs b) s₁ rfl
    let s₂ : CState := ⟨w₂, s.out⟩
    have h₂a : s₂.regs a = 0 := by
      change w₂ a = 0
      rw [h₂fr a hab]
      simpa [s₁] using h₁a
    have hloopZ : Ev R (clearPairWhen a b) s₂ s₂ := Ev.loopZ ha h₂a Ev.nil
    refine ⟨w₂, Ev.loopS ha hz (h₁.append (h₂.append hloopZ)), h₂a, ?_, ?_⟩
    · rw [h₂b, if_neg hz]
    · intro r hra hrb
      rw [h₂fr r hrb]
      simpa [s₁] using h₁fr r hra

/-- Pairwise distinctness for the five registers used by comparison. -/
def Distinct5 (a b c d e : Nat) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ b ≠ c ∧ b ≠ d ∧ b ≠ e ∧
    c ≠ d ∧ c ≠ e ∧ d ≠ e

theorem compareLoop_spec {R x y tmp gate eq : Nat}
    (hx : x < R) (hy : y < R) (ht : tmp < R) (hg : gate < R) (he : eq < R)
    (hd : Distinct5 x y tmp gate eq) :
    ∀ (v : Nat) (s : CState), s.regs x = v → s.regs tmp = 0 →
      s.regs gate = 0 → s.regs eq = 1 →
      ∃ w', Ev R (compareLoop x y tmp gate eq) s ⟨w', s.out⟩ ∧
        w' x = 0 ∧ w' y = 0 ∧ w' tmp = 0 ∧ w' gate = 0 ∧
        w' eq = (if s.regs x = s.regs y then 1 else 0) ∧
        ∀ r, r ≠ x → r ≠ y → r ≠ tmp → r ≠ gate → r ≠ eq →
          w' r = s.regs r := by
  rcases hd with ⟨hxy, hxt, hxg, hxe, hyt, hyg, hye, htg, hte, hge⟩
  intro v
  induction v with
  | zero =>
    intro s hsx hst hsg hse
    obtain ⟨w', hclear, hwy, hwe, hwfr⟩ :=
      clearPairWhen_spec hy he hye s
    have hwx : w' x = 0 := by rw [hwfr x hxy hxe, hsx]
    have hwt : w' tmp = 0 := by rw [hwfr tmp hyt.symm hte, hst]
    have hwg : w' gate = 0 := by rw [hwfr gate hyg.symm hge, hsg]
    refine ⟨w', Ev.loopZ hx hsx hclear, hwx, hwy, hwt, hwg, ?_, ?_⟩
    · simpa [hsx, hse, eq_comm] using hwe
    · intro r hrx hry hrt hrg hre
      exact hwfr r hry hre
  | succ v ih =>
    intro s hsx hst hsg hse
    have hxnz : s.regs x ≠ 0 := by omega
    let sD := s.down x
    have hDx : sD.regs x = v := by simp [sD, hsx]
    have hDy : sD.regs y = s.regs y := CState.down_regs_of_ne s hxy.symm
    have hDt : sD.regs tmp = 0 := by
      rw [CState.down_regs_of_ne s hxt.symm, hst]
    have hDg : sD.regs gate = 0 := by
      rw [CState.down_regs_of_ne s hxg.symm, hsg]
    have hDe : sD.regs eq = 1 := by
      rw [CState.down_regs_of_ne s hxe.symm, hse]
    obtain ⟨wT, hT, hTy, hTt, hTg, hTfr⟩ :=
      decTest_spec hy ht hg hyt hyg htg sD hDt hDg
    let sT : CState := ⟨wT, s.out⟩
    have hTx : sT.regs x = v := by
      change wT x = v
      rw [hTfr x hxy hxt hxg, hDx]
    have hTe : sT.regs eq = 1 := by
      change wT eq = 1
      rw [hTfr eq hye.symm hte.symm hge.symm, hDe]
    have hTgate : sT.regs gate = 0 ∨ sT.regs gate = 1 := by
      change wT gate = 0 ∨ wT gate = 1
      rw [hTg]
      split <;> simp
    obtain ⟨wF, hF, hFg, hFe, hFx, hFfr⟩ :=
      failWhen_spec hg he hx hge hxg.symm hxe.symm sT hTgate
    let sF : CState := ⟨wF, s.out⟩
    have hFt : sF.regs tmp = 0 := by
      change wF tmp = 0
      rw [hFfr tmp htg hte hxt.symm]
      simpa [sT] using hTt
    have hFy : sF.regs y = s.regs y - 1 := by
      change wF y = s.regs y - 1
      rw [hFfr y hyg hye hxy.symm]
      simpa [sT, hDy] using hTy
    by_cases hsy : s.regs y = 0
    · have hTgOne : sT.regs gate = 1 := by
        change wT gate = 1
        rw [hTg, hDy, if_pos hsy]
      have hFxZero : sF.regs x = 0 := by
        change wF x = 0
        rw [hFx, if_neg (by omega : sT.regs gate ≠ 0)]
      have hFeZero : sF.regs eq = 0 := by
        change wF eq = 0
        rw [hFe, if_neg (by omega : sT.regs gate ≠ 0)]
      have hFyZero : sF.regs y = 0 := by rw [hFy, hsy]
      have hrest : Ev R (compareLoop x y tmp gate eq) sF sF :=
        Ev.loopZ hx hFxZero (Ev.loopZ hy hFyZero Ev.nil)
      refine ⟨wF, ?_, hFxZero, hFyZero, hFt, hFg, ?_, ?_⟩
      · refine Ev.loopS hx hxnz ?_
        exact Ev.dec hx hxnz (hT.append (hF.append hrest))
      · rw [show wF eq = 0 by simpa [sF] using hFeZero, hsx, hsy]
        simp
      · intro r hrx hry hrt hrg hre
        rw [hFfr r hrg hre hrx]
        change wT r = s.regs r
        rw [hTfr r hry hrt hrg]
        exact CState.down_regs_of_ne s hrx

    · obtain ⟨yv, hsyv⟩ := Nat.exists_eq_succ_of_ne_zero hsy
      have hTgZero : sT.regs gate = 0 := by
        change wT gate = 0
        rw [hTg, hDy, if_neg hsy]
      have hFxV : sF.regs x = v := by
        change wF x = v
        rw [hFx, if_pos hTgZero, hTx]
      have hFeOne : sF.regs eq = 1 := by
        change wF eq = 1
        rw [hFe, if_pos hTgZero, hTe]
      obtain ⟨w', hrec, hwx, hwy, hwt, hwg, hweq, hwfr⟩ :=
        ih sF hFxV hFt hFg hFeOne
      refine ⟨w', ?_, hwx, hwy, hwt, hwg, ?_, ?_⟩
      · refine Ev.loopS hx hxnz ?_
        exact Ev.dec hx hxnz (hT.append (hF.append hrec))
      · rw [hweq, hsx, hFxV, hFy, hsyv]
        simp
      · intro r hrx hry hrt hrg hre
        rw [hwfr r hrx hry hrt hrg hre]
        change wF r = s.regs r
        rw [hFfr r hrg hre hrx]
        change wT r = s.regs r
        rw [hTfr r hry hrt hrg]
        exact CState.down_regs_of_ne s hrx

/-- Add the literal `n` to a counter. -/
def incMany (r n : Nat) : Code := List.replicate n (Cmd.inc r)

theorem incMany_spec {R r : Nat} (hr : r < R) (n : Nat) (s : CState) :
    ∃ w', Ev R (incMany r n) s ⟨w', s.out⟩ ∧ w' r = s.regs r + n ∧
      ∀ k, k ≠ r → w' k = s.regs k := by
  induction n generalizing s with
  | zero => exact ⟨s.regs, Ev.nil, by simp, fun _ _ => rfl⟩
  | succ n ih =>
    obtain ⟨w', hev, hwr, hwfr⟩ := ih (s.up r)
    refine ⟨w', Ev.inc hr hev, ?_, ?_⟩
    · rw [hwr, CState.up_regs_self]
      omega
    · intro k hkr
      rw [hwfr k hkr, CState.up_regs_of_ne s hkr]

/-- The framing form of `copy_spec`: copying only changes its destination and
scratch register. -/
theorem copy_spec_frame {R a b t : Nat} (ha : a < R) (hb : b < R) (ht : t < R)
    (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) (s : CState) :
    ∃ w', Ev R (copy a b t) s ⟨w', s.out⟩ ∧
      w' b = s.regs a ∧ w' t = 0 ∧
      ∀ r, r ≠ b → r ≠ t → w' r = s.regs r := by
  obtain ⟨w', hev, hwa, hwb, hwt, hwfr⟩ :=
    copy_spec ha hb ht hab hat hbt s
  refine ⟨w', hev, hwb, hwt, ?_⟩
  intro r hrb hrt
  by_cases hra : r = a
  · simpa [hra] using hwa
  · exact hwfr r hra hrb hrt

/-- A register disjoint from the five comparison scratch registers. -/
def Away5 (a x y tmp gate eq : Nat) : Prop :=
  a ≠ x ∧ a ≠ y ∧ a ≠ tmp ∧ a ≠ gate ∧ a ≠ eq

/-- Compare `a` and `b` while preserving them.  The five scratch registers
are initialized and cleaned by the macro itself. -/
def equal (a b x y tmp gate eq : Nat) : Code :=
  copy a x tmp ++ copy b y tmp ++ clear gate ++ clear eq ++ [Cmd.inc eq] ++
    compareLoop x y tmp gate eq

theorem equal_spec {R a b x y tmp gate eq : Nat}
    (ha : a < R) (hb : b < R) (hx : x < R) (hy : y < R) (ht : tmp < R)
    (hg : gate < R) (he : eq < R) (hd : Distinct5 x y tmp gate eq)
    (ha5 : Away5 a x y tmp gate eq) (hb5 : Away5 b x y tmp gate eq)
    (s : CState) :
    ∃ w', Ev R (equal a b x y tmp gate eq) s ⟨w', s.out⟩ ∧
      w' x = 0 ∧ w' y = 0 ∧ w' tmp = 0 ∧ w' gate = 0 ∧
      w' eq = (if s.regs a = s.regs b then 1 else 0) ∧
      ∀ r, r ≠ x → r ≠ y → r ≠ tmp → r ≠ gate → r ≠ eq →
        w' r = s.regs r := by
  rcases hd with ⟨hxy, hxt, hxg, hxe, hyt, hyg, hye, htg, hte, hge⟩
  rcases ha5 with ⟨hax, hay, hat, hag, hae⟩
  rcases hb5 with ⟨hbx, hby, hbt, hbg, hbe⟩
  obtain ⟨w₁, h₁, h₁x, h₁t, h₁fr⟩ :=
    copy_spec_frame ha hx ht hax hat hxt s
  let s₁ : CState := ⟨w₁, s.out⟩
  have h₁b : s₁.regs b = s.regs b := by
    change w₁ b = s.regs b
    exact h₁fr b hbx hbt
  have h₁y : s₁.regs y = s.regs y := by
    change w₁ y = s.regs y
    exact h₁fr y hxy.symm hyt
  obtain ⟨w₂, h₂, h₂y, h₂t, h₂fr⟩ :=
    copy_spec_frame hb hy ht hby hbt hyt s₁
  let s₂ : CState := ⟨w₂, s.out⟩
  have h₂x : s₂.regs x = s.regs a := by
    change w₂ x = s.regs a
    rw [h₂fr x hxy hxt]
    simpa [s₁] using h₁x
  have h₂yv : s₂.regs y = s.regs b := by
    change w₂ y = s.regs b
    rw [h₂y]
    exact h₁b
  obtain ⟨w₃, h₃, h₃g, h₃fr⟩ := clear_spec hg (s₂.regs gate) s₂ rfl
  let s₃ : CState := ⟨w₃, s.out⟩
  have h₃x : s₃.regs x = s.regs a := by
    change w₃ x = s.regs a
    rw [h₃fr x hxg, h₂x]
  have h₃y : s₃.regs y = s.regs b := by
    change w₃ y = s.regs b
    rw [h₃fr y hyg, h₂yv]
  have h₃t : s₃.regs tmp = 0 := by
    change w₃ tmp = 0
    rw [h₃fr tmp htg]
    simpa [s₂] using h₂t
  obtain ⟨w₄, h₄, h₄e, h₄fr⟩ := clear_spec he (s₃.regs eq) s₃ rfl
  let s₄ : CState := ⟨w₄, s.out⟩
  have h₄x : s₄.regs x = s.regs a := by
    change w₄ x = s.regs a
    rw [h₄fr x hxe, h₃x]
  have h₄y : s₄.regs y = s.regs b := by
    change w₄ y = s.regs b
    rw [h₄fr y hye, h₃y]
  have h₄t : s₄.regs tmp = 0 := by
    change w₄ tmp = 0
    rw [h₄fr tmp hte, h₃t]
  have h₄g : s₄.regs gate = 0 := by
    change w₄ gate = 0
    rw [h₄fr gate hge]
    simpa [s₃] using h₃g
  let s₅ := s₄.up eq
  have h₅x : s₅.regs x = s.regs a := by
    rw [CState.up_regs_of_ne s₄ hxe, h₄x]
  have h₅y : s₅.regs y = s.regs b := by
    rw [CState.up_regs_of_ne s₄ hye, h₄y]
  have h₅t : s₅.regs tmp = 0 := by
    rw [CState.up_regs_of_ne s₄ hte, h₄t]
  have h₅g : s₅.regs gate = 0 := by
    rw [CState.up_regs_of_ne s₄ hge, h₄g]
  have h₄ez : s₄.regs eq = 0 := by simpa [s₄] using h₄e
  have h₅e : s₅.regs eq = 1 := by simp [s₅, h₄ez]
  obtain ⟨wF, hF, hFx, hFy, hFt, hFg, hFe, hFfr⟩ :=
    compareLoop_spec hx hy ht hg he
      ⟨hxy, hxt, hxg, hxe, hyt, hyg, hye, htg, hte, hge⟩
      (s₅.regs x) s₅ rfl h₅t h₅g h₅e
  refine ⟨wF, ?_, hFx, hFy, hFt, hFg, ?_, ?_⟩
  · unfold equal
    exact h₁.append (h₂.append (h₃.append (h₄.append (Ev.inc he hF))))
  · simpa [h₅x, h₅y] using hFe
  · intro r hrx hry hrt hrg hre
    rw [hFfr r hrx hry hrt hrg hre]
    rw [CState.up_regs_of_ne s₄ hre]
    change w₄ r = s.regs r
    rw [h₄fr r hre]
    change w₃ r = s.regs r
    rw [h₃fr r hrg]
    change w₂ r = s.regs r
    rw [h₂fr r hry hrt]
    change w₁ r = s.regs r
    exact h₁fr r hrx hrt

/-- Consume a Boolean `flag` and set a zero `pc` to one of two literals.
The auxiliary `fall` counter is cleared on exit. -/
def selectPC (pc flag fall yes no : Nat) : Code :=
  [Cmd.inc fall,
    Cmd.loop flag ([Cmd.dec flag] ++ clear fall ++ incMany pc yes),
    Cmd.loop fall ([Cmd.dec fall] ++ incMany pc no)]

theorem selectPC_spec {R pc flag fall yes no : Nat}
    (hp : pc < R) (hf : flag < R) (hl : fall < R)
    (hpf : pc ≠ flag) (hpl : pc ≠ fall) (hfl : flag ≠ fall)
    (s : CState) (hpc : s.regs pc = 0) (hflag : s.regs flag = 0 ∨ s.regs flag = 1)
    (hfall : s.regs fall = 0) :
    ∃ w', Ev R (selectPC pc flag fall yes no) s ⟨w', s.out⟩ ∧
      w' pc = (if s.regs flag = 0 then no else yes) ∧
      w' flag = 0 ∧ w' fall = 0 ∧
      ∀ r, r ≠ pc → r ≠ flag → r ≠ fall → w' r = s.regs r := by
  let sI := s.up fall
  have hIp : sI.regs pc = 0 := by rw [CState.up_regs_of_ne s hpl, hpc]
  have hIf : sI.regs flag = s.regs flag := CState.up_regs_of_ne s hfl
  have hIl : sI.regs fall = 1 := by simp [sI, hfall]
  rcases hflag with hz | ho
  · have hfirst : Ev R
        [Cmd.loop flag ([Cmd.dec flag] ++ clear fall ++ incMany pc yes)] sI sI :=
      Ev.loopZ hf (by rw [hIf, hz]) Ev.nil
    have hlnz : sI.regs fall ≠ 0 := by omega
    let sD := sI.down fall
    have hDl : sD.regs fall = 0 := by simp [sD, hIl]
    have hDp : sD.regs pc = 0 := by
      rw [CState.down_regs_of_ne sI hpl, hIp]
    have hDf : sD.regs flag = 0 := by
      rw [CState.down_regs_of_ne sI (r := fall) (k := flag) hfl, hIf, hz]
    obtain ⟨wN, hN, hNp, hNfr⟩ := incMany_spec hp no sD
    let sN : CState := ⟨wN, s.out⟩
    have hNl : sN.regs fall = 0 := by
      change wN fall = 0
      rw [hNfr fall hpl.symm, hDl]
    have hNf : sN.regs flag = 0 := by
      change wN flag = 0
      rw [hNfr flag hpf.symm, hDf]
    have hlast : Ev R [Cmd.loop fall ([Cmd.dec fall] ++ incMany pc no)] sN sN :=
      Ev.loopZ hl hNl Ev.nil
    refine ⟨wN, Ev.inc hl (hfirst.append
      (Ev.loopS hl hlnz (Ev.dec hl hlnz (hN.append hlast)))), ?_, hNf, hNl, ?_⟩
    · rw [hNp, hDp, hz, if_pos rfl]
      omega
    · intro r hrp hrf hrl
      rw [hNfr r hrp, CState.down_regs_of_ne sI hrl]
      exact CState.up_regs_of_ne s hrl
  · have hfnz : sI.regs flag ≠ 0 := by rw [hIf, ho]; omega
    let sD := sI.down flag
    have hDf : sD.regs flag = 0 := by simp [sD, hIf, ho]
    have hDp : sD.regs pc = 0 := by
      rw [CState.down_regs_of_ne sI hpf, hIp]
    have hDl : sD.regs fall = 1 := by
      rw [CState.down_regs_of_ne sI (r := flag) (k := fall) hfl.symm, hIl]
    obtain ⟨wC, hC, hCl, hCfr⟩ := clear_spec hl (sD.regs fall) sD rfl
    let sC : CState := ⟨wC, s.out⟩
    have hCp : sC.regs pc = 0 := by
      change wC pc = 0
      rw [hCfr pc hpl, hDp]
    have hCf : sC.regs flag = 0 := by
      change wC flag = 0
      rw [hCfr flag hfl, hDf]
    obtain ⟨wY, hY, hYp, hYfr⟩ := incMany_spec hp yes sC
    let sY : CState := ⟨wY, s.out⟩
    have hYf : sY.regs flag = 0 := by
      change wY flag = 0
      rw [hYfr flag hpf.symm, hCf]
    have hYl : sY.regs fall = 0 := by
      change wY fall = 0
      rw [hYfr fall hpl.symm]
      simpa [sC] using hCl
    have hfirstZ : Ev R
        [Cmd.loop flag ([Cmd.dec flag] ++ clear fall ++ incMany pc yes),
          Cmd.loop fall ([Cmd.dec fall] ++ incMany pc no)] sY sY :=
      Ev.loopZ hf hYf (Ev.loopZ hl hYl Ev.nil)
    refine ⟨wY, Ev.inc hl (Ev.loopS hf hfnz (Ev.dec hf hfnz
      (hC.append (hY.append hfirstZ)))), ?_, hYf, hYl, ?_⟩
    · rw [hYp, hCp, ho, if_neg (by omega)]
      omega
    · intro r hrp hrf hrl
      rw [hYfr r hrp]
      change wC r = s.regs r
      rw [hCfr r hrl]
      exact (CState.down_regs_of_ne sI hrf).trans (CState.up_regs_of_ne s hrl)

/-! ## Compiling one URM instruction -/

/-- Dispatcher registers are allocated immediately above the source URM
registers `0, ..., B-1`. -/
def pcReg (B : Nat) : Nat := B
def savedReg (B : Nat) : Nat := B + 1
def cmpXReg (B : Nat) : Nat := B + 2
def cmpYReg (B : Nat) : Nat := B + 3
def tmpReg (B : Nat) : Nat := B + 4
def gateReg (B : Nat) : Nat := B + 5
def eqReg (B : Nat) : Nat := B + 6
def fallReg (B : Nat) : Nat := B + 7
def counterBound (B : Nat) : Nat := B + 8

/-- Agreement of the low counter registers with a URM register file. -/
def SourceMatches (B : Nat) (w : Nat → Nat) (σ : Cslib.URM.Regs) : Prop :=
  ∀ r, r < B → w r = σ r

/-- Every dispatcher scratch counter except the program counter is zero. -/
def ScratchClean (B : Nat) (w : Nat → Nat) : Prop :=
  w (savedReg B) = 0 ∧ w (cmpXReg B) = 0 ∧ w (cmpYReg B) = 0 ∧
    w (tmpReg B) = 0 ∧ w (gateReg B) = 0 ∧ w (eqReg B) = 0 ∧
    w (fallReg B) = 0

/-- Arithmetic semantics of the registers written by one URM instruction. -/
def instrNextRegs (i : Cslib.URM.Instr) (σ : Cslib.URM.Regs) : Cslib.URM.Regs :=
  match i with
  | .Z n => σ.write n 0
  | .S n => σ.write n (σ.read n + 1)
  | .T m n => σ.write n (σ.read m)
  | .J _ _ _ => σ

/-- Arithmetic semantics of the program counter after instruction `k`. -/
def instrNextPC (k : Nat) (i : Cslib.URM.Instr) (σ : Cslib.URM.Regs) : Nat :=
  match i with
  | .Z _ | .S _ | .T _ _ => k + 1
  | .J m n q => if σ.read m = σ.read n then q else k + 1

/-- Counter code for one selected URM instruction.  It enters with `pc = 0`
and writes the encoded successor counter `instrNextPC + 1`. -/
def execInstr (B k : Nat) : Cslib.URM.Instr → Code
  | .Z n => clear n ++ incMany (pcReg B) (k + 2)
  | .S n => [Cmd.inc n] ++ incMany (pcReg B) (k + 2)
  | .T m n =>
      (if m = n then [] else copy m n (tmpReg B)) ++
        incMany (pcReg B) (k + 2)
  | .J m n q =>
      equal m n (cmpXReg B) (cmpYReg B) (tmpReg B) (gateReg B) (eqReg B) ++
        selectPC (pcReg B) (eqReg B) (fallReg B) (q + 1) (k + 2)

theorem ScratchClean.frame {B : Nat} {w w' : Nat → Nat} (h : ScratchClean B w)
    (hfr : ∀ r, B < r → r < counterBound B → w' r = w r) :
    ScratchClean B w' := by
  rcases h with ⟨hs, hx, hy, ht, hg, he, hf⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfr (savedReg B) (by simp [savedReg]) (by simp [savedReg, counterBound]), hs]
  · rw [hfr (cmpXReg B) (by simp [cmpXReg]) (by simp [cmpXReg, counterBound]), hx]
  · rw [hfr (cmpYReg B) (by simp [cmpYReg]) (by simp [cmpYReg, counterBound]), hy]
  · rw [hfr (tmpReg B) (by simp [tmpReg]) (by simp [tmpReg, counterBound]), ht]
  · rw [hfr (gateReg B) (by simp [gateReg]) (by simp [gateReg, counterBound]), hg]
  · rw [hfr (eqReg B) (by simp [eqReg]) (by simp [eqReg, counterBound]), he]
  · rw [hfr (fallReg B) (by simp [fallReg]) (by simp [fallReg, counterBound]), hf]

/-- The exact arithmetic simulation of a selected URM instruction.  Source
registers agree with `instrNextRegs`, the encoded program counter is
`instrNextPC + 1`, and every dispatcher scratch register is reset. -/
theorem execInstr_spec {B k : Nat} (i : Cslib.URM.Instr) (σ : Cslib.URM.Regs)
    (hmax : i.maxRegister < B) (s : CState)
    (hsrc : SourceMatches B s.regs σ) (hpc : s.regs (pcReg B) = 0)
    (hclean : ScratchClean B s.regs) :
    ∃ w', Ev (counterBound B) (execInstr B k i) s ⟨w', s.out⟩ ∧
      SourceMatches B w' (instrNextRegs i σ) ∧
      w' (pcReg B) = instrNextPC k i σ + 1 ∧ ScratchClean B w' := by
  have hp : pcReg B < counterBound B := by simp [pcReg, counterBound]
  cases i with
  | Z n =>
    have hn : n < B := by simpa [Cslib.URM.Instr.maxRegister] using hmax
    obtain ⟨wC, hC, hCn, hCfr⟩ :=
      clear_spec (R := counterBound B) (a := n)
        (lt_trans hn (by simp [counterBound])) (s.regs n) s rfl
    let sC : CState := ⟨wC, s.out⟩
    have hCpc : sC.regs (pcReg B) = 0 := by
      change wC (pcReg B) = 0
      rw [hCfr (pcReg B) (by simp [pcReg]; omega), hpc]
    obtain ⟨wP, hP, hPpc, hPfr⟩ := incMany_spec hp (k + 2) sC
    refine ⟨wP, hC.append hP, ?_, ?_, ?_⟩
    · intro r hr
      rw [hPfr r (by simp [pcReg]; omega)]
      change wC r = instrNextRegs (.Z n) σ r
      by_cases hrn : r = n
      · subst r
        simp [instrNextRegs, hCn, Cslib.URM.Regs.write]
      · rw [hCfr r hrn, hsrc r hr]
        simp [instrNextRegs, Cslib.URM.Regs.write, Function.update_of_ne hrn]
    · rw [hPpc, hCpc]
      simp [instrNextPC]
    · apply ScratchClean.frame hclean
      intro r hBr hrR
      rw [hPfr r (by simp [pcReg]; omega)]
      change wC r = s.regs r
      exact hCfr r (by omega)
  | S n =>
    have hn : n < B := by simpa [Cslib.URM.Instr.maxRegister] using hmax
    let sI := s.up n
    have hIpc : sI.regs (pcReg B) = 0 := by
      rw [CState.up_regs_of_ne s (by simp [pcReg]; omega), hpc]
    obtain ⟨wP, hP, hPpc, hPfr⟩ := incMany_spec hp (k + 2) sI
    refine ⟨wP, Ev.inc (lt_trans hn (by simp [counterBound])) hP, ?_, ?_, ?_⟩
    · intro r hr
      rw [hPfr r (by simp [pcReg]; omega)]
      by_cases hrn : r = n
      · subst r
        simp [sI, instrNextRegs, Cslib.URM.Regs.write, hsrc n hn,
          Cslib.URM.Regs.read]
      · rw [CState.up_regs_of_ne s hrn, hsrc r hr]
        simp [instrNextRegs, Cslib.URM.Regs.write, Function.update_of_ne hrn]
    · rw [hPpc, hIpc]
      simp [instrNextPC]
    · apply ScratchClean.frame hclean
      intro r hBr hrR
      rw [hPfr r (by simp [pcReg]; omega)]
      exact CState.up_regs_of_ne s (by omega)
  | T m n =>
    have hmnB : max m n < B := by
      simpa [Cslib.URM.Instr.maxRegister] using hmax
    have hm : m < B := lt_of_le_of_lt (Nat.le_max_left m n) hmnB
    have hn : n < B := lt_of_le_of_lt (Nat.le_max_right m n) hmnB
    by_cases hmn : m = n
    · subst n
      obtain ⟨wP, hP, hPpc, hPfr⟩ := incMany_spec hp (k + 2) s
      refine ⟨wP, ?_, ?_, ?_, ?_⟩
      · simpa [execInstr] using hP
      · intro r hr
        rw [hPfr r (by simp [pcReg]; omega), hsrc r hr]
        simp [instrNextRegs, Cslib.URM.Regs.write, Cslib.URM.Regs.read]
      · rw [hPpc, hpc]
        simp [instrNextPC]
      · apply ScratchClean.frame hclean
        intro r hBr hrR
        exact hPfr r (by simp [pcReg]; omega)
    · have ht : tmpReg B < counterBound B := by simp [tmpReg, counterBound]
      obtain ⟨wC, hC, hCn, hCt, hCfr⟩ := copy_spec_frame
        (R := counterBound B) (a := m) (b := n) (t := tmpReg B)
        (lt_trans hm (by simp [counterBound])) (lt_trans hn (by simp [counterBound]))
        ht hmn (by simp [tmpReg]; omega)
        (by simp [tmpReg]; omega) s
      let sC : CState := ⟨wC, s.out⟩
      have hCpc : sC.regs (pcReg B) = 0 := by
        change wC (pcReg B) = 0
        rw [hCfr (pcReg B) (by simp [pcReg]; omega) (by simp [pcReg, tmpReg]), hpc]
      obtain ⟨wP, hP, hPpc, hPfr⟩ := incMany_spec hp (k + 2) sC
      refine ⟨wP, ?_, ?_, ?_, ?_⟩
      · simpa [execInstr, hmn] using hC.append hP
      · intro r hr
        rw [hPfr r (by simp [pcReg]; omega)]
        change wC r = instrNextRegs (.T m n) σ r
        by_cases hrn : r = n
        · subst r
          rw [hCn, hsrc m hm]
          simp [instrNextRegs, Cslib.URM.Regs.write, Cslib.URM.Regs.read]
        · rw [hCfr r hrn (by simp [tmpReg]; omega), hsrc r hr]
          simp [instrNextRegs, Cslib.URM.Regs.write, Function.update_of_ne hrn]
      · rw [hPpc, hCpc]
        simp [instrNextPC]
      · have hCclean : ScratchClean B wC := by
          apply ScratchClean.frame hclean
          intro r hBr hrR
          by_cases hrt : r = tmpReg B
          · subst r
            rw [hCt]
            exact hclean.2.2.2.1.symm
          · exact hCfr r (by omega) hrt
        apply ScratchClean.frame hCclean
        intro r hBr hrR
        exact hPfr r (by simp [pcReg]; omega)
  | J m n q =>
    have hmnB : max m n < B := by
      simpa [Cslib.URM.Instr.maxRegister] using hmax
    have hm : m < B := lt_of_le_of_lt (Nat.le_max_left m n) hmnB
    have hn : n < B := lt_of_le_of_lt (Nat.le_max_right m n) hmnB
    have hdist : Distinct5 (cmpXReg B) (cmpYReg B) (tmpReg B)
        (gateReg B) (eqReg B) := by
      simp [Distinct5, cmpXReg, cmpYReg, tmpReg, gateReg, eqReg]
    have ham : Away5 m (cmpXReg B) (cmpYReg B) (tmpReg B) (gateReg B) (eqReg B) := by
      simp [Away5, cmpXReg, cmpYReg, tmpReg, gateReg, eqReg]
      omega
    have han : Away5 n (cmpXReg B) (cmpYReg B) (tmpReg B) (gateReg B) (eqReg B) := by
      simp [Away5, cmpXReg, cmpYReg, tmpReg, gateReg, eqReg]
      omega
    obtain ⟨wE, hE, hEx, hEy, hEt, hEg, hEe, hEfr⟩ := equal_spec
      (R := counterBound B) (a := m) (b := n)
      (lt_trans hm (by simp [counterBound])) (lt_trans hn (by simp [counterBound]))
      (by simp [cmpXReg, counterBound])
      (by simp [cmpYReg, counterBound]) (by simp [tmpReg, counterBound])
      (by simp [gateReg, counterBound]) (by simp [eqReg, counterBound])
      hdist ham han s
    let sE : CState := ⟨wE, s.out⟩
    have hEpc : sE.regs (pcReg B) = 0 := by
      change wE (pcReg B) = 0
      rw [hEfr (pcReg B) (by simp [pcReg, cmpXReg]) (by simp [pcReg, cmpYReg])
        (by simp [pcReg, tmpReg]) (by simp [pcReg, gateReg])
        (by simp [pcReg, eqReg]), hpc]
    have hEfall : sE.regs (fallReg B) = 0 := by
      change wE (fallReg B) = 0
      rw [hEfr (fallReg B) (by simp [fallReg, cmpXReg])
        (by simp [fallReg, cmpYReg]) (by simp [fallReg, tmpReg])
        (by simp [fallReg, gateReg]) (by simp [fallReg, eqReg])]
      exact hclean.2.2.2.2.2.2
    have hEflag : sE.regs (eqReg B) = 0 ∨ sE.regs (eqReg B) = 1 := by
      change wE (eqReg B) = 0 ∨ wE (eqReg B) = 1
      rw [hEe]
      split <;> simp
    have hEeq : sE.regs (eqReg B) =
        (if σ.read m = σ.read n then 1 else 0) := by
      change wE (eqReg B) = _
      rw [hEe, hsrc m hm, hsrc n hn]
      simp only [Cslib.URM.Regs.read]
      rfl
    obtain ⟨wP, hP, hPpc, hPe, hPf, hPfr⟩ := selectPC_spec
      (R := counterBound B) (pc := pcReg B) (flag := eqReg B) (fall := fallReg B)
      (yes := q + 1) (no := k + 2) hp
      (by simp [eqReg, counterBound]) (by simp [fallReg, counterBound])
      (by simp [pcReg, eqReg]) (by simp [pcReg, fallReg])
      (by simp [eqReg, fallReg]) sE hEpc hEflag hEfall
    refine ⟨wP, hE.append hP, ?_, ?_, ?_⟩
    · intro r hr
      rw [hPfr r (by simp [pcReg]; omega) (by simp [eqReg]; omega)
        (by simp [fallReg]; omega)]
      change wE r = instrNextRegs (.J m n q) σ r
      rw [hEfr r (by simp [cmpXReg]; omega) (by simp [cmpYReg]; omega)
        (by simp [tmpReg]; omega) (by simp [gateReg]; omega)
        (by simp [eqReg]; omega), hsrc r hr]
      rfl
    · rw [hPpc, hEeq]
      by_cases heq : σ.read m = σ.read n
      · simp [instrNextPC, heq]
      · simp [instrNextPC, heq]
    · refine ⟨?_, ?_, ?_, ?_, ?_, hPe, hPf⟩
      · rw [hPfr (savedReg B) (by simp [savedReg, pcReg])
          (by simp [savedReg, eqReg]) (by simp [savedReg, fallReg])]
        change wE (savedReg B) = 0
        rw [hEfr (savedReg B) (by simp [savedReg, cmpXReg])
          (by simp [savedReg, cmpYReg]) (by simp [savedReg, tmpReg])
          (by simp [savedReg, gateReg]) (by simp [savedReg, eqReg])]
        exact hclean.1
      · rw [hPfr (cmpXReg B) (by simp [cmpXReg, pcReg])
          (by simp [cmpXReg, eqReg]) (by simp [cmpXReg, fallReg])]
        exact hEx
      · rw [hPfr (cmpYReg B) (by simp [cmpYReg, pcReg])
          (by simp [cmpYReg, eqReg]) (by simp [cmpYReg, fallReg])]
        exact hEy
      · rw [hPfr (tmpReg B) (by simp [tmpReg, pcReg])
          (by simp [tmpReg, eqReg]) (by simp [tmpReg, fallReg])]
        exact hEt
      · rw [hPfr (gateReg B) (by simp [gateReg, pcReg])
          (by simp [gateReg, eqReg]) (by simp [gateReg, fallReg])]
        exact hEg

/-! ## Dispatching on the saved program counter -/

/-- The scratch invariant used while scanning instruction blocks. -/
def AuxClean (B : Nat) (w : Nat → Nat) : Prop :=
  w (cmpXReg B) = 0 ∧ w (cmpYReg B) = 0 ∧ w (tmpReg B) = 0 ∧
    w (gateReg B) = 0 ∧ w (eqReg B) = 0 ∧ w (fallReg B) = 0

/-- Compare the saved encoded program counter to `k + 1`. -/
def testLiteral (B k : Nat) : Code :=
  incMany (fallReg B) (k + 1) ++
    equal (savedReg B) (fallReg B) (cmpXReg B) (cmpYReg B)
      (tmpReg B) (gateReg B) (eqReg B) ++
    clear (fallReg B)

theorem testLiteral_spec {B k : Nat} (s : CState) (haux : AuxClean B s.regs) :
    ∃ w', Ev (counterBound B) (testLiteral B k) s ⟨w', s.out⟩ ∧
      w' (eqReg B) = (if s.regs (savedReg B) = k + 1 then 1 else 0) ∧
      w' (cmpXReg B) = 0 ∧ w' (cmpYReg B) = 0 ∧ w' (tmpReg B) = 0 ∧
      w' (gateReg B) = 0 ∧ w' (fallReg B) = 0 ∧
      ∀ r, r ≠ cmpXReg B → r ≠ cmpYReg B → r ≠ tmpReg B →
        r ≠ gateReg B → r ≠ eqReg B → r ≠ fallReg B → w' r = s.regs r := by
  obtain ⟨wI, hI, hIfall, hIfr⟩ := incMany_spec
    (R := counterBound B) (r := fallReg B)
    (by simp [fallReg, counterBound]) (k + 1) s
  let sI : CState := ⟨wI, s.out⟩
  have hIsaved : sI.regs (savedReg B) = s.regs (savedReg B) := by
    change wI (savedReg B) = _
    exact hIfr _ (by simp [savedReg, fallReg])
  have hIfall' : sI.regs (fallReg B) = k + 1 := by
    change wI (fallReg B) = k + 1
    rw [hIfall, haux.2.2.2.2.2]
    omega
  have hd : Distinct5 (cmpXReg B) (cmpYReg B) (tmpReg B)
      (gateReg B) (eqReg B) := by
    simp [Distinct5, cmpXReg, cmpYReg, tmpReg, gateReg, eqReg]
  have hsaved : Away5 (savedReg B) (cmpXReg B) (cmpYReg B) (tmpReg B)
      (gateReg B) (eqReg B) := by
    simp [Away5, savedReg, cmpXReg, cmpYReg, tmpReg, gateReg, eqReg]
  have hfall : Away5 (fallReg B) (cmpXReg B) (cmpYReg B) (tmpReg B)
      (gateReg B) (eqReg B) := by
    simp [Away5, fallReg, cmpXReg, cmpYReg, tmpReg, gateReg, eqReg]
  obtain ⟨wE, hE, hEx, hEy, hEt, hEg, hEe, hEfr⟩ := equal_spec
    (R := counterBound B) (a := savedReg B) (b := fallReg B)
    (by simp [savedReg, counterBound]) (by simp [fallReg, counterBound])
    (by simp [cmpXReg, counterBound]) (by simp [cmpYReg, counterBound])
    (by simp [tmpReg, counterBound]) (by simp [gateReg, counterBound])
    (by simp [eqReg, counterBound]) hd hsaved hfall sI
  let sE : CState := ⟨wE, s.out⟩
  have hEeq : sE.regs (eqReg B) =
      (if s.regs (savedReg B) = k + 1 then 1 else 0) := by
    change wE (eqReg B) = _
    simpa [hIsaved, hIfall'] using hEe
  obtain ⟨wC, hC, hCfall, hCfr⟩ := clear_spec
    (R := counterBound B) (a := fallReg B) (by simp [fallReg, counterBound])
    (sE.regs (fallReg B)) sE rfl
  refine ⟨wC, ?_, ?_, ?_, ?_, ?_, ?_, hCfall, ?_⟩
  · unfold testLiteral
    simpa [List.append_assoc] using hI.append (hE.append hC)
  · rw [hCfr (eqReg B) (by simp [eqReg, fallReg])]
    exact hEeq
  · rw [hCfr (cmpXReg B) (by simp [cmpXReg, fallReg])]
    exact hEx
  · rw [hCfr (cmpYReg B) (by simp [cmpYReg, fallReg])]
    exact hEy
  · rw [hCfr (tmpReg B) (by simp [tmpReg, fallReg])]
    exact hEt
  · rw [hCfr (gateReg B) (by simp [gateReg, fallReg])]
    exact hEg
  · intro r hrx hry hrt hrg hre hrf
    rw [hCfr r hrf]
    change wE r = s.regs r
    rw [hEfr r hrx hry hrt hrg hre]
    change wI r = s.regs r
    exact hIfr r hrf

/-- One guarded instruction block in the linear dispatcher. -/
def dispatchBlock (B k : Nat) (i : Cslib.URM.Instr) : Code :=
  testLiteral B k ++
    [Cmd.loop (eqReg B)
      ([Cmd.dec (eqReg B)] ++ clear (savedReg B) ++ execInstr B k i)]

theorem dispatchBlock_miss {B k : Nat} (i : Cslib.URM.Instr)
    (σ : Cslib.URM.Regs) (s : CState) (hsrc : SourceMatches B s.regs σ)
    (haux : AuxClean B s.regs) (hmiss : s.regs (savedReg B) ≠ k + 1) :
    ∃ w', Ev (counterBound B) (dispatchBlock B k i) s ⟨w', s.out⟩ ∧
      SourceMatches B w' σ ∧ w' (pcReg B) = s.regs (pcReg B) ∧
      w' (savedReg B) = s.regs (savedReg B) ∧ AuxClean B w' := by
  obtain ⟨wT, hT, hTe, hTx, hTy, hTt, hTg, hTf, hTfr⟩ :=
    testLiteral_spec (B := B) (k := k) s haux
  have hTe0 : wT (eqReg B) = 0 := by rw [hTe, if_neg hmiss]
  have hloop : Ev (counterBound B)
      [Cmd.loop (eqReg B)
        ([Cmd.dec (eqReg B)] ++ clear (savedReg B) ++ execInstr B k i)]
      ⟨wT, s.out⟩ ⟨wT, s.out⟩ :=
    Ev.loopZ (by simp [eqReg, counterBound]) hTe0 Ev.nil
  refine ⟨wT, hT.append hloop, ?_, ?_, ?_, ?_⟩
  · intro r hr
    rw [hTfr r (by simp [cmpXReg]; omega) (by simp [cmpYReg]; omega)
      (by simp [tmpReg]; omega) (by simp [gateReg]; omega)
      (by simp [eqReg]; omega) (by simp [fallReg]; omega)]
    exact hsrc r hr
  · exact hTfr _ (by simp [pcReg, cmpXReg]) (by simp [pcReg, cmpYReg])
      (by simp [pcReg, tmpReg]) (by simp [pcReg, gateReg])
      (by simp [pcReg, eqReg]) (by simp [pcReg, fallReg])
  · exact hTfr _ (by simp [savedReg, cmpXReg]) (by simp [savedReg, cmpYReg])
      (by simp [savedReg, tmpReg]) (by simp [savedReg, gateReg])
      (by simp [savedReg, eqReg]) (by simp [savedReg, fallReg])
  · exact ⟨hTx, hTy, hTt, hTg, hTe0, hTf⟩

theorem dispatchBlock_hit {B k : Nat} (i : Cslib.URM.Instr)
    (σ : Cslib.URM.Regs) (hmax : i.maxRegister < B) (s : CState)
    (hsrc : SourceMatches B s.regs σ) (hpc : s.regs (pcReg B) = 0)
    (haux : AuxClean B s.regs) (hhit : s.regs (savedReg B) = k + 1) :
    ∃ w', Ev (counterBound B) (dispatchBlock B k i) s ⟨w', s.out⟩ ∧
      SourceMatches B w' (instrNextRegs i σ) ∧
      w' (pcReg B) = instrNextPC k i σ + 1 ∧ ScratchClean B w' := by
  obtain ⟨wT, hT, hTe, hTx, hTy, hTt, hTg, hTf, hTfr⟩ :=
    testLiteral_spec (B := B) (k := k) s haux
  have hTe1 : wT (eqReg B) = 1 := by rw [hTe, if_pos hhit]
  have hTsrc : SourceMatches B wT σ := by
    intro r hr
    rw [hTfr r (by simp [cmpXReg]; omega) (by simp [cmpYReg]; omega)
      (by simp [tmpReg]; omega) (by simp [gateReg]; omega)
      (by simp [eqReg]; omega) (by simp [fallReg]; omega)]
    exact hsrc r hr
  have hTpc : wT (pcReg B) = 0 := by
    rw [hTfr _ (by simp [pcReg, cmpXReg]) (by simp [pcReg, cmpYReg])
      (by simp [pcReg, tmpReg]) (by simp [pcReg, gateReg])
      (by simp [pcReg, eqReg]) (by simp [pcReg, fallReg]), hpc]
  have hTsave : wT (savedReg B) = k + 1 := by
    rw [hTfr _ (by simp [savedReg, cmpXReg]) (by simp [savedReg, cmpYReg])
      (by simp [savedReg, tmpReg]) (by simp [savedReg, gateReg])
      (by simp [savedReg, eqReg]) (by simp [savedReg, fallReg]), hhit]
  let sD := (⟨wT, s.out⟩ : CState).down (eqReg B)
  have hDe : sD.regs (eqReg B) = 0 := by simp [sD, hTe1]
  have hDsave : sD.regs (savedReg B) = k + 1 := by
    rw [CState.down_regs_of_ne _ (by simp [savedReg, eqReg])]
    simpa using hTsave
  obtain ⟨wC, hC, hCsave, hCfr⟩ := clear_spec
    (R := counterBound B) (a := savedReg B) (by simp [savedReg, counterBound])
    (sD.regs (savedReg B)) sD rfl
  let sC : CState := ⟨wC, s.out⟩
  have hCsrc : SourceMatches B wC σ := by
    intro r hr
    rw [hCfr r (by simp [savedReg]; omega)]
    rw [CState.down_regs_of_ne _ (by simp [eqReg]; omega)]
    exact hTsrc r hr
  have hCpc : sC.regs (pcReg B) = 0 := by
    change wC (pcReg B) = 0
    rw [hCfr _ (by simp [pcReg, savedReg])]
    rw [CState.down_regs_of_ne _ (by simp [pcReg, eqReg])]
    simpa using hTpc
  have hCclean : ScratchClean B wC := by
    refine ⟨hCsave, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hCfr _ (by simp [cmpXReg, savedReg])]
      rw [CState.down_regs_of_ne _ (by simp [cmpXReg, eqReg])]
      exact hTx
    · rw [hCfr _ (by simp [cmpYReg, savedReg])]
      rw [CState.down_regs_of_ne _ (by simp [cmpYReg, eqReg])]
      exact hTy
    · rw [hCfr _ (by simp [tmpReg, savedReg])]
      rw [CState.down_regs_of_ne _ (by simp [tmpReg, eqReg])]
      exact hTt
    · rw [hCfr _ (by simp [gateReg, savedReg])]
      rw [CState.down_regs_of_ne _ (by simp [gateReg, eqReg])]
      exact hTg
    · rw [hCfr _ (by simp [eqReg, savedReg]), hDe]
    · rw [hCfr _ (by simp [fallReg, savedReg])]
      rw [CState.down_regs_of_ne _ (by simp [fallReg, eqReg])]
      exact hTf
  obtain ⟨wI, hI, hIsrc, hIpc, hIclean⟩ :=
    execInstr_spec i σ hmax sC hCsrc hCpc hCclean
  have hIeq : wI (eqReg B) = 0 := hIclean.2.2.2.2.2.1
  have hloopZ : Ev (counterBound B)
      [Cmd.loop (eqReg B)
        ([Cmd.dec (eqReg B)] ++ clear (savedReg B) ++ execInstr B k i)]
      ⟨wI, s.out⟩ ⟨wI, s.out⟩ :=
    Ev.loopZ (by simp [eqReg, counterBound]) hIeq Ev.nil
  have hTenz : (⟨wT, s.out⟩ : CState).regs (eqReg B) ≠ 0 := by
    change wT (eqReg B) ≠ 0
    omega
  refine ⟨wI, hT.append ?_, hIsrc, hIpc, hIclean⟩
  exact Ev.loopS (by simp [eqReg, counterBound]) hTenz
    (Ev.dec (by simp [eqReg, counterBound]) hTenz
      (hC.append (hI.append hloopZ)))


/-! ## Paired unary columns on the Brainfuck tape

For a fixed positive register bound `R`, a row occupies `2 * R` cells.  The
two columns belonging to register `r` are its data column and a guide column.
If the counter contains `n`, both columns contain `1` in rows `0, ..., n-1`
and `0` from row `n` onward.  A zero guard row precedes row zero.  The guide
column lets the generated code return to row zero after finding the end of a
counter without storing a bounded row number.
-/

open Langlib.Brainfuck

/-- Number of tape cells in one row of the paired-column layout. -/
def stride (R : Nat) : Nat := 2 * R

/-- Absolute tape position of the data cell for `(row, r)`.  Row zero starts
after the guard row. -/
def dataPos (R row r : Nat) : Nat := stride R * (row + 1) + 2 * r

/-- Absolute tape position of the guide cell for `(row, r)`. -/
def guidePos (R row r : Nat) : Nat := dataPos R row r + 1

/-- The finite part of the zipper tape, read from cell zero to the last cell
that has been allocated. -/
def tapeCells (s : Brainfuck.State) : List UInt8 :=
  s.left.reverse ++ s.cell :: s.right

/-- Read a tape position, treating the unallocated suffix as zero. -/
def tapeAt (s : Brainfuck.State) (p : Nat) : UInt8 :=
  (tapeCells s).getD p 0

/-- The interpreter lifted to a configuration whose first component is the
remaining Brainfuck command queue. -/
def bfExec (cfg : Brainfuck.Config) :
    Nat → (List Brainfuck.Op × Brainfuck.State) → Brainfuck.State × Exit :=
  fun fuel q => Brainfuck.exec cfg fuel q.1 q.2

/-- `n` consecutive pointer moves. -/
def rights (n : Nat) : List Brainfuck.Op := List.replicate n .right
def lefts (n : Nat) : List Brainfuck.Op := List.replicate n .left

/-- Move from the row-zero data cell of register zero to that of `r`. -/
def toReg (r : Nat) : List Brainfuck.Op := rights (2 * r)

/-- Move from the row-zero data cell of `r` back to register zero. -/
def fromReg (r : Nat) : List Brainfuck.Op := lefts (2 * r)

/-- Brainfuck code for incrementing the unary counter under the pointer.
It first finds the zero just after the run, fills the data and guide cells,
then follows the guide column back to the guard row. -/
def incAt (R : Nat) : List Brainfuck.Op :=
  [.loop (rights (stride R)), .inc, .right, .inc, .loop (lefts (stride R))] ++
  rights (stride R) ++ [.left]

/-- Brainfuck code for decrementing a nonzero unary counter under the
pointer. -/
def decAt (R : Nat) : List Brainfuck.Op :=
  [.loop (rights (stride R))] ++ lefts (stride R) ++ [.dec, .right, .dec] ++
  lefts (stride R) ++ [.loop (lefts (stride R))] ++ rights (stride R) ++ [.left]

/-- Compositional translation of structured counter code.  Every translated
command starts and ends at the row-zero cell of register zero. -/
def lower (R : Nat) : Code → List Brainfuck.Op
  | [] => []
  | .inc r :: cs => toReg r ++ incAt R ++ fromReg r ++ lower R cs
  | .dec r :: cs => toReg r ++ decAt R ++ fromReg r ++ lower R cs
  | .emit :: cs => .output :: lower R cs
  | .loop r body :: cs =>
      toReg r ++
        [.loop (fromReg r ++ lower R body ++ toReg r)] ++
        fromReg r ++ lower R cs

theorem lower_append (R : Nat) (a b : Code) :
    lower R (a ++ b) = lower R a ++ lower R b := by
  induction a with
  | nil => simp [lower]
  | cons c cs ih =>
    cases c <;> simp only [lower, List.cons_append, ih, List.append_assoc]

/-! ### Exact one-command execution -/

variable {cfg : Brainfuck.Config} {k : List Brainfuck.Op} {s : Brainfuck.State}

theorem reaches_bf_inc :
    Reaches (bfExec cfg) (.inc :: k, s) (k, { s with cell := s.cell + 1 }) :=
  Reaches.one fun f => by simp only [bfExec, Brainfuck.exec]

theorem reaches_bf_dec :
    Reaches (bfExec cfg) (.dec :: k, s) (k, { s with cell := s.cell - 1 }) :=
  Reaches.one fun f => by simp only [bfExec, Brainfuck.exec]

theorem reaches_bf_right :
    Reaches (bfExec cfg) (.right :: k, s) (k, s.moveRight) :=
  Reaches.one fun f => by simp only [bfExec, Brainfuck.exec]

theorem reaches_bf_left {s' : Brainfuck.State} (h : s.moveLeft? = some s') :
    Reaches (bfExec cfg) (.left :: k, s) (k, s') :=
  Reaches.one fun f => by simp only [bfExec, Brainfuck.exec, h]

theorem reaches_bf_output :
    Reaches (bfExec cfg) (.output :: k, s)
      (k, { s with output := s.output.push s.cell }) :=
  Reaches.one fun f => by simp only [bfExec, Brainfuck.exec]

theorem reaches_bf_loop_zero {body : List Brainfuck.Op} (h : s.cell = 0) :
    Reaches (bfExec cfg) (.loop body :: k, s) (k, s) :=
  Reaches.one fun f => by simp [bfExec, Brainfuck.exec, h]

theorem reaches_bf_loop_nonzero {body : List Brainfuck.Op} (h : s.cell ≠ 0) :
    Reaches (bfExec cfg) (.loop body :: k, s)
      (body ++ .loop body :: k, s) :=
  Reaches.one fun f => by
    simp only [bfExec, Brainfuck.exec]
    rw [if_neg (by simpa using h)]

/-! ### Tape movement -/

theorem tapeCells_moveLeft {s s' : Brainfuck.State} (h : s.moveLeft? = some s') :
    tapeCells s' = tapeCells s := by
  cases s with
  | mk left cell right input output =>
    cases left with
    | nil => simp [Brainfuck.State.moveLeft?] at h
    | cons c cs =>
      simp only [Brainfuck.State.moveLeft?, Option.some.injEq] at h
      subst s'
      simp [tapeCells, List.reverse_cons, List.append_assoc]

theorem tapeAt_moveLeft {s s' : Brainfuck.State} (h : s.moveLeft? = some s') (p : Nat) :
    tapeAt s' p = tapeAt s p := by
  unfold tapeAt
  rw [tapeCells_moveLeft h]

theorem pointer_moveLeft {s s' : Brainfuck.State} (h : s.moveLeft? = some s') :
    s'.left.length + 1 = s.left.length := by
  cases s with
  | mk left cell right input output =>
    cases left with
    | nil => simp [Brainfuck.State.moveLeft?] at h
    | cons c cs =>
      simp only [Brainfuck.State.moveLeft?, Option.some.injEq] at h
      subst s'
      simp

theorem pointer_moveRight (s : Brainfuck.State) :
    s.moveRight.left.length = s.left.length + 1 := by
  cases s with
  | mk left cell right input output =>
    cases right <;> simp [Brainfuck.State.moveRight]

private theorem getD_append_zero (xs : List UInt8) (p : Nat) :
    (xs ++ [0]).getD p 0 = xs.getD p 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append]
  by_cases h : p < xs.length
  · simp [h]
  · have hle : xs.length ≤ p := by omega
    rw [if_neg h, List.getElem?_eq_none hle]
    by_cases hp : p - xs.length = 0 <;> simp [hp]

theorem tapeAt_moveRight (s : Brainfuck.State) (p : Nat) :
    tapeAt s.moveRight p = tapeAt s p := by
  cases s with
  | mk left cell right input output =>
    cases right with
    | nil =>
      simp only [Brainfuck.State.moveRight, tapeAt, tapeCells, List.reverse_cons]
      exact getD_append_zero _ _
    | cons c cs =>
      simp [Brainfuck.State.moveRight, tapeAt, tapeCells, List.reverse_cons,
        List.append_assoc]

theorem tapeAt_pointer (s : Brainfuck.State) : tapeAt s s.left.length = s.cell := by
  unfold tapeAt tapeCells
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by simp : s.left.reverse.length ≤ s.left.length)]
  simp

theorem moveLeft?_moveRight (s : Brainfuck.State) :
    ∃ s', s.moveRight.moveLeft? = some s' := by
  cases s with
  | mk left cell right input output =>
    cases right with
    | nil => exact ⟨⟨left, cell, [0], input, output⟩, rfl⟩
    | cons c cs => exact ⟨⟨left, cell, c :: cs, input, output⟩, rfl⟩

/-- Functional iteration of right moves. -/
def moveRightN : Nat → Brainfuck.State → Brainfuck.State
  | 0, s => s
  | n + 1, s => moveRightN n s.moveRight

/-- Relational iteration of successful left moves. -/
inductive MoveLeftN : Nat → Brainfuck.State → Brainfuck.State → Prop where
  | zero (s : Brainfuck.State) : MoveLeftN 0 s s
  | succ {n : Nat} {s s₁ t : Brainfuck.State} :
      s.moveLeft? = some s₁ → MoveLeftN n s₁ t → MoveLeftN (n + 1) s t

theorem reaches_rights (n : Nat) (k : List Brainfuck.Op) (s : Brainfuck.State) :
    Reaches (bfExec cfg) (rights n ++ k, s) (k, moveRightN n s) := by
  induction n generalizing s with
  | zero => simpa [rights, moveRightN] using Reaches.refl (bfExec cfg) (k, s)
  | succ n ih =>
    simp only [rights, List.replicate_succ, List.cons_append, moveRightN]
    exact Reaches.trans reaches_bf_right (ih s.moveRight)

theorem reaches_lefts {n : Nat} {s t : Brainfuck.State} (h : MoveLeftN n s t)
    (k : List Brainfuck.Op) :
    Reaches (bfExec cfg) (lefts n ++ k, s) (k, t) := by
  induction h with
  | zero s => simpa [lefts] using Reaches.refl (bfExec cfg) (k, s)
  | succ h _ ih =>
    simp only [lefts, List.replicate_succ, List.cons_append]
    exact Reaches.trans (reaches_bf_left h) ih

theorem moveRightN_pointer (n : Nat) (s : Brainfuck.State) :
    (moveRightN n s).left.length = s.left.length + n := by
  induction n generalizing s with
  | zero => simp [moveRightN]
  | succ n ih => simp only [moveRightN, ih, pointer_moveRight]; omega

theorem moveRightN_tapeAt (n : Nat) (s : Brainfuck.State) (p : Nat) :
    tapeAt (moveRightN n s) p = tapeAt s p := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [moveRightN, ih, tapeAt_moveRight]

theorem moveRightN_cell (n : Nat) (s : Brainfuck.State) :
    (moveRightN n s).cell = tapeAt s (s.left.length + n) := by
  rw [← tapeAt_pointer (moveRightN n s), moveRightN_tapeAt, moveRightN_pointer]

theorem MoveLeftN.pointer {n : Nat} {s t : Brainfuck.State} (h : MoveLeftN n s t) :
    t.left.length + n = s.left.length := by
  induction h with
  | zero => simp
  | succ hm _ ih => have hp := pointer_moveLeft hm; omega

theorem MoveLeftN.tapeAt {n : Nat} {s t : Brainfuck.State} (h : MoveLeftN n s t)
    (p : Nat) : tapeAt t p = tapeAt s p := by
  induction h with
  | zero => rfl
  | succ hm _ ih => rw [ih, tapeAt_moveLeft hm]

theorem exists_moveLeftN {n : Nat} {s : Brainfuck.State} (h : n ≤ s.left.length) :
    ∃ t, MoveLeftN n s t := by
  induction n generalizing s with
  | zero => exact ⟨s, .zero s⟩
  | succ n ih =>
    cases s with
    | mk left cell right input output =>
      cases left with
      | nil => simp at h
      | cons c cs =>
        let s₁ : Brainfuck.State := ⟨cs, c, cell :: right, input, output⟩
        have hm : (⟨c :: cs, cell, right, input, output⟩ : Brainfuck.State).moveLeft? =
            some s₁ := rfl
        have hn : n ≤ s₁.left.length := by simp only [s₁]; simp only [List.length_cons] at h; omega
        obtain ⟨t, ht⟩ := ih hn
        exact ⟨t, .succ hm ht⟩

/-- Moving right and then the same distance left returns to the original
absolute pointer and preserves every tape cell. -/
theorem right_left_roundtrip (n : Nat) (s : Brainfuck.State) :
    ∃ t, MoveLeftN n (moveRightN n s) t ∧
      t.left.length = s.left.length ∧ ∀ p, tapeAt t p = tapeAt s p := by
  have hle : n ≤ (moveRightN n s).left.length := by rw [moveRightN_pointer]; omega
  obtain ⟨t, ht⟩ := exists_moveLeftN hle
  refine ⟨t, ht, ?_, ?_⟩
  · have := ht.pointer; rw [moveRightN_pointer] at this; omega
  · intro p; rw [ht.tapeAt, moveRightN_tapeAt]

theorem moveRightN_add (a b : Nat) (s : Brainfuck.State) :
    moveRightN (a + b) s = moveRightN b (moveRightN a s) := by
  induction a generalizing s with
  | zero => simp [moveRightN]
  | succ a ih =>
    rw [Nat.succ_add]
    simp only [moveRightN]
    exact ih s.moveRight

theorem tapeAt_setCell_self (s : Brainfuck.State) (v : UInt8) :
    tapeAt { s with cell := v } s.left.length = v := by
  simpa using tapeAt_pointer ({ s with cell := v } : Brainfuck.State)

theorem tapeAt_setCell_of_ne (s : Brainfuck.State) (v : UInt8) (p : Nat)
    (h : p ≠ s.left.length) :
    tapeAt { s with cell := v } p = tapeAt s p := by
  unfold tapeAt tapeCells
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  by_cases hp : p < s.left.length
  · rw [List.getElem?_append_left (by simpa using hp),
      List.getElem?_append_left (by simpa using hp)]
  · have hgt : s.left.length < p := by omega
    rw [List.getElem?_append_right (by simpa using (Nat.le_of_lt hgt) :
        s.left.reverse.length ≤ p),
      List.getElem?_append_right (by simpa using (Nat.le_of_lt hgt) :
        s.left.reverse.length ≤ p)]
    have heq : p - s.left.reverse.length = (p - s.left.length - 1) + 1 := by
      simp only [List.length_reverse]
      omega
    rw [heq]
    simp only [List.getElem?_cons_succ]

theorem tapeAt_setCell (s : Brainfuck.State) (v : UInt8) (p : Nat) :
    tapeAt { s with cell := v } p =
      if p = s.left.length then v else tapeAt s p := by
  by_cases h : p = s.left.length
  · subst p; rw [if_pos rfl, tapeAt_setCell_self]
  · rw [if_neg h, tapeAt_setCell_of_ne _ _ _ h]

theorem moveRightN_output (n : Nat) (s : Brainfuck.State) :
    (moveRightN n s).output = s.output := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [moveRightN, ih]
    cases s with
    | mk left cell right input output => cases right <;> rfl

private theorem output_moveLeft {s s' : Brainfuck.State} (h : s.moveLeft? = some s') :
    s'.output = s.output := by
  cases s with
  | mk left cell right input output =>
    cases left with
    | nil => simp [Brainfuck.State.moveLeft?] at h
    | cons c cs =>
      simp only [Brainfuck.State.moveLeft?, Option.some.injEq] at h
      subst s'
      rfl

theorem MoveLeftN.output {n : Nat} {s t : Brainfuck.State} (h : MoveLeftN n s t) :
    t.output = s.output := by
  induction h with
  | zero => rfl
  | succ hm _ ih => exact ih.trans (output_moveLeft hm)

private theorem slot_sub (width q slot j : Nat) (hj : j ≤ q) :
    width * q + slot - width * j = width * (q - j) + slot := by
  have hq : q = j + (q - j) := by omega
  conv_lhs => rw [hq, Nat.mul_add]
  omega

/-- The Brainfuck tape and output represent a counter-machine state at the
fixed base pointer. -/
def Matches (R : Nat) (c : CState) (s : Brainfuck.State) : Prop :=
  0 < R ∧
  s.left.length = stride R ∧
  s.output.size = c.out ∧
  (∀ r, r < R → tapeAt s (2 * r + 1) = 0) ∧
  ∀ r, r < R → ∀ row,
    tapeAt s (dataPos R row r) = (if row < c.regs r then 1 else 0) ∧
    tapeAt s (guidePos R row r) = (if row < c.regs r then 1 else 0)

theorem Matches.cell_at_reg {R : Nat} {c : CState} {s : Brainfuck.State}
    (h : Matches R c s) {r : Nat} (hr : r < R) :
    (moveRightN (2 * r) s).cell = (if 0 < c.regs r then 1 else 0) := by
  rw [moveRightN_cell, h.2.1]
  simpa [dataPos] using (h.2.2.2.2 r hr 0).1

theorem Matches.output_push {R : Nat} {c : CState} {s : Brainfuck.State}
    (h : Matches R c s) :
    Matches R c.emitOne { s with output := s.output.push s.cell } := by
  refine ⟨h.1, h.2.1, ?_, ?_⟩
  · simp [CState.emitOne, h.2.2.1]
  · exact ⟨h.2.2.2.1, h.2.2.2.2⟩

private theorem slotPos_inj {R a b x y : Nat} (hR : 0 < R)
    (hx : x < stride R) (hy : y < stride R)
    (h : stride R * a + x = stride R * b + y) : a = b ∧ x = y := by
  have hm := congrArg (fun z => z % stride R) h
  have hxy : x = y := by
    simpa [Nat.add_mod, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] using hm
  subst y
  have hab : stride R * a = stride R * b := by omega
  exact ⟨Nat.eq_of_mul_eq_mul_left (by simp [stride, hR]) hab, rfl⟩

theorem dataPos_inj {R row row' r r' : Nat} (hR : 0 < R)
    (hr : r < R) (hr' : r' < R)
    (h : dataPos R row r = dataPos R row' r') : row = row' ∧ r = r' := by
  have hs := slotPos_inj hR (by simp [stride]; omega : 2 * r < stride R)
    (by simp [stride]; omega : 2 * r' < stride R) h
  constructor <;> omega

theorem guidePos_inj {R row row' r r' : Nat} (hR : 0 < R)
    (hr : r < R) (hr' : r' < R)
    (h : guidePos R row r = guidePos R row' r') : row = row' ∧ r = r' := by
  have hh : stride R * (row + 1) + (2 * r + 1) =
      stride R * (row' + 1) + (2 * r' + 1) := by
    unfold guidePos dataPos at h
    omega
  have hs := slotPos_inj (a := row + 1) (b := row' + 1) hR
    (by simp [stride]; omega : 2 * r + 1 < stride R)
    (by simp [stride]; omega : 2 * r' + 1 < stride R) hh
  constructor <;> omega

theorem dataPos_ne_guidePos {R row row' r r' : Nat} (hR : 0 < R)
    (hr : r < R) (hr' : r' < R) : dataPos R row r ≠ guidePos R row' r' := by
  intro h
  have hh : stride R * (row + 1) + 2 * r =
      stride R * (row' + 1) + (2 * r' + 1) := by
    unfold guidePos dataPos at h
    omega
  have hs := slotPos_inj (a := row + 1) (b := row' + 1) hR
    (by simp [stride]; omega : 2 * r < stride R)
    (by simp [stride]; omega : 2 * r' + 1 < stride R) hh
  omega

theorem guard_ne_dataPos {R row r r' : Nat} (hR : 0 < R)
    (hr : r < R) (hr' : r' < R) : 2 * r + 1 ≠ dataPos R row r' := by
  intro h
  have hh : stride R * 0 + (2 * r + 1) = stride R * (row + 1) + 2 * r' := by
    unfold dataPos at h
    simpa only [Nat.mul_zero, Nat.zero_add] using h
  have hs := slotPos_inj (a := 0) (b := row + 1) hR
    (by simp [stride]; omega : 2 * r + 1 < stride R)
    (by simp [stride]; omega : 2 * r' < stride R)
    hh
  omega

theorem guard_ne_guidePos {R row r r' : Nat} (hR : 0 < R)
    (hr : r < R) (hr' : r' < R) : 2 * r + 1 ≠ guidePos R row r' := by
  intro h
  have hh : stride R * 0 + (2 * r + 1) =
      stride R * (row + 1) + (2 * r' + 1) := by
    unfold guidePos dataPos at h
    simp only [Nat.mul_zero, Nat.zero_add]
    omega
  have hs := slotPos_inj (a := 0) (b := row + 1) hR
    (by simp [stride]; omega : 2 * r + 1 < stride R)
    (by simp [stride]; omega : 2 * r' + 1 < stride R)
    hh
  omega

theorem matches_up_of_tape {R r : Nat} {c : CState} {s t : Brainfuck.State}
    (h : Matches R c s) (hr : r < R)
    (hptr : t.left.length = stride R) (hout : t.output = s.output)
    (htape : ∀ p, tapeAt t p =
      if p = dataPos R (c.regs r) r ∨ p = guidePos R (c.regs r) r then 1
      else tapeAt s p) :
    Matches R (c.up r) t := by
  refine ⟨h.1, hptr, ?_, ?_, ?_⟩
  · rw [hout, h.2.2.1]
    rfl
  · intro r' hr'
    rw [htape]
    rw [if_neg]
    · exact h.2.2.2.1 r' hr'
    · simp only [not_or]
      exact ⟨guard_ne_dataPos h.1 hr' hr,
        guard_ne_guidePos h.1 hr' hr⟩
  · intro r' hr' row
    constructor
    · rw [htape]
      have hcross : dataPos R row r' ≠ guidePos R (c.regs r) r :=
        dataPos_ne_guidePos h.1 hr' hr
      by_cases heq : dataPos R row r' = dataPos R (c.regs r) r
      · have hi := dataPos_inj h.1 hr' hr heq
        rw [if_pos (Or.inl heq)]
        rcases hi with ⟨hrow, hrr⟩
        subst r'
        subst row
        simp [CState.up]
      · rw [if_neg (by simp [heq, hcross])]
        rw [(h.2.2.2.2 r' hr' row).1]
        by_cases hrr : r' = r
        · subst r'
          have hrow : row ≠ c.regs r := by
            intro hrow
            exact heq (by simp [hrow])
          simp only [CState.up_regs_self]
          by_cases hlt : row < c.regs r
          · rw [if_pos hlt, if_pos (by omega)]
          · rw [if_neg hlt, if_neg (by omega)]
        · simp [CState.up, Function.update_of_ne hrr]
    · rw [htape]
      have hcross : guidePos R row r' ≠ dataPos R (c.regs r) r :=
        (dataPos_ne_guidePos h.1 hr hr').symm
      by_cases heq : guidePos R row r' = guidePos R (c.regs r) r
      · have hi := guidePos_inj h.1 hr' hr heq
        rw [if_pos (Or.inr heq)]
        rcases hi with ⟨hrow, hrr⟩
        subst r'
        subst row
        simp [CState.up]
      · rw [if_neg (by simp [heq, hcross])]
        rw [(h.2.2.2.2 r' hr' row).2]
        by_cases hrr : r' = r
        · subst r'
          have hrow : row ≠ c.regs r := by
            intro hrow
            exact heq (by simp [hrow])
          simp only [CState.up_regs_self]
          by_cases hlt : row < c.regs r
          · rw [if_pos hlt, if_pos (by omega)]
          · rw [if_neg hlt, if_neg (by omega)]
        · simp [CState.up, Function.update_of_ne hrr]

theorem matches_down_of_tape {R r : Nat} {c : CState} {s t : Brainfuck.State}
    (h : Matches R c s) (hr : r < R) (_hnz : c.regs r ≠ 0)
    (hptr : t.left.length = stride R) (hout : t.output = s.output)
    (htape : ∀ p, tapeAt t p =
      if p = dataPos R (c.regs r - 1) r ∨ p = guidePos R (c.regs r - 1) r then 0
      else tapeAt s p) :
    Matches R (c.down r) t := by
  refine ⟨h.1, hptr, ?_, ?_, ?_⟩
  · rw [hout, h.2.2.1]
    rfl
  · intro r' hr'
    rw [htape, if_neg]
    · exact h.2.2.2.1 r' hr'
    · push Not
      exact ⟨guard_ne_dataPos h.1 hr' hr,
        guard_ne_guidePos h.1 hr' hr⟩
  · intro r' hr' row
    constructor
    · rw [htape]
      have hcross : dataPos R row r' ≠ guidePos R (c.regs r - 1) r :=
        dataPos_ne_guidePos h.1 hr' hr
      by_cases heq : dataPos R row r' = dataPos R (c.regs r - 1) r
      · have hi := dataPos_inj h.1 hr' hr heq
        rw [if_pos (Or.inl heq)]
        rcases hi with ⟨hrow, hrr⟩
        subst r'
        subst row
        simp [CState.down]
      · rw [if_neg (by simp [heq, hcross])]
        rw [(h.2.2.2.2 r' hr' row).1]
        by_cases hrr : r' = r
        · subst r'
          have hrow : row ≠ c.regs r - 1 := by
            intro hrow
            exact heq (by simp [hrow])
          simp only [CState.down_regs_self]
          by_cases hlt : row < c.regs r
          · by_cases hlt' : row < c.regs r - 1
            · rw [if_pos hlt, if_pos hlt']
            · exfalso; omega
          · rw [if_neg hlt, if_neg (by omega)]
        · simp [CState.down, Function.update_of_ne hrr]
    · rw [htape]
      have hcross : guidePos R row r' ≠ dataPos R (c.regs r - 1) r :=
        (dataPos_ne_guidePos h.1 hr hr').symm
      by_cases heq : guidePos R row r' = guidePos R (c.regs r - 1) r
      · have hi := guidePos_inj h.1 hr' hr heq
        rw [if_pos (Or.inr heq)]
        rcases hi with ⟨hrow, hrr⟩
        subst r'
        subst row
        simp [CState.down]
      · rw [if_neg (by simp [heq, hcross])]
        rw [(h.2.2.2.2 r' hr' row).2]
        by_cases hrr : r' = r
        · subst r'
          have hrow : row ≠ c.regs r - 1 := by
            intro hrow
            exact heq (by simp [hrow])
          simp only [CState.down_regs_self]
          by_cases hlt : row < c.regs r
          · by_cases hlt' : row < c.regs r - 1
            · rw [if_pos hlt, if_pos hlt']
            · exfalso; omega
          · rw [if_neg hlt, if_neg (by omega)]
        · simp [CState.down, Function.update_of_ne hrr]

/-! ### Scanning a unary column -/

theorem reaches_scan_right (step n : Nat) (s : Brainfuck.State) (k : List Brainfuck.Op)
    (hcell : ∀ j, j ≤ n →
      (moveRightN (step * j) s).cell = (if j < n then 1 else 0)) :
    Reaches (bfExec cfg) (.loop (rights step) :: k, s)
      (k, moveRightN (step * n) s) := by
  induction n generalizing s with
  | zero =>
    have hz : s.cell = 0 := by
      have hz₀ := hcell 0 (by omega)
      simpa [moveRightN] using hz₀
    simpa [moveRightN] using (reaches_bf_loop_zero (cfg := cfg) (k := k)
      (body := rights step) hz)
  | succ n ih =>
    have hone : s.cell ≠ 0 := by
      have := hcell 0 (by omega)
      simp only [Nat.mul_zero, moveRightN, if_pos (by omega : 0 < n + 1)] at this
      rw [this]
      decide
    have hshift : ∀ j, j ≤ n →
        (moveRightN (step * j) (moveRightN step s)).cell =
          (if j < n then 1 else 0) := by
      intro j hj
      rw [← moveRightN_add,
        show step + step * j = step * (j + 1) by simp [Nat.mul_add, Nat.add_comm]]
      have hs := hcell (j + 1) (by omega)
      simpa only [Nat.add_lt_add_iff_right] using hs
    have hloop := reaches_bf_loop_nonzero (cfg := cfg) (k := k)
      (body := rights step) hone
    have hmove := reaches_rights (cfg := cfg) step (.loop (rights step) :: k) s
    have hrest := ih (moveRightN step s) hshift
    have hchain := Reaches.trans hloop (Reaches.trans hmove hrest)
    rw [← moveRightN_add] at hchain
    simpa [Nat.mul_add, Nat.add_comm] using hchain

theorem MoveLeftN.trans {a b : Nat} {s t u : Brainfuck.State}
    (h₁ : MoveLeftN a s t) (h₂ : MoveLeftN b t u) : MoveLeftN (a + b) s u := by
  induction h₁ with
  | zero => simpa using h₂
  | succ hm _ ih =>
    rw [Nat.succ_add]
    exact .succ hm (ih h₂)

theorem reaches_scan_left (step n : Nat) (s : Brainfuck.State) (k : List Brainfuck.Op)
    (hptr : step * n ≤ s.left.length)
    (hcell : ∀ j, j ≤ n →
      tapeAt s (s.left.length - step * j) = (if j < n then 1 else 0)) :
    ∃ t, Reaches (bfExec cfg) (.loop (lefts step) :: k, s) (k, t) ∧
      MoveLeftN (step * n) s t := by
  induction n generalizing s with
  | zero =>
    have hz : s.cell = 0 := by
      rw [← tapeAt_pointer]
      have hz₀ := hcell 0 (by omega)
      simpa using hz₀
    refine ⟨s, reaches_bf_loop_zero (cfg := cfg) (k := k) (body := lefts step) hz, ?_⟩
    simpa using MoveLeftN.zero s
  | succ n ih =>
    have hone : s.cell ≠ 0 := by
      rw [← tapeAt_pointer]
      have h₁ := hcell 0 (by omega)
      simp only [Nat.mul_zero, Nat.sub_zero, if_pos (by omega : 0 < n + 1)] at h₁
      rw [h₁]
      decide
    have hsle : step ≤ s.left.length := by
      have : step * (n + 1) = step * n + step := Nat.mul_succ step n
      omega
    obtain ⟨s₁, hm⟩ := exists_moveLeftN hsle
    have hp₁ : s₁.left.length + step = s.left.length := hm.pointer
    have hptr₁ : step * n ≤ s₁.left.length := by
      have htotal : step * (n + 1) ≤ s.left.length := hptr
      rw [Nat.mul_succ] at htotal
      omega
    have hcell₁ : ∀ j, j ≤ n →
        tapeAt s₁ (s₁.left.length - step * j) = (if j < n then 1 else 0) := by
      intro j hj
      rw [hm.tapeAt]
      have hindex : s₁.left.length - step * j =
          s.left.length - step * (j + 1) := by
        have hjle : step * j ≤ s₁.left.length := by
          exact Nat.le_trans (Nat.mul_le_mul_left step hj) hptr₁
        rw [Nat.mul_succ]
        omega
      rw [hindex]
      have hs := hcell (j + 1) (by omega)
      simpa only [Nat.add_lt_add_iff_right] using hs
    obtain ⟨t, hreach, htail⟩ := ih s₁ hptr₁ hcell₁
    have hloop := reaches_bf_loop_nonzero (cfg := cfg) (k := k)
      (body := lefts step) hone
    have hmove := reaches_lefts (cfg := cfg) hm (.loop (lefts step) :: k)
    refine ⟨t, Reaches.trans hloop (Reaches.trans hmove hreach), ?_⟩
    rw [Nat.mul_succ, Nat.add_comm]
    exact MoveLeftN.trans hm htail

/-! ### Incrementing one represented counter -/

theorem reaches_inc_cmd {R r : Nat} {c : CState} {s : Brainfuck.State}
    (h : Matches R c s) (hr : r < R) (k : List Brainfuck.Op) :
    ∃ t, Reaches (bfExec cfg)
        (toReg r ++ incAt R ++ fromReg r ++ k, s) (k, t) ∧
      Matches R (c.up r) t := by
  let v := c.regs r
  let sr := moveRightN (2 * r) s
  let tail₀ := .inc :: .right :: .inc :: .loop (lefts (stride R)) ::
    (rights (stride R) ++ .left :: (fromReg r ++ k))
  have hto : Reaches (bfExec cfg)
      (toReg r ++ (incAt R ++ fromReg r ++ k), s)
      (incAt R ++ fromReg r ++ k, sr) := by
    simpa [toReg, sr] using reaches_rights (cfg := cfg) (2 * r)
      (incAt R ++ fromReg r ++ k) s
  have hscanCells : ∀ j, j ≤ v →
      (moveRightN (stride R * j) sr).cell = (if j < v then 1 else 0) := by
    intro j hj
    rw [moveRightN_cell, moveRightN_pointer, moveRightN_tapeAt]
    have hc := (h.2.2.2.2 r hr j).1
    have hp : s.left.length + 2 * r + stride R * j = dataPos R j r := by
      rw [h.2.1]
      simp only [dataPos, Nat.mul_succ]
      omega
    rw [hp]
    simpa [v] using hc
  have hscan : Reaches (bfExec cfg)
      (.loop (rights (stride R)) :: tail₀, sr)
      (tail₀, moveRightN (stride R * v) sr) :=
    reaches_scan_right (cfg := cfg) (stride R) v sr tail₀ hscanCells
  let d₀ := moveRightN (stride R * v) sr
  have hd₀pos : d₀.left.length = dataPos R v r := by
    simp only [d₀, moveRightN_pointer, sr, h.2.1]
    simp only [dataPos, Nat.mul_succ]
    omega
  have hd₀cell : d₀.cell = 0 := by
    have := hscanCells v (by omega)
    simpa [d₀] using this
  have hd₀tape (p : Nat) : tapeAt d₀ p = tapeAt s p := by
    simp only [d₀, sr]
    rw [moveRightN_tapeAt, moveRightN_tapeAt]
  let d₁ : Brainfuck.State := { d₀ with cell := d₀.cell + 1 }
  have hd₁cell : d₁.cell = 1 := by simp [d₁, hd₀cell]
  have hd₁tape (p : Nat) : tapeAt d₁ p =
      if p = dataPos R v r then 1 else tapeAt s p := by
    rw [show d₁ = { d₀ with cell := d₀.cell + 1 } from rfl, tapeAt_setCell,
      hd₀pos, hd₀tape]
    simp only [hd₀cell]
    rfl
  have hinc₁ : Reaches (bfExec cfg) (.inc :: tail₀.tail, d₀)
      (tail₀.tail, d₁) := by
    simpa [d₁] using (reaches_bf_inc (cfg := cfg) (k := tail₀.tail) (s := d₀))
  let g₀ := d₁.moveRight
  have hg₀pos : g₀.left.length = guidePos R v r := by
    simp [g₀, pointer_moveRight, d₁, hd₀pos, guidePos]
  have hg₀cell : g₀.cell = 0 := by
    rw [← tapeAt_pointer, show g₀.left.length = guidePos R v r from hg₀pos]
    simp only [g₀, tapeAt_moveRight]
    rw [hd₁tape, if_neg (dataPos_ne_guidePos h.1 hr hr).symm]
    simpa [v] using (h.2.2.2.2 r hr v).2
  have hright : Reaches (bfExec cfg) (.right :: tail₀.tail.tail, d₁)
      (tail₀.tail.tail, g₀) := by
    simpa [g₀] using
      (reaches_bf_right (cfg := cfg) (k := tail₀.tail.tail) (s := d₁))
  let g₁ : Brainfuck.State := { g₀ with cell := g₀.cell + 1 }
  have hg₁tape (p : Nat) : tapeAt g₁ p =
      if p = guidePos R v r then 1
      else if p = dataPos R v r then 1 else tapeAt s p := by
    rw [show g₁ = { g₀ with cell := g₀.cell + 1 } from rfl, tapeAt_setCell,
      hg₀pos]
    simp only [hg₀cell]
    rw [show tapeAt g₀ p = tapeAt d₁ p from tapeAt_moveRight d₁ p,
      hd₁tape]
    rfl
  have hinc₂ : Reaches (bfExec cfg) (.inc :: tail₀.tail.tail.tail, g₀)
      (tail₀.tail.tail.tail, g₁) := by
    simpa [g₁] using
      (reaches_bf_inc (cfg := cfg) (k := tail₀.tail.tail.tail) (s := g₀))
  have hleftPtr : stride R * (v + 1) ≤ g₁.left.length := by
    simp only [g₁, hg₀pos, guidePos, dataPos]
    omega
  have hleftCells : ∀ j, j ≤ v + 1 →
      tapeAt g₁ (g₁.left.length - stride R * j) =
        (if j < v + 1 then 1 else 0) := by
    intro j hj
    rw [hg₁tape]
    by_cases jz : j = 0
    · subst j
      rw [if_pos]
      · simp
      · simp [g₁, hg₀pos]
    · by_cases je : j = v + 1
      · subst j
        have hidx : g₁.left.length - stride R * (v + 1) = 2 * r + 1 := by
          simp only [g₁, hg₀pos, guidePos, dataPos]
          omega
        rw [hidx, if_neg, if_neg, h.2.2.2.1 r hr, if_neg (by omega)]
        · exact guard_ne_dataPos h.1 hr hr
        · exact guard_ne_guidePos h.1 hr hr
      · have hjv : j ≤ v := by omega
        let row := v - j
        have hidx : g₁.left.length - stride R * j = guidePos R row r := by
          rw [show g₁.left.length = stride R * (v + 1) + (2 * r + 1) by
            rw [hg₀pos]; simp [guidePos, dataPos]; omega]
          rw [slot_sub (stride R) (v + 1) (2 * r + 1) j (by omega)]
          simp only [guidePos, dataPos, row]
          have he : v + 1 - j = v - j + 1 := by omega
          rw [he]
          omega
        have hneGuide : guidePos R row r ≠ guidePos R v r := by
          intro heqg
          have hi := guidePos_inj h.1 hr hr heqg
          have : row = v := hi.1
          simp only [row] at this
          omega
        rw [hidx, if_neg hneGuide, if_neg (dataPos_ne_guidePos h.1 hr hr).symm,
          (h.2.2.2.2 r hr row).2]
        simp only [row]
        rw [if_pos (by omega), if_pos (by omega)]
  let tailL := rights (stride R) ++ .left :: (fromReg r ++ k)
  obtain ⟨guard, hback, hmoveBack⟩ := reaches_scan_left (cfg := cfg) (stride R) (v + 1)
    g₁ tailL hleftPtr hleftCells
  have hguardPos : guard.left.length = 2 * r + 1 := by
    have hp := hmoveBack.pointer
    simp only [g₁, hg₀pos, guidePos, dataPos] at hp
    rw [Nat.mul_succ] at hp
    omega
  let rowGuide := moveRightN (stride R) guard
  have htoGuide := reaches_rights (cfg := cfg) (stride R) (.left :: (fromReg r ++ k)) guard
  have hrowGuidePos : rowGuide.left.length = stride R + 2 * r + 1 := by
    rw [show rowGuide.left.length = guard.left.length + stride R by
      simp [rowGuide, moveRightN_pointer]]
    rw [hguardPos]
    omega
  obtain ⟨rowData, hmleft⟩ := exists_moveLeftN (n := 1) (s := rowGuide) (by
    rw [hrowGuidePos]; omega)
  have hleftOne := reaches_lefts (cfg := cfg) hmleft (fromReg r ++ k)
  have hrowDataPos : rowData.left.length = stride R + 2 * r := by
    have hp := hmleft.pointer
    rw [hrowGuidePos] at hp
    omega
  obtain ⟨t, hmhome⟩ := exists_moveLeftN (n := 2 * r) (s := rowData) (by
    rw [hrowDataPos]; omega)
  have hhome := reaches_lefts (cfg := cfg) hmhome k
  have htptr : t.left.length = stride R := by
    have hp := hmhome.pointer
    rw [hrowDataPos] at hp
    omega
  have httape (p : Nat) : tapeAt t p =
      if p = dataPos R v r ∨ p = guidePos R v r then 1 else tapeAt s p := by
    rw [hmhome.tapeAt, hmleft.tapeAt, moveRightN_tapeAt, hmoveBack.tapeAt, hg₁tape]
    by_cases hg : p = guidePos R v r
    · simp [hg]
    · by_cases hd : p = dataPos R v r <;> simp [hg, hd]
  have htout : t.output = s.output := by
    rw [hmhome.output, hmleft.output, moveRightN_output, hmoveBack.output]
    change d₁.moveRight.output = s.output
    have hro : d₁.moveRight.output = d₁.output := by
      cases d₁ with
      | mk left cell right input output => cases right <;> rfl
    rw [hro]
    change d₀.output = s.output
    simp only [d₀, sr, moveRightN_output]
  have hscan' : Reaches (bfExec cfg) (incAt R ++ fromReg r ++ k, sr)
      (tail₀, d₀) := by
    simpa [incAt, tail₀, List.append_assoc, d₀] using hscan
  have htotal := Reaches.trans hto
    (Reaches.trans hscan' (Reaches.trans hinc₁ (Reaches.trans hright
      (Reaches.trans hinc₂ (Reaches.trans hback
        (Reaches.trans htoGuide (Reaches.trans hleftOne hhome)))))))
  refine ⟨t, ?_, matches_up_of_tape h hr htptr htout httape⟩
  simpa [incAt, tail₀, tailL, List.append_assoc] using htotal

/-! ### Decrementing one represented counter -/

theorem reaches_dec_cmd {R r : Nat} {c : CState} {s : Brainfuck.State}
    (h : Matches R c s) (hr : r < R) (hnz : c.regs r ≠ 0)
    (k : List Brainfuck.Op) :
    ∃ t, Reaches (bfExec cfg)
        (toReg r ++ decAt R ++ fromReg r ++ k, s) (k, t) ∧
      Matches R (c.down r) t := by
  let v := c.regs r
  let q := v - 1
  let sr := moveRightN (2 * r) s
  let tailAfter := rights (stride R) ++ .left :: (fromReg r ++ k)
  let tailLoop := .loop (lefts (stride R)) :: tailAfter
  let tailBeforeLoop := lefts (stride R) ++ tailLoop
  let tailDecGuide := .dec :: tailBeforeLoop
  let tailRight := .right :: tailDecGuide
  let tailDecData := .dec :: tailRight
  let tail₀ := lefts (stride R) ++ tailDecData
  have hto : Reaches (bfExec cfg)
      (toReg r ++ (decAt R ++ fromReg r ++ k), s)
      (decAt R ++ fromReg r ++ k, sr) := by
    simpa [toReg, sr] using reaches_rights (cfg := cfg) (2 * r)
      (decAt R ++ fromReg r ++ k) s
  have hscanCells : ∀ j, j ≤ v →
      (moveRightN (stride R * j) sr).cell = (if j < v then 1 else 0) := by
    intro j hj
    rw [moveRightN_cell, moveRightN_pointer, moveRightN_tapeAt]
    have hc := (h.2.2.2.2 r hr j).1
    have hp : s.left.length + 2 * r + stride R * j = dataPos R j r := by
      rw [h.2.1]
      simp only [dataPos, Nat.mul_succ]
      omega
    rw [hp]
    simpa [v] using hc
  have hscan : Reaches (bfExec cfg)
      (.loop (rights (stride R)) :: tail₀, sr)
      (tail₀, moveRightN (stride R * v) sr) :=
    reaches_scan_right (cfg := cfg) (stride R) v sr tail₀ hscanCells
  let d₀ := moveRightN (stride R * v) sr
  have hd₀pos : d₀.left.length = dataPos R v r := by
    simp only [d₀, moveRightN_pointer, sr, h.2.1]
    simp only [dataPos, Nat.mul_succ]
    omega
  have hd₀tape (p : Nat) : tapeAt d₀ p = tapeAt s p := by
    simp only [d₀, sr]
    rw [moveRightN_tapeAt, moveRightN_tapeAt]
  have hstepLeft : stride R ≤ d₀.left.length := by
    rw [hd₀pos]
    unfold dataPos
    have hm : stride R ≤ stride R * (v + 1) := by
      have := Nat.mul_le_mul_left (stride R) (show 1 ≤ v + 1 by omega)
      simpa using this
    exact Nat.le_trans hm (Nat.le_add_right _ _)
  obtain ⟨dLast, hmLast⟩ := exists_moveLeftN hstepLeft
  have htoLast := reaches_lefts (cfg := cfg) hmLast tailDecData
  have hdLastPos : dLast.left.length = dataPos R q r := by
    have hp := hmLast.pointer
    rw [hd₀pos] at hp
    have hq : q + 1 = v := by simp only [q]; omega
    have hpos : dataPos R v r = dataPos R q r + stride R := by
      simp only [dataPos]
      rw [← hq, Nat.mul_succ]
      omega
    rw [hpos] at hp
    omega
  have hdLastCell : dLast.cell = 1 := by
    rw [← tapeAt_pointer, hdLastPos, hmLast.tapeAt, hd₀tape]
    have hc := (h.2.2.2.2 r hr q).1
    rw [hc, if_pos (by simp [q]; omega)]
  let d₁ : Brainfuck.State := { dLast with cell := dLast.cell - 1 }
  have hd₁tape (p : Nat) : tapeAt d₁ p =
      if p = dataPos R q r then 0 else tapeAt s p := by
    rw [show d₁ = { dLast with cell := dLast.cell - 1 } from rfl,
      tapeAt_setCell, hdLastPos]
    simp only [hdLastCell]
    rw [hmLast.tapeAt, hd₀tape]
    rfl
  have hdecData : Reaches (bfExec cfg) (.dec :: tailRight, dLast) (tailRight, d₁) := by
    simpa [d₁] using (reaches_bf_dec (cfg := cfg) (k := tailRight) (s := dLast))
  let g₀ := d₁.moveRight
  have hg₀pos : g₀.left.length = guidePos R q r := by
    simp [g₀, pointer_moveRight, d₁, hdLastPos, guidePos]
  have hg₀cell : g₀.cell = 1 := by
    rw [← tapeAt_pointer, hg₀pos]
    simp only [g₀, tapeAt_moveRight]
    rw [hd₁tape, if_neg (dataPos_ne_guidePos h.1 hr hr).symm]
    have hc := (h.2.2.2.2 r hr q).2
    rw [hc, if_pos (by simp [q]; omega)]
  have hright : Reaches (bfExec cfg) (.right :: tailDecGuide, d₁)
      (tailDecGuide, g₀) := by
    simpa [g₀] using
      (reaches_bf_right (cfg := cfg) (k := tailDecGuide) (s := d₁))
  let g₁ : Brainfuck.State := { g₀ with cell := g₀.cell - 1 }
  have hg₁tape (p : Nat) : tapeAt g₁ p =
      if p = guidePos R q r then 0
      else if p = dataPos R q r then 0 else tapeAt s p := by
    rw [show g₁ = { g₀ with cell := g₀.cell - 1 } from rfl,
      tapeAt_setCell, hg₀pos]
    simp only [hg₀cell]
    rw [show tapeAt g₀ p = tapeAt d₁ p from tapeAt_moveRight d₁ p,
      hd₁tape]
    rfl
  have hdecGuide : Reaches (bfExec cfg) (.dec :: tailBeforeLoop, g₀)
      (tailBeforeLoop, g₁) := by
    simpa [g₁] using
      (reaches_bf_dec (cfg := cfg) (k := tailBeforeLoop) (s := g₀))
  have hpreLeft : stride R ≤ g₁.left.length := by
    rw [show g₁.left.length = guidePos R q r from hg₀pos]
    unfold guidePos dataPos
    have hm : stride R ≤ stride R * (q + 1) := by
      have := Nat.mul_le_mul_left (stride R) (show 1 ≤ q + 1 by omega)
      simpa using this
    omega
  obtain ⟨pre, hmPre⟩ := exists_moveLeftN hpreLeft
  have htoPre := reaches_lefts (cfg := cfg) hmPre tailLoop
  have hprePos : pre.left.length = stride R * q + 2 * r + 1 := by
    have hp := hmPre.pointer
    rw [show g₁.left.length = guidePos R q r from hg₀pos] at hp
    simp only [guidePos, dataPos, Nat.mul_succ] at hp
    omega
  have hbackPtr : stride R * q ≤ pre.left.length := by rw [hprePos]; omega
  have hbackCells : ∀ j, j ≤ q →
      tapeAt pre (pre.left.length - stride R * j) = (if j < q then 1 else 0) := by
    intro j hj
    rw [hmPre.tapeAt, hg₁tape]
    have hidx : pre.left.length - stride R * j =
        stride R * (q - j) + 2 * r + 1 := by
      rw [hprePos]
      rw [show stride R * q + 2 * r + 1 = stride R * q + (2 * r + 1) by omega,
        slot_sub (stride R) q (2 * r + 1) j hj]
      omega
    rw [hidx]
    by_cases je : j = q
    · subst j
      simp only [Nat.sub_self, Nat.mul_zero, Nat.zero_add]
      rw [if_neg (guard_ne_guidePos h.1 hr hr),
        if_neg (guard_ne_dataPos h.1 hr hr), h.2.2.2.1 r hr, if_neg (by omega)]
    · let row := q - j - 1
      have hjq : j < q := by omega
      have hrow : q - j = row + 1 := by simp only [row]; omega
      rw [hrow]
      have hpos : stride R * (row + 1) + 2 * r + 1 = guidePos R row r := by
        simp [guidePos, dataPos]
      rw [hpos]
      have hneGuide : guidePos R row r ≠ guidePos R q r := by
        intro heq
        have hi := guidePos_inj h.1 hr hr heq
        simp only [row] at hi
        omega
      rw [if_neg hneGuide, if_neg (dataPos_ne_guidePos h.1 hr hr).symm,
        (h.2.2.2.2 r hr row).2]
      have hrowv : row < v := by simp only [row, q, v]; omega
      rw [if_pos hrowv, if_pos hjq]
  obtain ⟨guard, hback, hmBack⟩ := reaches_scan_left (cfg := cfg) (stride R) q pre
    tailAfter hbackPtr hbackCells
  have hguardPos : guard.left.length = 2 * r + 1 := by
    have hp := hmBack.pointer
    rw [hprePos] at hp
    omega
  let rowGuide := moveRightN (stride R) guard
  have htoGuide := reaches_rights (cfg := cfg) (stride R) (.left :: (fromReg r ++ k)) guard
  have hrowGuidePos : rowGuide.left.length = stride R + 2 * r + 1 := by
    rw [show rowGuide.left.length = guard.left.length + stride R by
      simp [rowGuide, moveRightN_pointer]]
    rw [hguardPos]
    omega
  obtain ⟨rowData, hmleft⟩ := exists_moveLeftN (n := 1) (s := rowGuide) (by
    rw [hrowGuidePos]; omega)
  have hleftOne := reaches_lefts (cfg := cfg) hmleft (fromReg r ++ k)
  have hrowDataPos : rowData.left.length = stride R + 2 * r := by
    have hp := hmleft.pointer
    rw [hrowGuidePos] at hp
    omega
  obtain ⟨t, hmhome⟩ := exists_moveLeftN (n := 2 * r) (s := rowData) (by
    rw [hrowDataPos]; omega)
  have hhome := reaches_lefts (cfg := cfg) hmhome k
  have htptr : t.left.length = stride R := by
    have hp := hmhome.pointer
    rw [hrowDataPos] at hp
    omega
  have httape (p : Nat) : tapeAt t p =
      if p = dataPos R q r ∨ p = guidePos R q r then 0 else tapeAt s p := by
    rw [hmhome.tapeAt, hmleft.tapeAt, moveRightN_tapeAt, hmBack.tapeAt,
      hmPre.tapeAt, hg₁tape]
    by_cases hg : p = guidePos R q r
    · simp [hg]
    · by_cases hd : p = dataPos R q r <;> simp [hg, hd]
  have htout : t.output = s.output := by
    rw [hmhome.output, hmleft.output, moveRightN_output, hmBack.output, hmPre.output]
    change d₁.moveRight.output = s.output
    have hro : d₁.moveRight.output = d₁.output := by
      cases d₁ with
      | mk left cell right input output => cases right <;> rfl
    rw [hro]
    change dLast.output = s.output
    rw [hmLast.output]
    simp only [d₀, sr, moveRightN_output]
  have hscan' : Reaches (bfExec cfg) (decAt R ++ fromReg r ++ k, sr)
      (tail₀, d₀) := by
    simpa [decAt, tail₀, tailDecData, tailRight, tailDecGuide, tailBeforeLoop,
      tailLoop, tailAfter, List.append_assoc, d₀] using hscan
  have htotal := Reaches.trans hto
    (Reaches.trans hscan' (Reaches.trans htoLast (Reaches.trans hdecData
      (Reaches.trans hright (Reaches.trans hdecGuide (Reaches.trans htoPre
        (Reaches.trans hback (Reaches.trans htoGuide
          (Reaches.trans hleftOne hhome)))))))))
  refine ⟨t, ?_, matches_down_of_tape h hr hnz htptr htout ?_⟩
  · simpa [decAt, tail₀, tailDecData, tailRight, tailDecGuide, tailBeforeLoop,
      tailLoop, tailAfter, List.append_assoc] using htotal
  · simpa [q, v] using httape

/-! ## Correctness of lowering structured counter code -/

theorem matches_right_left {R : Nat} {c : CState} {s t : Brainfuck.State}
    (h : Matches R c s) (n : Nat) (hm : MoveLeftN n (moveRightN n s) t) :
    Matches R c t := by
  refine ⟨h.1, ?_, ?_, ?_, ?_⟩
  · have hp := hm.pointer
    rw [moveRightN_pointer] at hp
    have hs := h.2.1
    omega
  · rw [hm.output, moveRightN_output, h.2.2.1]
  · intro r hr
    rw [hm.tapeAt, moveRightN_tapeAt]
    exact h.2.2.2.1 r hr
  · intro r hr row
    constructor
    · rw [hm.tapeAt, moveRightN_tapeAt]
      exact (h.2.2.2.2 r hr row).1
    · rw [hm.tapeAt, moveRightN_tapeAt]
      exact (h.2.2.2.2 r hr row).2

/-- A complete counter-machine derivation is simulated by the lowered
Brainfuck code, with any continuation appended. -/
theorem ev_lower {R : Nat} {code : Code} {c t : CState}
    (hev : Ev R code c t) {s : Brainfuck.State} (hm : Matches R c s)
    (k : List Brainfuck.Op) :
    ∃ u, Reaches (bfExec cfg) (lower R code ++ k, s) (k, u) ∧ Matches R t u := by
  induction hev generalizing s with
  | nil =>
    exact ⟨s, by simpa [lower] using Reaches.refl (bfExec cfg) (k, s), hm⟩
  | inc hr _ ih =>
    obtain ⟨s₁, hinc, hm₁⟩ := reaches_inc_cmd (cfg := cfg) hm hr (lower R _ ++ k)
    obtain ⟨u, hrest, hmu⟩ := ih hm₁
    refine ⟨u, ?_, hmu⟩
    simpa [lower, List.append_assoc] using Reaches.trans hinc hrest
  | dec hr hnz _ ih =>
    obtain ⟨s₁, hdec, hm₁⟩ := reaches_dec_cmd (cfg := cfg) hm hr hnz (lower R _ ++ k)
    obtain ⟨u, hrest, hmu⟩ := ih hm₁
    refine ⟨u, ?_, hmu⟩
    simpa [lower, List.append_assoc] using Reaches.trans hdec hrest
  | emit hev ih =>
    rename_i cs s₀ t₀
    let s₁ : Brainfuck.State := { s with output := s.output.push s.cell }
    have hout := reaches_bf_output (cfg := cfg) (k := lower R cs ++ k) (s := s)
    obtain ⟨u, hrest, hmu⟩ := ih (Matches.output_push hm)
    refine ⟨u, ?_, hmu⟩
    simpa [lower, List.append_assoc] using Reaches.trans hout hrest
  | loopZ hr hz hev ih =>
    rename_i r body cs c₀ t₀
    let cont := fromReg r ++ lower R cs ++ k
    let sr := moveRightN (2 * r) s
    have hto : Reaches (bfExec cfg)
        (toReg r ++ (.loop (fromReg r ++ lower R body ++ toReg r) :: cont), s)
        (.loop (fromReg r ++ lower R body ++ toReg r) :: cont, sr) := by
      simpa [toReg, sr] using reaches_rights (cfg := cfg) (2 * r)
        (.loop (fromReg r ++ lower R body ++ toReg r) :: cont) s
    have hcell : sr.cell = 0 := by
      have hc := Matches.cell_at_reg hm hr
      simpa [sr, hz] using hc
    have hloop : Reaches (bfExec cfg)
        (.loop (fromReg r ++ lower R body ++ toReg r) :: cont, sr) (cont, sr) :=
      reaches_bf_loop_zero (cfg := cfg) hcell
    have hle : 2 * r ≤ sr.left.length := by
      simp only [sr, moveRightN_pointer, hm.2.1]
      omega
    obtain ⟨sb, hmb⟩ := exists_moveLeftN hle
    have hback : Reaches (bfExec cfg) (cont, sr) (lower R cs ++ k, sb) := by
      simpa [cont, fromReg] using reaches_lefts (cfg := cfg) hmb (lower R cs ++ k)
    have hmbm : Matches R c₀ sb := matches_right_left hm (2 * r) hmb
    obtain ⟨u, hrest, hmu⟩ := ih hmbm
    refine ⟨u, ?_, hmu⟩
    have htotal := Reaches.trans hto (Reaches.trans hloop (Reaches.trans hback hrest))
    simpa [lower, cont, List.append_assoc] using htotal
  | loopS hr hnz hev ih =>
    rename_i r bodyCode cs c₀ t₀
    let body := fromReg r ++ lower R bodyCode ++ toReg r
    let cont := fromReg r ++ lower R cs ++ k
    let sr := moveRightN (2 * r) s
    have hto : Reaches (bfExec cfg)
        (toReg r ++ (.loop body :: cont), s) (.loop body :: cont, sr) := by
      simpa [toReg, sr] using reaches_rights (cfg := cfg) (2 * r) (.loop body :: cont) s
    have hcell : sr.cell ≠ 0 := by
      have hc := Matches.cell_at_reg hm hr
      rw [if_pos (Nat.pos_of_ne_zero hnz)] at hc
      rw [hc]
      decide
    have hloop : Reaches (bfExec cfg) (.loop body :: cont, sr)
        (body ++ .loop body :: cont, sr) := reaches_bf_loop_nonzero (cfg := cfg) hcell
    have hle : 2 * r ≤ sr.left.length := by
      simp only [sr, moveRightN_pointer, hm.2.1]
      omega
    obtain ⟨sb, hmb⟩ := exists_moveLeftN hle
    have hback : Reaches (bfExec cfg) (body ++ .loop body :: cont, sr)
        (lower R (bodyCode ++ .loop r bodyCode :: cs) ++ k, sb) := by
      have hb := reaches_lefts (cfg := cfg) hmb
        (lower R (bodyCode ++ .loop r bodyCode :: cs) ++ k)
      simpa [body, cont, fromReg, lower_append, lower, List.append_assoc] using hb
    have hmbm : Matches R c₀ sb := matches_right_left hm (2 * r) hmb
    obtain ⟨u, hrest, hmu⟩ := ih hmbm
    refine ⟨u, ?_, hmu⟩
    have htotal := Reaches.trans hto (Reaches.trans hloop (Reaches.trans hback hrest))
    simpa [lower, body, cont, List.append_assoc] using htotal


end Langlib.Computability.URMBrainfuck
