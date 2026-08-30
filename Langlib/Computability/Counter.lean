import Langlib.Common.Computability
import Langlib.Computability.URM

/-!
# The structured counter machine, and a URM compiled into it

Every completeness proof in the library has the same first half: turn an
unlimited register machine, whose control is a program counter and a
conditional jump, into something with *structured* control, which is what a
target language usually offers. That half is target independent, so it lives
here rather than being written once per language.

`Cmd` is a register machine with increment, decrement, one output byte, and
`loop r b`, which runs `b` while register `r` is nonzero. `Ev` is its
big-step semantics, `counterProgram` is the compiler from a URM program and
its input vector, and `counterProgram_spec` is the simulation: whenever the
URM halts with `result` in register 0, the counter program runs from the
all-zero state to a state that has emitted exactly `result` bytes.

A backend therefore has only to interpret four commands. Brainfuck lays the
registers out as unary columns on the tape
(`Langlib/Computability/Brainfuck.lean`); Unlambda and SKI hold them in a
combinator tuple (`Langlib/Computability/Unlambda.lean`).

`dec` on a zero register has no rule: the semantics below is a big-step
relation, and a program that decrements a zero register simply has no
derivation. That is the discipline the brainfuck code needs, because the code
emitted for `dec` walks one cell down a unary run and would step onto the
guard row if the run were empty, and it costs the other backends nothing.
-/

namespace Langlib.Computability.Counter

open Langlib.Common

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

/-- Increasing the register bound preserves a derivation. -/
theorem Ev.mono {R R' : Nat} (hRR : R ≤ R') {code : Code} {s t : CState}
    (h : Ev R code s t) : Ev R' code s t := by
  induction h with
  | nil => exact Ev.nil
  | inc hr _ ih => exact Ev.inc (lt_of_lt_of_le hr hRR) ih
  | dec hr hnz _ ih => exact Ev.dec (lt_of_lt_of_le hr hRR) hnz ih
  | emit _ ih => exact Ev.emit ih
  | loopZ hr hz _ ih => exact Ev.loopZ (lt_of_lt_of_le hr hRR) hz ih
  | loopS hr hnz _ ih => exact Ev.loopS (lt_of_lt_of_le hr hRR) hnz ih

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

/-- Consecutive guarded blocks, numbered from `k`. -/
def dispatchBlocks (B : Nat) : Nat → List Cslib.URM.Instr → Code
  | _, [] => []
  | k, i :: is => dispatchBlock B k i ++ dispatchBlocks B (k + 1) is

theorem ScratchClean.aux {B : Nat} {w : Nat → Nat} (h : ScratchClean B w) :
    AuxClean B w := ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
      h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

/-- Once a block has matched and cleared the saved counter, all later blocks
are misses and preserve the selected instruction's result. -/
theorem dispatchBlocks_zero {B k : Nat} (is : List Cslib.URM.Instr)
    (σ : Cslib.URM.Regs) (s : CState) (hsrc : SourceMatches B s.regs σ)
    (haux : AuxClean B s.regs) (hsaved : s.regs (savedReg B) = 0) :
    ∃ w', Ev (counterBound B) (dispatchBlocks B k is) s ⟨w', s.out⟩ ∧
      SourceMatches B w' σ ∧ w' (pcReg B) = s.regs (pcReg B) ∧
      w' (savedReg B) = 0 ∧ AuxClean B w' := by
  induction is generalizing k s with
  | nil => exact ⟨s.regs, Ev.nil, hsrc, rfl, hsaved, haux⟩
  | cons i is ih =>
    have hmiss : s.regs (savedReg B) ≠ k + 1 := by omega
    obtain ⟨w₁, h₁, h₁src, h₁pc, h₁saved, h₁aux⟩ :=
      dispatchBlock_miss i σ s hsrc haux hmiss
    let s₁ : CState := ⟨w₁, s.out⟩
    have h₁saved0 : s₁.regs (savedReg B) = 0 := by
      change w₁ (savedReg B) = 0
      rw [h₁saved, hsaved]
    obtain ⟨w₂, h₂, h₂src, h₂pc, h₂saved, h₂aux⟩ :=
      ih (k := k + 1) s₁ h₁src h₁aux h₁saved0
    refine ⟨w₂, ?_, h₂src, ?_, h₂saved, h₂aux⟩
    · exact h₁.append h₂
    · rw [h₂pc]
      exact h₁pc

/-- A scan starting at block number `k` selects the instruction at list
offset `d`, then all remaining blocks miss because the saved counter is zero. -/
theorem dispatchBlocks_find {B k d : Nat} {is : List Cslib.URM.Instr}
    {i : Cslib.URM.Instr} (hget : is[d]? = some i) (hmax : i.maxRegister < B)
    (σ : Cslib.URM.Regs) (s : CState) (hsrc : SourceMatches B s.regs σ)
    (hpc : s.regs (pcReg B) = 0) (haux : AuxClean B s.regs)
    (hsaved : s.regs (savedReg B) = k + d + 1) :
    ∃ w', Ev (counterBound B) (dispatchBlocks B k is) s ⟨w', s.out⟩ ∧
      SourceMatches B w' (instrNextRegs i σ) ∧
      w' (pcReg B) = instrNextPC (k + d) i σ + 1 ∧ ScratchClean B w' := by
  induction d generalizing k is s with
  | zero =>
    cases is with
    | nil => simp at hget
    | cons head tail =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
      subst head
      have hhit : s.regs (savedReg B) = k + 1 := by simpa using hsaved
      obtain ⟨w₁, h₁, h₁src, h₁pc, h₁clean⟩ :=
        dispatchBlock_hit i σ hmax s hsrc hpc haux hhit
      let s₁ : CState := ⟨w₁, s.out⟩
      obtain ⟨w₂, h₂, h₂src, h₂pc, h₂saved, h₂aux⟩ :=
        dispatchBlocks_zero (B := B) (k := k + 1) tail (instrNextRegs i σ) s₁
          h₁src h₁clean.aux h₁clean.1
      refine ⟨w₂, h₁.append h₂, h₂src, ?_, ?_⟩
      · rw [h₂pc]
        simpa using h₁pc
      · exact ⟨h₂saved, h₂aux.1, h₂aux.2.1, h₂aux.2.2.1,
          h₂aux.2.2.2.1, h₂aux.2.2.2.2.1, h₂aux.2.2.2.2.2⟩
  | succ d ih =>
    cases is with
    | nil => simp at hget
    | cons head tail =>
      have hget' : tail[d]? = some i := by simpa using hget
      have hmiss : s.regs (savedReg B) ≠ k + 1 := by
        rw [hsaved]
        omega
      obtain ⟨w₁, h₁, h₁src, h₁pc, h₁saved, h₁aux⟩ :=
        dispatchBlock_miss head σ s hsrc haux hmiss
      let s₁ : CState := ⟨w₁, s.out⟩
      have h₁pc0 : s₁.regs (pcReg B) = 0 := by
        change w₁ (pcReg B) = 0
        rw [h₁pc, hpc]
      have h₁saved' : s₁.regs (savedReg B) = (k + 1) + d + 1 := by
        change w₁ (savedReg B) = _
        rw [h₁saved, hsaved]
        omega
      obtain ⟨w₂, h₂, h₂src, h₂pc, h₂clean⟩ :=
        ih (k := k + 1) (is := tail) hget' s₁ h₁src h₁pc0 h₁aux h₁saved'
      refine ⟨w₂, h₁.append h₂, h₂src, ?_, h₂clean⟩
      simpa only [show k + 1 + d = k + (d + 1) by omega] using h₂pc

/-- Every instruction in a source program uses a low counter register. -/
def ProgramBelow (B : Nat) (P : Cslib.URM.Program) : Prop :=
  ∀ i ∈ P, i.maxRegister < B

/-- One pass through the dispatcher. -/
def dispatchStep (B : Nat) (P : Cslib.URM.Program) : Code :=
  move (pcReg B) (savedReg B) ++ dispatchBlocks B 0 P

theorem step_arithmetic {P : Cslib.URM.Program} {u u' : Cslib.URM.State}
    (h : Cslib.URM.Step P u u') :
    ∃ i, P[u.pc]? = some i ∧
      u'.pc = instrNextPC u.pc i u.regs ∧
      u'.regs = instrNextRegs i u.regs := by
  cases h with
  | zero hi => exact ⟨.Z _, hi, rfl, rfl⟩
  | succ hi => exact ⟨.S _, hi, rfl, rfl⟩
  | transfer hi => exact ⟨.T _ _, hi, rfl, rfl⟩
  | jump_eq hi heq =>
    refine ⟨.J _ _ _, hi, ?_, rfl⟩
    simp [instrNextPC, heq]
  | jump_ne hi hne =>
    refine ⟨.J _ _ _, hi, ?_, rfl⟩
    simp [instrNextPC, hne]

/-- One URM transition becomes one complete dispatcher pass. -/
theorem dispatchStep_spec {B : Nat} {P : Cslib.URM.Program}
    (hbelow : ProgramBelow B P) {u u' : Cslib.URM.State}
    (hstep : Cslib.URM.Step P u u') (s : CState)
    (hsrc : SourceMatches B s.regs u.regs)
    (hpc : s.regs (pcReg B) = u.pc + 1) (hclean : ScratchClean B s.regs) :
    ∃ w', Ev (counterBound B) (dispatchStep B P) s ⟨w', s.out⟩ ∧
      SourceMatches B w' u'.regs ∧ w' (pcReg B) = u'.pc + 1 ∧
      ScratchClean B w' := by
  obtain ⟨i, hget, hnextpc, hnextregs⟩ := step_arithmetic hstep
  have himem : i ∈ P := List.mem_of_getElem? hget
  have himax : i.maxRegister < B := hbelow i himem
  have hp : pcReg B < counterBound B := by simp [pcReg, counterBound]
  have hsavedB : savedReg B < counterBound B := by simp [savedReg, counterBound]
  obtain ⟨wM, hM, hMpc, hMsaved, hMfr⟩ := move_spec hp hsavedB
    (by simp [pcReg, savedReg]) (s.regs (pcReg B)) s rfl
  let sM : CState := ⟨wM, s.out⟩
  have hMsrc : SourceMatches B wM u.regs := by
    intro r hr
    rw [hMfr r (by simp [pcReg]; omega) (by simp [savedReg]; omega)]
    exact hsrc r hr
  have hMpc0 : sM.regs (pcReg B) = 0 := hMpc
  have hMsaved' : sM.regs (savedReg B) = 0 + u.pc + 1 := by
    change wM (savedReg B) = 0 + u.pc + 1
    rw [hMsaved, hclean.1, hpc]
    omega
  have hMaux : AuxClean B wM := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hMfr _ (by simp [cmpXReg, pcReg]) (by simp [cmpXReg, savedReg])]
      exact hclean.2.1
    · rw [hMfr _ (by simp [cmpYReg, pcReg]) (by simp [cmpYReg, savedReg])]
      exact hclean.2.2.1
    · rw [hMfr _ (by simp [tmpReg, pcReg]) (by simp [tmpReg, savedReg])]
      exact hclean.2.2.2.1
    · rw [hMfr _ (by simp [gateReg, pcReg]) (by simp [gateReg, savedReg])]
      exact hclean.2.2.2.2.1
    · rw [hMfr _ (by simp [eqReg, pcReg]) (by simp [eqReg, savedReg])]
      exact hclean.2.2.2.2.2.1
    · rw [hMfr _ (by simp [fallReg, pcReg]) (by simp [fallReg, savedReg])]
      exact hclean.2.2.2.2.2.2
  obtain ⟨wD, hD, hDsrc, hDpc, hDclean⟩ := dispatchBlocks_find
    (B := B) (k := 0) (d := u.pc) (is := P) hget himax u.regs sM
      hMsrc hMpc0 hMaux (by simpa using hMsaved')
  refine ⟨wD, hM.append hD, ?_, ?_, hDclean⟩
  · simpa [hnextregs]
  · simpa [hnextpc] using hDpc

/-- A saved counter beyond the last block misses the entire dispatch chain. -/
theorem dispatchBlocks_large {B k : Nat} (is : List Cslib.URM.Instr)
    (σ : Cslib.URM.Regs) (s : CState) (hsrc : SourceMatches B s.regs σ)
    (haux : AuxClean B s.regs) (hlarge : k + is.length < s.regs (savedReg B)) :
    ∃ w', Ev (counterBound B) (dispatchBlocks B k is) s ⟨w', s.out⟩ ∧
      SourceMatches B w' σ ∧ w' (pcReg B) = s.regs (pcReg B) ∧
      w' (savedReg B) = s.regs (savedReg B) ∧ AuxClean B w' := by
  induction is generalizing k s with
  | nil => exact ⟨s.regs, Ev.nil, hsrc, rfl, rfl, haux⟩
  | cons i is ih =>
    have hmiss : s.regs (savedReg B) ≠ k + 1 := by
      simp only [List.length_cons] at hlarge
      omega
    obtain ⟨w₁, h₁, h₁src, h₁pc, h₁saved, h₁aux⟩ :=
      dispatchBlock_miss i σ s hsrc haux hmiss
    let s₁ : CState := ⟨w₁, s.out⟩
    have hlarge' : (k + 1) + is.length < s₁.regs (savedReg B) := by
      change _ < w₁ (savedReg B)
      rw [h₁saved]
      simp only [List.length_cons] at hlarge
      omega
    obtain ⟨w₂, h₂, h₂src, h₂pc, h₂saved, h₂aux⟩ :=
      ih (k := k + 1) s₁ h₁src h₁aux hlarge'
    refine ⟨w₂, h₁.append h₂, h₂src, ?_, ?_, h₂aux⟩
    · rw [h₂pc]
      exact h₁pc
    · rw [h₂saved]
      exact h₁saved

/-- A halted source state makes one final pass, finds no block, and clears
the active program counter to zero. -/
theorem dispatchStep_halted {B : Nat} {P : Cslib.URM.Program}
    {u : Cslib.URM.State} (hhalt : u.isHalted P) (s : CState)
    (hsrc : SourceMatches B s.regs u.regs)
    (hpc : s.regs (pcReg B) = u.pc + 1) (hclean : ScratchClean B s.regs) :
    ∃ w', Ev (counterBound B) (dispatchStep B P) s ⟨w', s.out⟩ ∧
      SourceMatches B w' u.regs ∧ w' (pcReg B) = 0 := by
  have hp : pcReg B < counterBound B := by simp [pcReg, counterBound]
  have hsavedB : savedReg B < counterBound B := by simp [savedReg, counterBound]
  obtain ⟨wM, hM, hMpc, hMsaved, hMfr⟩ := move_spec hp hsavedB
    (by simp [pcReg, savedReg]) (s.regs (pcReg B)) s rfl
  let sM : CState := ⟨wM, s.out⟩
  have hMsrc : SourceMatches B wM u.regs := by
    intro r hr
    rw [hMfr r (by simp [pcReg]; omega) (by simp [savedReg]; omega)]
    exact hsrc r hr
  have hMaux : AuxClean B wM := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hMfr _ (by simp [cmpXReg, pcReg]) (by simp [cmpXReg, savedReg])]
      exact hclean.2.1
    · rw [hMfr _ (by simp [cmpYReg, pcReg]) (by simp [cmpYReg, savedReg])]
      exact hclean.2.2.1
    · rw [hMfr _ (by simp [tmpReg, pcReg]) (by simp [tmpReg, savedReg])]
      exact hclean.2.2.2.1
    · rw [hMfr _ (by simp [gateReg, pcReg]) (by simp [gateReg, savedReg])]
      exact hclean.2.2.2.2.1
    · rw [hMfr _ (by simp [eqReg, pcReg]) (by simp [eqReg, savedReg])]
      exact hclean.2.2.2.2.2.1
    · rw [hMfr _ (by simp [fallReg, pcReg]) (by simp [fallReg, savedReg])]
      exact hclean.2.2.2.2.2.2
  have hMlarge : P.length < sM.regs (savedReg B) := by
    change P.length < wM (savedReg B)
    rw [hMsaved, hclean.1, hpc]
    have hh : P.length ≤ u.pc := by simpa [Cslib.URM.State.isHalted] using hhalt
    omega
  obtain ⟨wD, hD, hDsrc, hDpc, hDsave, hDaux⟩ :=
    dispatchBlocks_large (B := B) (k := 0) P u.regs sM hMsrc hMaux
      (by simpa using hMlarge)
  refine ⟨wD, hM.append hD, hDsrc, ?_⟩
  rw [hDpc]
  exact hMpc

/-- The repeated dispatcher loop. -/
def runCode (B : Nat) (P : Cslib.URM.Program) : Code :=
  [Cmd.loop (pcReg B) (dispatchStep B P)]

/-- A finite source run followed by a halted state becomes the complete
counter-machine dispatcher loop. -/
theorem steps_runCode {B : Nat} {P : Cslib.URM.Program}
    (hbelow : ProgramBelow B P) {u v : Cslib.URM.State}
    (hsteps : Cslib.URM.Steps P u v) (hhalt : v.isHalted P)
    (s : CState) (hsrc : SourceMatches B s.regs u.regs)
    (hpc : s.regs (pcReg B) = u.pc + 1) (hclean : ScratchClean B s.regs) :
    ∃ w', Ev (counterBound B) (runCode B P) s ⟨w', s.out⟩ ∧
      SourceMatches B w' v.regs ∧ w' (pcReg B) = 0 := by
  induction hsteps using Relation.ReflTransGen.head_induction_on generalizing s with
  | refl =>
    obtain ⟨wD, hD, hDsrc, hDpc⟩ := dispatchStep_halted hhalt s hsrc hpc hclean
    let sD : CState := ⟨wD, s.out⟩
    have hloopZ : Ev (counterBound B) (runCode B P) sD sD :=
      Ev.loopZ (by simp [pcReg, counterBound]) hDpc Ev.nil
    have hpnz : s.regs (pcReg B) ≠ 0 := by rw [hpc]; omega
    refine ⟨wD, Ev.loopS (by simp [pcReg, counterBound]) hpnz ?_, hDsrc, hDpc⟩
    exact hD.append hloopZ
  | head hstep hrest ih =>
    obtain ⟨wD, hD, hDsrc, hDpc, hDclean⟩ :=
      dispatchStep_spec hbelow hstep s hsrc hpc hclean
    let sD : CState := ⟨wD, s.out⟩
    obtain ⟨wF, hF, hFsrc, hFpc⟩ := ih sD hDsrc hDpc hDclean
    have hpnz : s.regs (pcReg B) ≠ 0 := by rw [hpc]; omega
    refine ⟨wF, Ev.loopS (by simp [pcReg, counterBound]) hpnz ?_, hFsrc, hFpc⟩
    exact hD.append hF

/-! ## Initialization and output -/

/-- Load literal inputs into consecutive source counters.  Loading the tail
first keeps the induction state zero at every yet-unwritten index. -/
def loadInputs : Nat → List Nat → Code
  | _, [] => []
  | a, v :: vs => loadInputs (a + 1) vs ++ incMany a v

theorem loadInputs_spec (a : Nat) (xs : List Nat) (out : Nat) :
    ∃ w', Ev (a + xs.length + 1) (loadInputs a xs) ⟨fun _ => 0, out⟩ ⟨w', out⟩ ∧
      ∀ r, w' r =
        if a ≤ r ∧ r < a + xs.length then xs.getD (r - a) 0 else 0 := by
  induction xs generalizing a with
  | nil =>
    refine ⟨fun _ => 0, Ev.nil, ?_⟩
    intro r
    simp
  | cons v vs ih =>
    obtain ⟨wT, hT, hTval⟩ := ih (a + 1)
    let sT : CState := ⟨wT, out⟩
    have haBound : a < a + (v :: vs).length + 1 := by simp; omega
    have hTbig : Ev (a + (v :: vs).length + 1) (loadInputs (a + 1) vs)
        ⟨fun _ => 0, out⟩ ⟨wT, out⟩ := by
      apply Ev.mono (R := a + 1 + vs.length + 1)
      · simp only [List.length_cons]
        omega
      · exact hT
    obtain ⟨wF, hF, hFa, hFfr⟩ :=
      incMany_spec haBound v sT
    refine ⟨wF, ?_, ?_⟩
    · exact hTbig.append hF
    · intro r
      by_cases hra : r = a
      · subst r
        rw [hFa]
        have hTa : wT a = 0 := by
          rw [hTval]
          simp
        simp [sT, hTa]
      · rw [hFfr r hra]
        change wT r = _
        rw [hTval]
        by_cases har : a ≤ r
        · have har' : a + 1 ≤ r := by omega
          by_cases hrlen : r < a + (v :: vs).length
          · have hrlen' : r < a + 1 + vs.length := by
              simp only [List.length_cons] at hrlen
              omega
            rw [if_pos ⟨har', hrlen'⟩, if_pos ⟨har, hrlen⟩]
            have hsub : r - a = (r - (a + 1)) + 1 := by omega
            rw [hsub]
            simp
          · have hrlen' : ¬r < a + 1 + vs.length := by
              simp only [List.length_cons] at hrlen
              omega
            rw [if_neg (fun h => hrlen' h.2), if_neg (fun h => hrlen h.2)]
        · have har' : ¬a + 1 ≤ r := by omega
          rw [if_neg (fun h => har' h.1), if_neg (fun h => har h.1)]

/-- Source-register capacity needed by a program and its input vector. -/
def sourceBound (P : Cslib.URM.Program) (inputs : List Nat) : Nat :=
  max (P.maxRegister + 1) inputs.length

theorem sourceBound_pos (P : Cslib.URM.Program) (inputs : List Nat) :
    0 < sourceBound P inputs := by
  unfold sourceBound
  omega

theorem programBelow_sourceBound (P : Cslib.URM.Program) (inputs : List Nat) :
    ProgramBelow (sourceBound P inputs) P := by
  intro i hi
  have le_foldl : ∀ (xs : List Cslib.URM.Instr) (acc : Nat),
      acc ≤ xs.foldl (fun a j => max a j.maxRegister) acc := by
    intro xs
    induction xs with
    | nil => intro acc; rfl
    | cons j js ih =>
      intro acc
      exact Nat.le_trans (Nat.le_max_left acc j.maxRegister) (ih _)
  have mem_le : ∀ (xs : List Cslib.URM.Instr) (acc : Nat) (j : Cslib.URM.Instr),
      j ∈ xs → j.maxRegister ≤ xs.foldl (fun a t => max a t.maxRegister) acc := by
    intro xs
    induction xs with
    | nil => intro _ _ h; simp at h
    | cons head tail ih =>
      intro acc j hj
      simp only [List.mem_cons] at hj
      rcases hj with rfl | hj
      · exact Nat.le_trans
          (Nat.le_max_right acc _) (le_foldl tail _)
      · exact ih (max acc _) j hj
  have hle : i.maxRegister ≤ P.maxRegister := by
    exact mem_le P 0 i hi
  unfold sourceBound
  omega

/-- Counter-machine prologue: load inputs and activate source instruction 0. -/
def initCode (P : Cslib.URM.Program) (inputs : List Nat) : Code :=
  loadInputs 0 inputs ++ incMany (pcReg (sourceBound P inputs)) 1

theorem initCode_spec (P : Cslib.URM.Program) (inputs : List Nat) :
    ∃ w', Ev (counterBound (sourceBound P inputs)) (initCode P inputs)
        ⟨fun _ => 0, 0⟩ ⟨w', 0⟩ ∧
      SourceMatches (sourceBound P inputs) w' (Cslib.URM.Regs.ofInputs inputs) ∧
      w' (pcReg (sourceBound P inputs)) = 1 ∧
      ScratchClean (sourceBound P inputs) w' := by
  let B := sourceBound P inputs
  have hlen : inputs.length ≤ B := by simp [B, sourceBound]
  obtain ⟨wL, hLsmall, hLval⟩ := loadInputs_spec 0 inputs 0
  have hmono : 0 + inputs.length + 1 ≤ counterBound B := by
    simp [counterBound]
    omega
  have hL : Ev (counterBound B) (loadInputs 0 inputs) ⟨fun _ => 0, 0⟩ ⟨wL, 0⟩ :=
    Ev.mono hmono hLsmall
  let sL : CState := ⟨wL, 0⟩
  have hp : pcReg B < counterBound B := by simp [pcReg, counterBound]
  obtain ⟨wP, hP, hPpc, hPfr⟩ := incMany_spec hp 1 sL
  refine ⟨wP, hL.append hP, ?_, ?_, ?_⟩
  · intro r hr
    rw [hPfr r (by simp [pcReg]; omega)]
    change wL r = Cslib.URM.Regs.ofInputs inputs r
    rw [hLval]
    simp only [Nat.zero_le, Nat.zero_add, true_and]
    by_cases hri : r < inputs.length
    · simp [hri, Cslib.URM.Regs.ofInputs]
    · simp [hri, Cslib.URM.Regs.ofInputs, List.getD_eq_getElem?_getD]
  · rw [hPpc]
    change wL (pcReg B) + 1 = 1
    rw [hLval]
    simp [pcReg, hlen]
  · have houtside : ∀ r, B < r → wP r = 0 := by
      intro r hBr
      rw [hPfr r (by simp [pcReg]; omega)]
      change wL r = 0
      rw [hLval]
      simp only [Nat.zero_le, Nat.zero_add, true_and]
      rw [if_neg (by omega)]
    exact ⟨houtside (savedReg B) (by simp [savedReg]),
      houtside (cmpXReg B) (by simp [cmpXReg]),
      houtside (cmpYReg B) (by simp [cmpYReg]),
      houtside (tmpReg B) (by simp [tmpReg]),
      houtside (gateReg B) (by simp [gateReg]),
      houtside (eqReg B) (by simp [eqReg]),
      houtside (fallReg B) (by simp [fallReg])⟩

/-- Emit one byte per unit of counter `r`, consuming that counter. -/
def emitCounter (r : Nat) : Code := [Cmd.loop r [Cmd.dec r, Cmd.emit]]

theorem emitCounter_spec {R r : Nat} (hr : r < R) :
    ∀ (v : Nat) (s : CState), s.regs r = v →
      ∃ w', Ev R (emitCounter r) s ⟨w', s.out + v⟩ ∧ w' r = 0 ∧
        ∀ k, k ≠ r → w' k = s.regs k := by
  intro v
  induction v with
  | zero =>
    intro s hs
    exact ⟨s.regs, Ev.loopZ hr hs Ev.nil, hs, fun _ _ => rfl⟩
  | succ v ih =>
    intro s hs
    have hnz : s.regs r ≠ 0 := by omega
    let sD := s.down r
    have hDr : sD.regs r = v := by simp [sD, hs]
    obtain ⟨w', hrest, hwr, hwfr⟩ := ih sD.emitOne hDr
    have hrest' : Ev R (emitCounter r) sD.emitOne
        ⟨w', s.out + (v + 1)⟩ := by
      convert hrest using 1
      all_goals simp [sD, CState.emitOne]
      all_goals omega
    refine ⟨w', Ev.loopS hr hnz (Ev.dec hr hnz (Ev.emit hrest')), hwr, ?_⟩
    · intro k hkr
      rw [hwfr k hkr]
      exact CState.down_regs_of_ne s hkr

/-- Complete structured-counter program: initialize, simulate, then encode
the answer as an output-byte count. -/
def counterProgram (P : Cslib.URM.Program) (inputs : List Nat) : Code :=
  initCode P inputs ++ runCode (sourceBound P inputs) P ++ emitCounter 0

theorem counterProgram_spec (P : Cslib.URM.Program) (inputs : List Nat)
    (result : Nat) (h : Cslib.URM.HaltsWithResult P inputs result) :
    ∃ w', Ev (counterBound (sourceBound P inputs)) (counterProgram P inputs)
      ⟨fun _ => 0, 0⟩ ⟨w', result⟩ := by
  rcases h with ⟨v, hsteps, hhalt, hresult⟩
  let B := sourceBound P inputs
  obtain ⟨wI, hI, hIsrc, hIpc, hIclean⟩ := initCode_spec P inputs
  let sI : CState := ⟨wI, 0⟩
  obtain ⟨wR, hR, hRsrc, hRpc⟩ := steps_runCode
    (B := B) (P := P) (programBelow_sourceBound P inputs) hsteps hhalt sI
      hIsrc hIpc hIclean
  let sR : CState := ⟨wR, 0⟩
  have hzeroB : 0 < B := sourceBound_pos P inputs
  have hRzero : sR.regs 0 = result := by
    change wR 0 = result
    rw [hRsrc 0 hzeroB]
    exact hresult
  obtain ⟨wF, hF, hFzero, hFfr⟩ := emitCounter_spec
    (R := counterBound B) (r := 0) (by simp [counterBound]) result sR hRzero
  refine ⟨wF, ?_⟩
  unfold counterProgram
  simpa [B, sR, List.append_assoc] using hI.append (hR.append hF)



end Langlib.Computability.Counter
