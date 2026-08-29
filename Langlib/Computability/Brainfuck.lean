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


end Langlib.Computability.URMBrainfuck
