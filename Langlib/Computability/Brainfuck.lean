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
It first finds the zero just after the run.  The excursion to the following
guide cell allocates enough zero tape for the next increment. -/
def incAt (R : Nat) : List Brainfuck.Op :=
  [.loop (rights (stride R)), .inc, .right, .inc] ++
  rights (stride R) ++ lefts (stride R) ++ [.loop (lefts (stride R))] ++
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
      simp only [Brainfuck.State.moveRight, tapeAt, tapeCells, List.reverse_cons,
        List.nil_append]
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


end Langlib.Computability.URMBrainfuck
