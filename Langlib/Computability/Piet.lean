import Langlib.Computability.Class
import Langlib.Computability.URM
import Langlib.Languages.Piet.Semantics

/-!
# Verified foundations for a URM to Piet compiler

Piet's arithmetic storage is an unbounded integer stack.  This file isolates
the stack part of a URM compiler from the image-layout part.  `BlockCmd`
records a Piet operation and the positive size of the colour block that is
left when that operation runs.  `runCode` uses Piet's actual `execOp`, so the
lemmas below check such details as the source-block size used by `push` and
the operand order used by `roll`.

The remaining obligation for a completeness theorem is geometric: lower the
verified command traces to a codel grid and prove, through `computeBlocks` and
`evalGrid`, that DP/CC movement follows those traces, including branches and
back edges.  No `TuringComplete` term is asserted here until that obligation
is proved.
-/

namespace Langlib.Computability.URMPiet

open Langlib.Common
open Langlib.Piet
open Cslib.URM (Program Regs)

/-- A Piet command paired with one less than the size of its source colour
block.  Storing the predecessor makes positivity true by construction. -/
structure BlockCmd where
  op : Op
  blockExtra : Nat
deriving Repr, BEq, Inhabited

/-- The source block of every lowered command has positive size. -/
def BlockCmd.blockSize (c : BlockCmd) : Nat := c.blockExtra + 1

theorem BlockCmd.blockSize_pos (c : BlockCmd) : 0 < c.blockSize := by
  simp [BlockCmd.blockSize]

/-- Execute a command trace using Piet's command semantics. -/
def runCode : List BlockCmd → MState → MState
  | [], s => s
  | c :: cs, s => runCode cs (execOp c.op c.blockSize s)

theorem runCode_append (a b : List BlockCmd) (s : MState) :
    runCode (a ++ b) s = runCode b (runCode a s) := by
  induction a generalizing s with
  | nil => rfl
  | cons c cs ih => simp only [List.cons_append, runCode, ih]

/-- An operation whose source block has size one. -/
def op (o : Op) : BlockCmd := ⟨o, 0⟩

/-- Push a natural number using only positive colour blocks.  Zero is formed
as `1 - 1`, since a Piet colour block can never have size zero. -/
def pushNat (n : Nat) : List BlockCmd :=
  if n = 0 then [op .push, op .push, op .subtract]
  else [{ op := .push, blockExtra := n - 1 }]

/-- Push two naturals and perform a roll.  Piet expects the number of rolls
on top of the depth, so the depth is pushed first. -/
def rollNat (rolls depth : Nat) : List BlockCmd :=
  pushNat depth ++ pushNat rolls ++ [op .roll]

theorem runCode_pushNat (n : Nat) (s : MState) :
    runCode (pushNat n) s = { s with stack := (n : Int) :: s.stack } := by
  unfold pushNat
  by_cases hn : n = 0
  · subst n
    simp [runCode, op, BlockCmd.blockSize, execOp]
  · rw [if_neg hn]
    simp only [runCode, BlockCmd.blockSize, execOp]
    have : n - 1 + 1 = n := by omega
    simp [this]

/-- A direct check that Piet's `push` reads the size of the block being left,
not the destination block. -/
theorem push_uses_source_block_size (extra : Nat) (s : MState) :
    runCode [{ op := .push, blockExtra := extra }] s =
      { s with stack := ((extra + 1 : Nat) : Int) :: s.stack } := by
  simp [runCode, BlockCmd.blockSize, execOp]

/-- The actual Piet `roll` rule, specialised to non-negative arguments and
a depth equal to the current stack length. -/
theorem runCode_rollNat (rolls depth : Nat) (s : MState)
    (hdepth : 0 < depth) (hlen : s.stack.length = depth) :
    runCode (rollNat rolls depth) s =
      { s with stack :=
          s.stack.drop (rolls % depth) ++ s.stack.take (rolls % depth) } := by
  simp only [rollNat, runCode_append, runCode_pushNat]
  simp only [runCode, op, execOp]
  change
    (if (depth : Int) < 0 then
        { s with stack := (rolls : Int) :: (depth : Int) :: s.stack }
      else
        let d := (depth : Int).toNat
        if d > s.stack.length then
          { s with stack := (rolls : Int) :: (depth : Int) :: s.stack }
        else if d == 0 then s
        else
          let k := ((rolls : Int) % (d : Int)).toNat
          let front := s.stack.take d
          { s with stack := front.drop k ++ front.take k ++ s.stack.drop d }) = _
  have ht : s.stack.take depth = s.stack := by rw [← hlen]; simp
  have hd : s.stack.drop depth = [] := by rw [← hlen]; simp
  have hneg : ¬ (depth : Int) < 0 := by omega
  have hzero : depth ≠ 0 := by omega
  rw [if_neg hneg]
  simp [hzero, hlen, ht, hd, ← Int.natCast_emod]

/-- `roll` rotates exactly the requested stack prefix and leaves the suffix
below it in place. -/
theorem runCode_rollNat_prefix (rolls depth : Nat) (front back : List Int)
    (s : MState) (hdepth : 0 < depth) (hlen : front.length = depth)
    (hstack : s.stack = front ++ back) :
    runCode (rollNat rolls depth) s =
      { s with stack :=
          front.drop (rolls % depth) ++ front.take (rolls % depth) ++ back } := by
  simp only [rollNat, runCode_append, runCode_pushNat]
  simp only [runCode, op, execOp]
  change
    (if (depth : Int) < 0 then
        { s with stack := (rolls : Int) :: (depth : Int) :: s.stack }
      else
        let d := (depth : Int).toNat
        if d > s.stack.length then
          { s with stack := (rolls : Int) :: (depth : Int) :: s.stack }
        else if d == 0 then s
        else
          let k := ((rolls : Int) % (d : Int)).toNat
          let front' := s.stack.take d
          { s with stack := front'.drop k ++ front'.take k ++ s.stack.drop d }) = _
  have htake : s.stack.take depth = front := by
    rw [hstack, ← hlen]
    exact List.take_left
  have hdrop : s.stack.drop depth = back := by
    rw [hstack, ← hlen]
    exact List.drop_left
  have htotal : depth ≤ s.stack.length := by
    rw [hstack, List.length_append, hlen]
    omega
  have hneg : ¬ (depth : Int) < 0 := by omega
  have hzero : depth ≠ 0 := by omega
  rw [if_neg hneg]
  simp [hzero, htotal, htake, hdrop, ← Int.natCast_emod]

/-- The abstract command trace for replacing stack entry `r` with a value
already on top.  The caller supplies the old register file under that value.
The two rolls rearrange only the prefix ending at register `r`; `pop` then
discards the old value. -/
def storeTop (r : Nat) : List BlockCmd :=
  rollNat 1 (r + 2) ++ rollNat r (r + 1) ++ [op .pop]

/-- `storeTop r` replaces the entry after a prefix of length `r` with the
value supplied on top.  This is the central fixed-depth register-write
operation. -/
theorem runCode_storeTop (r : Nat) (pre post : List Int) (old value : Int)
    (s : MState) (hpre : pre.length = r)
    (hstack : s.stack = value :: (pre ++ old :: post)) :
    runCode (storeTop r) s = { s with stack := pre ++ value :: post } := by
  let s₁ : MState := { s with stack := pre ++ old :: value :: post }
  have hfront₁ : (value :: (pre ++ [old])).length = r + 2 := by
    simp [hpre]
  have hs₁ : runCode (rollNat 1 (r + 2)) s = s₁ := by
    rw [runCode_rollNat_prefix 1 (r + 2) (value :: (pre ++ [old])) post s
      (by omega) hfront₁]
    · simp only [Nat.mod_eq_of_lt (by omega : 1 < r + 2)]
      simp [s₁]
    · simpa [List.append_assoc] using hstack
  let s₂ : MState := { s with stack := old :: pre ++ value :: post }
  have hfront₂ : (pre ++ [old]).length = r + 1 := by simp [hpre]
  have hs₂ : runCode (rollNat r (r + 1)) s₁ = s₂ := by
    rw [runCode_rollNat_prefix r (r + 1) (pre ++ [old]) (value :: post) s₁
      (by omega) hfront₂]
    · rw [Nat.mod_eq_of_lt (by omega : r < r + 1)]
      simp [hpre, s₁, s₂]
    · simp [s₁]
  simp only [storeTop, runCode_append, hs₁, hs₂, runCode, op, execOp]
  simp [s₂]

/-- A command-level zeroing macro. -/
def zeroAt (r : Nat) : List BlockCmd := pushNat 0 ++ storeTop r

/-- A command-level successor macro, assuming a copy of register `r` has
already been placed on top by `copyAt`. -/
def succTop (r : Nat) : List BlockCmd :=
  pushNat 1 ++ [op .add] ++ storeTop r

theorem runCode_zeroAt (r : Nat) (pre post : List Int) (old : Int)
    (s : MState) (hpre : pre.length = r)
    (hstack : s.stack = pre ++ old :: post) :
    runCode (zeroAt r) s = { s with stack := pre ++ 0 :: post } := by
  simp only [zeroAt, runCode_append, runCode_pushNat]
  apply runCode_storeTop r pre post old 0
  · exact hpre
  · simp [hstack]

theorem runCode_succTop (r : Nat) (pre post : List Int) (old : Int)
    (s : MState) (hpre : pre.length = r)
    (hstack : s.stack = old :: (pre ++ old :: post)) :
    runCode (succTop r) s = { s with stack := pre ++ (old + 1) :: post } := by
  simp only [succTop, runCode_append, runCode_pushNat]
  let s' : MState := { s with stack := (old + 1) :: (pre ++ old :: post) }
  have hadd : runCode [op .add]
      { s with stack := ((1 : Nat) : Int) :: s.stack } = s' := by
    simp [runCode, op, execOp, hstack, s']
  rw [hadd]
  apply runCode_storeTop r pre post old (old + 1) s'
  · exact hpre
  · simp [s']

/-- Copy stack entry `r` to the top while restoring the register file below
it.  `R` is the fixed register-file depth. -/
def copyAt (R r : Nat) : List BlockCmd :=
  rollNat r R ++ [op .dup] ++ rollNat 1 (R + 1) ++
    rollNat (R - r) R ++ rollNat R (R + 1)

/-- Correctness of `copyAt` against Piet's actual `roll` convention. -/
theorem runCode_copyAt (R r : Nat) (pre post : List Int) (value : Int)
    (s : MState) (hr : r < R) (hpre : pre.length = r)
    (hstack : s.stack = pre ++ value :: post)
    (hlen : s.stack.length = R) :
    runCode (copyAt R r) s = { s with stack := value :: s.stack } := by
  have hpost : post.length + r + 1 = R := by
    rw [hstack, List.length_append, List.length_cons, hpre] at hlen
    omega
  let s₁ : MState := { s with stack := value :: post ++ pre }
  have hs₁ : runCode (rollNat r R) s = s₁ := by
    rw [runCode_rollNat_prefix r R (pre ++ value :: post) [] s (by omega)]
    · rw [Nat.mod_eq_of_lt hr]
      simp [hpre, s₁]
    · simpa [hstack] using hlen
    · simpa using hstack
  let s₂ : MState := { s with stack := value :: value :: post ++ pre }
  have hs₂ : runCode [op .dup] s₁ = s₂ := by
    simp [runCode, op, execOp, s₁, s₂]
  let s₃ : MState := { s with stack := value :: post ++ pre ++ [value] }
  have hlen₂ : s₂.stack.length = R + 1 := by
    simp [s₂, hpre, hpost]
  have hs₃ : runCode (rollNat 1 (R + 1)) s₂ = s₃ := by
    rw [runCode_rollNat 1 (R + 1) s₂ (by omega) hlen₂]
    rw [Nat.mod_eq_of_lt (by omega : 1 < R + 1)]
    simp [s₂, s₃, List.append_assoc]
  let s₄ : MState := { s with stack := pre ++ value :: post ++ [value] }
  have hfront₄ : (value :: post ++ pre).length = R := by
    simp [hpre, hpost]
  have hs₄ : runCode (rollNat (R - r) R) s₃ = s₄ := by
    by_cases hz : r = 0
    · have hpre0 : pre.length = 0 := by omega
      have hp : pre = [] := List.eq_nil_of_length_eq_zero hpre0
      subst pre
      rw [runCode_rollNat_prefix (R - r) R (value :: post) [value] s₃
        (by omega) (by simpa using hfront₄)]
      · simp [hz, s₃, s₄]
      · simp [s₃]
    · rw [runCode_rollNat_prefix (R - r) R ((value :: post) ++ pre) [value] s₃
        (by omega) hfront₄]
      · rw [Nat.mod_eq_of_lt (by omega : R - r < R)]
        have hh : (value :: post).length = R - r := by simp; omega
        rw [← hh, List.drop_left, List.take_left]
      · simp [s₃, List.append_assoc]
  let s₅ : MState := { s with stack := value :: pre ++ value :: post }
  have hlen₄ : s₄.stack.length = R + 1 := by
    simp [s₄, hpre]
    omega
  have hs₅ : runCode (rollNat R (R + 1)) s₄ = s₅ := by
    rw [runCode_rollNat R (R + 1) s₄ (by omega) hlen₄,
      Nat.mod_eq_of_lt (by omega : R < R + 1)]
    have hregs : (pre ++ value :: post).length = R := by
      simp [hpre]
      omega
    rw [← hregs, List.drop_left, List.take_left]
    simp [s₄, s₅]
  simp only [copyAt, runCode_append, hs₁, hs₂, hs₃, hs₄, hs₅]
  simp [s₅, hstack]

/-- `copyAt` stated directly for a finite stack vector. -/
theorem runCode_copyAt_list (regs : List Int) (r : Nat) (s : MState)
    (hr : r < regs.length) (hstack : s.stack = regs) :
    runCode (copyAt regs.length r) s =
      { s with stack := regs[r] :: regs } := by
  have hsplit : List.take r regs ++ regs[r] :: List.drop (r + 1) regs = regs := by
    rw [List.getElem_cons_drop hr]
    exact List.take_append_drop r regs
  have hcopy := runCode_copyAt regs.length r (List.take r regs)
    (List.drop (r + 1) regs) regs[r] s hr
    (List.length_take_of_le (Nat.le_of_lt hr))
    (hstack.trans hsplit.symm) (by rw [hstack])
  simpa [hstack] using hcopy

/-- `storeTop` stated directly as `List.set` on a finite stack vector. -/
theorem runCode_storeTop_list (regs : List Int) (r : Nat) (value : Int)
    (s : MState) (hr : r < regs.length) (hstack : s.stack = value :: regs) :
    runCode (storeTop r) s = { s with stack := regs.set r value } := by
  have hsplit : List.take r regs ++ regs[r] :: List.drop (r + 1) regs = regs := by
    rw [List.getElem_cons_drop hr]
    exact List.take_append_drop r regs
  rw [List.set_eq_take_cons_drop value hr]
  apply runCode_storeTop r (List.take r regs) (List.drop (r + 1) regs)
    regs[r] value s
  · exact List.length_take_of_le (Nat.le_of_lt hr)
  · simpa [hsplit] using hstack

/-- Copying through one temporary value shifts a register index by one. -/
theorem runCode_copyAt_cons (regs : List Int) (r : Nat) (value : Int)
    (s : MState) (hr : r < regs.length) (hstack : s.stack = value :: regs) :
    runCode (copyAt (regs.length + 1) (r + 1)) s =
      { s with stack := regs[r] :: value :: regs } := by
  have hr' : r + 1 < (value :: regs).length := by simp; omega
  have hcopy := runCode_copyAt_list (value :: regs) (r + 1) s hr' hstack
  simpa only [List.length_cons, List.getElem_cons_succ] using hcopy

/-- Copying through two temporary values shifts a register index by two. -/
theorem runCode_copyAt_cons_cons (regs : List Int) (r : Nat) (a b : Int)
    (s : MState) (hr : r < regs.length) (hstack : s.stack = a :: b :: regs) :
    runCode (copyAt (regs.length + 2) (r + 2)) s =
      { s with stack := regs[r] :: a :: b :: regs } := by
  have hr' : r + 2 < (a :: b :: regs).length := by simp; omega
  have hcopy := runCode_copyAt_list (a :: b :: regs) (r + 2) s hr' hstack
  simpa only [List.length_cons, List.getElem_cons_succ] using hcopy

/-- Stack code for the three non-branching URM instructions. -/
def instrCode (R : Nat) : Cslib.URM.Instr → Option (List BlockCmd)
  | .Z r => some (zeroAt r)
  | .S r => some (copyAt R r ++ succTop r)
  | .T m r => some (copyAt R m ++ storeTop r)
  | .J _ _ _ => none

theorem runCode_Z (R r : Nat) (pre post : List Int) (old : Int)
    (s : MState) (_hr : r < R) (hpre : pre.length = r)
    (hstack : s.stack = pre ++ old :: post) (_hlen : s.stack.length = R) :
    runCode (zeroAt r) s = { s with stack := pre ++ 0 :: post } :=
  runCode_zeroAt r pre post old s hpre hstack

theorem runCode_S (R r : Nat) (pre post : List Int) (old : Int)
    (s : MState) (hr : r < R) (hpre : pre.length = r)
    (hstack : s.stack = pre ++ old :: post) (hlen : s.stack.length = R) :
    runCode (copyAt R r ++ succTop r) s =
      { s with stack := pre ++ (old + 1) :: post } := by
  rw [runCode_append, runCode_copyAt R r pre post old s hr hpre hstack hlen]
  exact runCode_succTop r pre post old _ hpre (by simp [hstack])

theorem runCode_T (R m r : Nat)
    (preM postM preR postR : List Int) (src dst : Int)
    (s : MState) (hm : m < R) (hpreM : preM.length = m)
    (hpreR : preR.length = r)
    (hsrc : s.stack = preM ++ src :: postM)
    (hdst : s.stack = preR ++ dst :: postR)
    (hlen : s.stack.length = R) :
    runCode (copyAt R m ++ storeTop r) s =
      { s with stack := preR ++ src :: postR } := by
  rw [runCode_append,
    runCode_copyAt R m preM postM src s hm hpreM hsrc hlen]
  exact runCode_storeTop r preR postR dst src _ hpreR (by simp [hdst])

/-- Compile a list of non-branching URM instructions to their verified stack
traces.  A jump is rejected explicitly because its image-level routing proof
is the remaining completeness obligation. -/
def straightCode (R : Nat) : Program → Except String (List BlockCmd)
  | [] => .ok []
  | i :: is => do
      let c ← match instrCode R i with
        | some c => .ok c
        | none => .error "URM J requires a proved Piet routing gadget"
      return c ++ (← straightCode R is)

/-! ## A runnable straight-corridor lowerer

This lowerer is used to exercise the stack macros on the real interpreter.
It deliberately handles one pass only.  In particular it does not pretend
that a row can implement a URM jump.
-/

def hueOfNat (n : Nat) : Hue :=
  match n % 6 with
  | 0 => .red | 1 => .yellow | 2 => .green
  | 3 => .cyan | 4 => .blue | _ => .magenta

def lightnessOfNat (n : Nat) : Lightness :=
  match n % 3 with
  | 0 => .light | 1 => .normal | _ => .dark

/-- The colour-wheel displacement encoding an operation. -/
def opDelta : Op → Nat × Nat
  | .push => (0, 1) | .pop => (0, 2)
  | .add => (1, 0) | .subtract => (1, 1) | .multiply => (1, 2)
  | .divide => (2, 0) | .mod => (2, 1) | .not => (2, 2)
  | .greater => (3, 0) | .pointer => (3, 1) | .switch => (3, 2)
  | .dup => (4, 0) | .roll => (4, 1) | .inNum => (4, 2)
  | .inChar => (5, 0) | .outNum => (5, 1) | .outChar => (5, 2)

def advance (h : Hue) (l : Lightness) (o : Op) : Hue × Lightness :=
  let d := opDelta o
  (hueOfNat (h.toNat + d.1), lightnessOfNat (l.toNat + d.2))

/-- The colour transition chosen by `advance` is exactly the requested Piet
operation. -/
theorem opFor_advance (h : Hue) (l : Lightness) (o : Op) :
    let c := advance h l o
    opFor (hueSteps h c.1) (lightSteps l c.2) = some o := by
  cases h <;> cases l <;> cases o <;> rfl

/-- Consecutive generated source blocks cannot merge, since every operation
has a non-zero colour displacement. -/
theorem advance_ne (h : Hue) (l : Lightness) (o : Op) :
    advance h l o ≠ (h, l) := by
  intro heq
  have hc : opFor (hueSteps h (advance h l o).1)
      (lightSteps l (advance h l o).2) = some o := opFor_advance h l o
  rw [heq] at hc
  cases h <;> cases l <;> simp [hueSteps, lightSteps, opFor] at hc

/-- Lay command source blocks left to right.  The final singleton is the
destination block of the final operation. -/
def coloredRuns : Hue → Lightness → List BlockCmd → List Codel
  | h, l, [] => [.chromatic h l]
  | h, l, c :: cs =>
      List.replicate c.blockSize (.chromatic h l) ++
        let next := advance h l c.op
        coloredRuns next.1 next.2 cs

theorem coloredRuns_ne_nil (h : Hue) (l : Lightness) (code : List BlockCmd) :
    coloredRuns h l code ≠ [] := by
  induction code generalizing h l with
  | nil => simp [coloredRuns]
  | cons c cs ih =>
    simp [coloredRuns, BlockCmd.blockSize]

theorem coloredRuns_length (h : Hue) (l : Lightness) (code : List BlockCmd) :
    (coloredRuns h l code).length = (code.map BlockCmd.blockSize).sum + 1 := by
  induction code generalizing h l with
  | nil => rfl
  | cons c cs ih =>
    simp [coloredRuns, ih, Nat.add_assoc]

/-- A three-row corridor.  The first source block is a vertical two-codel
block whose `pop` is ignored on the initially empty stack.  Its blocked
upper exit toggles CC, after which execution traverses the middle row.  A
white codel separates the last command from a full-height terminal bar. -/
def linearGrid (code : List BlockCmd) : Grid :=
  let startH := Hue.red
  let startL := Lightness.normal
  let afterPrefix := advance startH startL .pop
  let terminal := Codel.chromatic Hue.yellow Lightness.normal
  let middle := [.chromatic startH startL] ++
    coloredRuns afterPrefix.1 afterPrefix.2 code ++ [.white, terminal]
  let width := middle.length
  let top := [.chromatic startH startL] ++ List.replicate (width - 2) .black ++ [terminal]
  let bottom := List.replicate (width - 1) .black ++ [terminal]
  { width, height := 3, codels := (top ++ middle ++ bottom).toArray }

/-- The register depth used by the straight-line test compiler. -/
def registerDepth (P : Program) (inputs : List Nat) : Nat :=
  max (P.maxRegister + 1) inputs.length

def initialRegisters (R : Nat) (inputs : List Nat) : List Nat :=
  (List.range R).map fun r => inputs.getD r 0

def initialCode (R : Nat) (inputs : List Nat) : List BlockCmd :=
  ((initialRegisters R inputs).reverse).flatMap pushNat

theorem runCode_pushNats (values : List Nat) (s : MState) :
    runCode (values.flatMap pushNat) s =
      { s with stack := (values.map Int.ofNat).reverse ++ s.stack } := by
  induction values generalizing s with
  | nil => simp [runCode]
  | cons value values ih =>
    simp only [List.flatMap_cons, runCode_append, runCode_pushNat, ih]
    simp [List.map, List.reverse_cons, List.append_assoc]

private theorem reverse_map_natInt (values : List Nat) :
    (((values.reverse).map Int.ofNat).reverse) = values.map Int.ofNat := by
  rw [List.map_reverse, List.reverse_reverse]

theorem runCode_initialCode (R : Nat) (inputs : List Nat) (s : MState) :
    runCode (initialCode R inputs) s =
      { s with stack :=
          (initialRegisters R inputs).map Int.ofNat ++ s.stack } := by
  rw [initialCode, runCode_pushNats]
  congr 1
  exact congrArg (· ++ s.stack) (reverse_map_natInt (initialRegisters R inputs))

/-- Runnable compiler for the non-branching fragment.  It lowers the verified
stack traces to the regular corridor and prints register zero. -/
def compileStraight (P : Program) (inputs : List Nat) : Except String Grid := do
  let R := registerDepth P inputs
  let body ← straightCode R P
  let output := copyAt R 0 ++ [op .outNum]
  return linearGrid (initialCode R inputs ++ body ++ output)

/-- Decimal output decoder used by the partial compiler tests. -/
def decodeOutput (b : ByteArray) : Option Nat :=
  match String.fromUTF8? b with
  | some s => s.toNat?
  | none => none

/-! ## A branchless URM dispatcher

Arbitrary URM control flow can be reduced to one geometric loop.  The stack
contains the URM register prefix followed by `pc`, `next`, and `flag`.
During one pass every source instruction is guarded by `pc = i`; arithmetic
masks make inactive instructions leave the state unchanged.  A `J` writes its
target to `next` when both its guard and register comparison are true. -/

/-- Store `pc + 1` in `next`. -/
def beginDispatch (N pc next : Nat) : List BlockCmd :=
  copyAt N pc ++ pushNat 1 ++ [op .add] ++ storeTop next

/-- Set `flag` to `1` exactly when `pc = i`. -/
def selectInstr (N pc flag i : Nat) : List BlockCmd :=
  copyAt N pc ++ pushNat i ++ [op .subtract, op .not] ++ storeTop flag

theorem runCode_beginDispatch_list (regs : List Int) (pc next : Nat) (s : MState)
    (hpc : pc < regs.length) (hnext : next < regs.length)
    (hstack : s.stack = regs) :
    runCode (beginDispatch regs.length pc next) s =
      { s with stack := regs.set next (regs[pc] + 1) } := by
  simp only [beginDispatch, runCode_append]
  rw [runCode_copyAt_list regs pc s hpc hstack, runCode_pushNat]
  simp only [runCode, op, execOp]
  apply runCode_storeTop_list regs next (regs[pc] + 1) _ hnext
  rfl

theorem runCode_selectInstr_list (regs : List Int) (pc flag i : Nat) (s : MState)
    (hpc : pc < regs.length) (hflag : flag < regs.length)
    (hstack : s.stack = regs) :
    runCode (selectInstr regs.length pc flag i) s =
      { s with stack := regs.set flag (if regs[pc] = (i : Int) then 1 else 0) } := by
  simp only [selectInstr, runCode_append]
  rw [runCode_copyAt_list regs pc s hpc hstack, runCode_pushNat]
  simp only [runCode, op, execOp]
  apply runCode_storeTop_list regs flag (if regs[pc] = (i : Int) then 1 else 0)
    _ hflag
  by_cases h : regs[pc] = (i : Int)
  · simp [h]
  · simp [h]
    omega

/-- Guarded `Z r`: multiply the register by `not flag`. -/
def guardedZ (N flag r : Nat) : List BlockCmd :=
  copyAt N flag ++ [op .not] ++ copyAt (N + 1) (r + 1) ++
    [op .multiply] ++ storeTop r

/-- Guarded `S r`: add the Boolean guard to the register. -/
def guardedS (N flag r : Nat) : List BlockCmd :=
  copyAt N flag ++ copyAt (N + 1) (r + 1) ++
    [op .add] ++ storeTop r

/-- Guarded `T m r`: `r := r + flag * (m - r)`. -/
def guardedT (N flag m r : Nat) : List BlockCmd :=
  copyAt N m ++ copyAt (N + 1) (r + 1) ++ [op .subtract] ++
    copyAt (N + 1) (flag + 1) ++ [op .multiply] ++
    copyAt (N + 1) (r + 1) ++ [op .add] ++ storeTop r

def boolNotInt (x : Int) : Int := if x = 0 then 1 else 0

theorem runCode_guardedZ_list (regs : List Int) (flag r : Nat) (s : MState)
    (hflag : flag < regs.length) (hr : r < regs.length)
    (hstack : s.stack = regs) :
    runCode (guardedZ regs.length flag r) s =
      { s with stack := regs.set r (boolNotInt regs[flag] * regs[r]) } := by
  simp only [guardedZ, runCode_append]
  rw [runCode_copyAt_list regs flag s hflag hstack]
  have hnot : runCode [op .not] { s with stack := regs[flag] :: regs } =
      { s with stack := boolNotInt regs[flag] :: regs } := by
    simp [runCode, op, execOp, boolNotInt]
  rw [hnot]
  have hr' : r + 1 < (boolNotInt regs[flag] :: regs).length := by simp; omega
  have hcopy := runCode_copyAt_list (boolNotInt regs[flag] :: regs) (r + 1)
    { s with stack := boolNotInt regs[flag] :: regs } hr' rfl
  simp only [List.getElem_cons_succ] at hcopy
  rw [show regs.length + 1 = (boolNotInt regs[flag] :: regs).length by simp]
  rw [hcopy]
  have hmul : runCode [op .multiply]
      { s with stack := regs[r] :: boolNotInt regs[flag] :: regs } =
      { s with stack := boolNotInt regs[flag] * regs[r] :: regs } := by
    simp [runCode, op, execOp, Int.mul_comm]
  rw [hmul]
  apply runCode_storeTop_list regs r (boolNotInt regs[flag] * regs[r]) _ hr
  rfl

theorem runCode_guardedS_list (regs : List Int) (flag r : Nat) (s : MState)
    (hflag : flag < regs.length) (hr : r < regs.length)
    (hstack : s.stack = regs) :
    runCode (guardedS regs.length flag r) s =
      { s with stack := regs.set r (regs[r] + regs[flag]) } := by
  simp only [guardedS, runCode_append]
  rw [runCode_copyAt_list regs flag s hflag hstack]
  have hr' : r + 1 < (regs[flag] :: regs).length := by simp; omega
  have hcopy := runCode_copyAt_list (regs[flag] :: regs) (r + 1)
    { s with stack := regs[flag] :: regs } hr' rfl
  simp only [List.getElem_cons_succ] at hcopy
  rw [show regs.length + 1 = (regs[flag] :: regs).length by simp]
  rw [hcopy]
  have hadd : runCode [op .add]
      { s with stack := regs[r] :: regs[flag] :: regs } =
      { s with stack := (regs[r] + regs[flag]) :: regs } := by
    simp [runCode, op, execOp, Int.add_comm]
  rw [hadd]
  apply runCode_storeTop_list regs r (regs[r] + regs[flag]) _ hr
  rfl

theorem runCode_guardedT_list (regs : List Int) (flag m r : Nat) (s : MState)
    (hflag : flag < regs.length) (hm : m < regs.length) (hr : r < regs.length)
    (hstack : s.stack = regs) :
    runCode (guardedT regs.length flag m r) s =
      { s with stack := regs.set r (regs[r] + regs[flag] * (regs[m] - regs[r])) } := by
  simp only [guardedT, runCode_append]
  rw [runCode_copyAt_list regs m s hm hstack]
  rw (occs := .pos [2]) [runCode_copyAt_cons regs r regs[m] _ hr rfl]
  have hsub : runCode [op .subtract]
      { s with stack := regs[r] :: regs[m] :: regs } =
      { s with stack := (regs[m] - regs[r]) :: regs } := by
    simp [runCode, op, execOp]
  rw [hsub]
  rw [runCode_copyAt_cons regs flag (regs[m] - regs[r]) _ hflag rfl]
  have hmul : runCode [op .multiply]
      { s with stack := regs[flag] :: (regs[m] - regs[r]) :: regs } =
      { s with stack := ((regs[m] - regs[r]) * regs[flag]) :: regs } := by
    simp [runCode, op, execOp]
  rw [hmul]
  rw [runCode_copyAt_cons regs r ((regs[m] - regs[r]) * regs[flag]) _ hr rfl]
  have hadd : runCode [op .add]
      { s with stack := regs[r] :: ((regs[m] - regs[r]) * regs[flag]) :: regs } =
      { s with stack :=
          (regs[r] + regs[flag] * (regs[m] - regs[r])) :: regs } := by
    simp [runCode, op, execOp]
    simp [Int.mul_comm, Int.add_comm]
  rw [hadd]
  apply runCode_storeTop_list regs r
    (regs[r] + regs[flag] * (regs[m] - regs[r])) _ hr rfl

/-- Replace `flag` by its conjunction with register equality. -/
def guardedEq (N flag m r : Nat) : List BlockCmd :=
  -- equality of the two source registers
  copyAt N m ++ copyAt (N + 1) (r + 1) ++ [op .subtract, op .not] ++
  -- conjunction with the instruction guard
  copyAt (N + 1) (flag + 1) ++ [op .multiply] ++ storeTop flag

/-- Compute the fall-through contribution `next * (1 - flag)`. -/
def guardedNextLeft (N next flag : Nat) : List BlockCmd :=
  -- next * (1 - flag)
  copyAt N flag ++ [op .not] ++ copyAt (N + 1) (next + 1) ++ [op .multiply]

/-- Select `next` between its old value and jump target `q`. -/
def guardedNext (N next flag q : Nat) : List BlockCmd :=
  guardedNextLeft N next flag ++
  -- plus q * flag
  copyAt (N + 1) (flag + 1) ++ pushNat q ++ [op .multiply, op .add] ++
  storeTop next

/-- Guarded `J m r q`.  `flag` is replaced by the conjunction of the
instruction guard and `m = r`, then `next` is selected between its current
value and `q`. -/
def guardedJ (N next flag m r q : Nat) : List BlockCmd :=
  guardedEq N flag m r ++ guardedNext N next flag q

theorem runCode_guardedEq_list (regs : List Int) (flag m r : Nat) (s : MState)
    (hflag : flag < regs.length) (hm : m < regs.length) (hr : r < regs.length)
    (hstack : s.stack = regs) :
    runCode (guardedEq regs.length flag m r) s =
      { s with stack := regs.set flag (boolNotInt (regs[m] - regs[r]) * regs[flag]) } := by
  simp only [guardedEq, runCode_append]
  rw [runCode_copyAt_list regs m s hm hstack]
  rw [runCode_copyAt_cons regs r regs[m] _ hr rfl]
  have hsubnot : runCode [op .subtract, op .not]
      { s with stack := regs[r] :: regs[m] :: regs } =
      { s with stack := boolNotInt (regs[m] - regs[r]) :: regs } := by
    simp [runCode, op, execOp, boolNotInt]
  rw [hsubnot]
  rw [runCode_copyAt_cons regs flag (boolNotInt (regs[m] - regs[r])) _ hflag rfl]
  have hmul : runCode [op .multiply]
      { s with stack := regs[flag] :: boolNotInt (regs[m] - regs[r]) :: regs } =
      { s with stack :=
          (boolNotInt (regs[m] - regs[r]) * regs[flag]) :: regs } := by
    simp [runCode, op, execOp]
  rw [hmul]
  apply runCode_storeTop_list regs flag
    (boolNotInt (regs[m] - regs[r]) * regs[flag]) _ hflag rfl

theorem runCode_guardedNextLeft_list (regs : List Int) (next flag : Nat)
    (s : MState) (hnext : next < regs.length) (hflag : flag < regs.length)
    (hstack : s.stack = regs) :
    runCode (guardedNextLeft regs.length next flag) s =
      { s with stack :=
          (boolNotInt regs[flag] * regs[next]) :: regs } := by
  simp only [guardedNextLeft, runCode_append]
  rw [runCode_copyAt_list regs flag s hflag hstack]
  have hnot : runCode [op .not] { s with stack := regs[flag] :: regs } =
      { s with stack := boolNotInt regs[flag] :: regs } := by
    simp [runCode, op, execOp, boolNotInt]
  rw [hnot]
  rw [runCode_copyAt_cons regs next (boolNotInt regs[flag]) _ hnext rfl]
  have hmul : runCode [op .multiply]
      { s with stack := regs[next] :: boolNotInt regs[flag] :: regs } =
      { s with stack := (boolNotInt regs[flag] * regs[next]) :: regs } := by
    simp [runCode, op, execOp]
  exact hmul

theorem runCode_guardedNext_list (regs : List Int) (next flag q : Nat)
    (s : MState) (hnext : next < regs.length) (hflag : flag < regs.length)
    (hstack : s.stack = regs) :
    runCode (guardedNext regs.length next flag q) s =
      { s with stack := regs.set next (boolNotInt regs[flag] * regs[next] +
          (q : Int) * regs[flag]) } := by
  simp only [guardedNext, runCode_append]
  rw [runCode_guardedNextLeft_list regs next flag s hnext hflag hstack]
  rw [runCode_copyAt_cons regs flag (boolNotInt regs[flag] * regs[next]) _ hflag rfl]
  rw [runCode_pushNat]
  have hmuladd : runCode [op .multiply, op .add]
      { s with stack := (q : Int) :: regs[flag] ::
          (boolNotInt regs[flag] * regs[next]) :: regs } =
      { s with stack :=
          (boolNotInt regs[flag] * regs[next] + (q : Int) * regs[flag]) :: regs } := by
    simp [runCode, op, execOp, Int.mul_comm]
  rw [hmuladd]
  apply runCode_storeTop_list regs next
    (boolNotInt regs[flag] * regs[next] + (q : Int) * regs[flag]) _ hnext rfl

theorem runCode_guardedJ_list (regs : List Int) (next flag m r q : Nat)
    (s : MState) (hnext : next < regs.length) (hflag : flag < regs.length)
    (hm : m < regs.length) (hr : r < regs.length) (hstack : s.stack = regs) :
    let updated := regs.set flag (boolNotInt (regs[m] - regs[r]) * regs[flag])
    runCode (guardedJ regs.length next flag m r q) s =
      { s with stack := updated.set next (boolNotInt (updated[flag]'(by
            simpa [updated] using hflag)) *
            (updated[next]'(by simpa [updated] using hnext)) +
            (q : Int) * (updated[flag]'(by simpa [updated] using hflag))) } := by
  dsimp only
  rw [guardedJ, runCode_append]
  rw [runCode_guardedEq_list regs flag m r s hflag hm hr hstack]
  let regs' := regs.set flag (boolNotInt (regs[m] - regs[r]) * regs[flag])
  have hlen : regs'.length = regs.length := by simp [regs']
  have hnext' : next < regs'.length := by omega
  have hflag' : flag < regs'.length := by omega
  have hcode : guardedNext regs.length next flag q =
      guardedNext regs'.length next flag q := by rw [hlen]
  rw [hcode]
  simpa [regs'] using runCode_guardedNext_list regs' next flag q
    { s with stack := regs' } hnext' hflag' rfl

def guardedInstr (N next flag : Nat) : Cslib.URM.Instr → List BlockCmd
  | .Z r => guardedZ N flag r
  | .S r => guardedS N flag r
  | .T m r => guardedT N flag m r
  | .J m r q => guardedJ N next flag m r q

/-- One linear dispatcher pass, with source positions numbered from `i`. -/
def dispatchFrom (N pc next flag : Nat) : Nat → Program → List BlockCmd
  | _, [] => []
  | i, instr :: rest =>
      selectInstr N pc flag i ++ guardedInstr N next flag instr ++
        dispatchFrom N pc next flag (i + 1) rest

/-- Commit `next` to `pc`. -/
def endDispatch (N pc next : Nat) : List BlockCmd :=
  copyAt N next ++ storeTop pc

theorem runCode_endDispatch_list (regs : List Int) (pc next : Nat) (s : MState)
    (hpc : pc < regs.length) (hnext : next < regs.length)
    (hstack : s.stack = regs) :
    runCode (endDispatch regs.length pc next) s =
      { s with stack := regs.set pc regs[next] } := by
  simp only [endDispatch, runCode_append]
  rw [runCode_copyAt_list regs next s hnext hstack]
  apply runCode_storeTop_list regs pc regs[next] _ hpc rfl

/-- Copy the answer under a Boolean saying whether the committed program
counter is still inside the source program.  The stack result is
`running :: answer :: registers`. -/
def prepareBranch (N pc programLength : Nat) : List BlockCmd :=
  copyAt N 0 ++ pushNat programLength ++ copyAt (N + 2) (pc + 2) ++
    [op .greater]

theorem runCode_prepareBranch_list (regs : List Int) (pc programLength : Nat)
    (s : MState) (hnonempty : 0 < regs.length) (hpc : pc < regs.length)
    (hstack : s.stack = regs) :
    runCode (prepareBranch regs.length pc programLength) s =
      { s with stack := (if regs[pc] < (programLength : Int) then 1 else 0) ::
          regs[0] :: regs } := by
  simp only [prepareBranch, runCode_append]
  rw [runCode_copyAt_list regs 0 s hnonempty hstack, runCode_pushNat]
  rw [runCode_copyAt_cons_cons regs pc (programLength : Int) regs[0] _ hpc rfl]
  simp [runCode, op, execOp]

/-- Compensate the return corridor's chooser turns, then steer from a
Boolean running flag. -/
def steerBranch : List BlockCmd := pushNat 1 ++ [op .switch, op .pointer]

theorem runCode_steerBranch_zero (answer : Int) (regs : List Int) (s : MState)
    (hstack : s.stack = 0 :: answer :: regs) :
    runCode steerBranch s =
      { s with cc := s.cc.toggle, stack := answer :: regs } := by
  rcases s with ⟨pos, dp, cc, stack, input, output⟩
  cases dp <;> cases cc <;>
    simp [steerBranch, runCode_append, runCode_pushNat, runCode, op, execOp,
      hstack, Dir.rotate, Dir.ofNat, Dir.toNat, CC.toggle]

theorem runCode_steerBranch_one (answer : Int) (regs : List Int) (s : MState)
    (hstack : s.stack = 1 :: answer :: regs) :
    runCode steerBranch s =
      { s with dp := s.dp.clockwise, cc := s.cc.toggle, stack := answer :: regs } := by
  rcases s with ⟨pos, dp, cc, stack, input, output⟩
  cases dp <;> cases cc <;>
    simp [steerBranch, runCode_append, runCode_pushNat, runCode, op, execOp,
      hstack, Dir.clockwise, Dir.rotate, Dir.ofNat, Dir.toNat, CC.toggle]

/-- One complete dispatcher iteration.  The final `switch` compensates for
the three clockwise turns in the white return corridor.  `pointer` consumes
the running flag: zero continues right to output, one turns down to loop. -/
def dispatcherCode (P : Program) (base : Nat) : List BlockCmd :=
  let pc := base
  let next := base + 1
  let flag := base + 2
  let N := base + 3
  beginDispatch N pc next ++ dispatchFrom N pc next flag 0 P ++
    endDispatch N pc next ++ prepareBranch N pc P.length ++
    steerBranch

/-- The colour after every command in a trace has executed. -/
def endColor : Hue → Lightness → List BlockCmd → Hue × Lightness
  | h, l, [] => (h, l)
  | h, l, c :: cs =>
      let next := advance h l c.op
      endColor next.1 next.2 cs

/-- A fixed-loop codel layout for the branchless dispatcher.

Execution starts on white at `(0,0)` and slides right into the first source
block.  A running iteration turns down at the final pivot, executes `pop` on
the saved answer, and follows the white bottom/left return corridor.  A
halting iteration continues right, executes `outNum`, then enters the interior
of the terminal colour block.  None of that block's eight selected exits is
the entry codel, and every selected exit is blocked. -/
def loopGrid (prologue body : List BlockCmd) : Grid :=
  let startH := Hue.red
  let startL := Lightness.normal
  let prologuePath := coloredRuns startH startL prologue
  let main := pushNat 1 ++ [op .pop] ++ body
  let path := coloredRuns startH startL main
  let pivot := endColor startH startL main
  let outBlock := advance pivot.1 pivot.2 .outNum
  let loopBlock := advance pivot.1 pivot.2 .pop
  let terminal := Codel.chromatic Hue.yellow Lightness.dark
  let A := prologuePath.length
  let L := path.length
  let top := [.white] ++ prologuePath ++ [.white] ++ path ++
    [.chromatic outBlock.1 outBlock.2, .white, .white, terminal]
  let middle := List.replicate (A + 1) .black ++ [.white] ++
    List.replicate (L - 1) .black ++
    [.chromatic loopBlock.1 loopBlock.2, .black, terminal, terminal, terminal]
  let bottom := List.replicate (A + 1) .black ++ List.replicate (L + 1) .white ++
    [.black, terminal, terminal, terminal]
  { width := A + L + 6, height := 3, codels := (top ++ middle ++ bottom).toArray }

/-- Full runnable compiler, including arbitrary `J` targets.  Its command
trace proof is developed above; this definition is kept separate from
`compileStraight` so the straight-line fragment remains available. -/
def compileLoop (P : Program) (inputs : List Nat) : Grid :=
  let base := registerDepth P inputs
  let N := base + 3
  loopGrid (initialCode N inputs) (dispatcherCode P base)

/-! ## Unit-block normalization

The loop geometry becomes easier to characterize when every command source is
a singleton.  Larger `push` blocks can be eliminated by constructing the same
positive integer from repeated singleton pushes and additions. -/

def addUnit : Nat → List BlockCmd
  | 0 => []
  | n + 1 => addUnit n ++ [op .push, op .add]

def pushNatUnit : Nat → List BlockCmd
  | 0 => [op .push, op .push, op .subtract]
  | n + 1 => op .push :: addUnit n

theorem runCode_addUnit (n : Nat) (v : Int) (st : List Int) (s : MState)
    (hstack : s.stack = v :: st) :
    runCode (addUnit n) s = { s with stack := (v + n) :: st } := by
  induction n generalizing s v with
  | zero =>
    simp only [addUnit, runCode]
    cases s
    simp_all
  | succ n ih =>
    simp only [addUnit, runCode_append]
    rw [ih v s hstack]
    simp [runCode, op, BlockCmd.blockSize, execOp]
    omega

theorem runCode_pushNatUnit (n : Nat) (s : MState) :
    runCode (pushNatUnit n) s = { s with stack := (n : Int) :: s.stack } := by
  cases n with
  | zero => simp [pushNatUnit, runCode, op, BlockCmd.blockSize, execOp]
  | succ n =>
    simp only [pushNatUnit, runCode]
    rw [runCode_addUnit n 1 s.stack _ rfl]
    simp [op, BlockCmd.blockSize, execOp]
    omega

def unitizeCmd (c : BlockCmd) : List BlockCmd :=
  match c.op with
  | .push => pushNatUnit c.blockSize
  | o => [op o]

def unitize (code : List BlockCmd) : List BlockCmd := code.flatMap unitizeCmd

/-- Every command source in a normalized trace occupies one codel. -/
def UnitCode (code : List BlockCmd) : Prop :=
  ∀ c, c ∈ code → c.blockSize = 1

theorem coloredRuns_length_of_unit (h : Hue) (l : Lightness)
    (code : List BlockCmd) (hu : UnitCode code) :
    (coloredRuns h l code).length = code.length + 1 := by
  rw [coloredRuns_length]
  have hsum : (code.map BlockCmd.blockSize).sum = code.length := by
    induction code with
    | nil => rfl
    | cons c cs ih =>
      have hc : c.blockSize = 1 := hu c (by simp)
      have hcs : UnitCode cs := by
        intro c' hc'
        exact hu c' (by simp [hc'])
      simp [hc, ih hcs, Nat.add_comm]
  rw [hsum]

theorem unitCode_addUnit (n : Nat) : UnitCode (addUnit n) := by
  induction n with
  | zero => simp [UnitCode, addUnit]
  | succ n ih =>
    intro c hc
    rw [addUnit, List.mem_append] at hc
    cases hc with
    | inl hc => exact ih c hc
    | inr hc =>
      simp at hc
      rcases hc with h | h <;> subst c <;> rfl

theorem unitCode_pushNatUnit (n : Nat) : UnitCode (pushNatUnit n) := by
  cases n with
  | zero => simp [UnitCode, pushNatUnit, op, BlockCmd.blockSize]
  | succ n =>
    simpa [UnitCode, pushNatUnit, op, BlockCmd.blockSize] using unitCode_addUnit n

theorem unitCode_unitizeCmd (c : BlockCmd) : UnitCode (unitizeCmd c) := by
  cases c with
  | mk o extra =>
    cases o
    case push =>
      change UnitCode (pushNatUnit (extra + 1))
      simpa [Nat.succ_eq_add_one] using unitCode_pushNatUnit extra.succ
    all_goals simp [unitizeCmd, UnitCode, op, BlockCmd.blockSize]

theorem unitCode_unitize (code : List BlockCmd) : UnitCode (unitize code) := by
  intro c hc
  simp only [unitize, List.mem_flatMap] at hc
  obtain ⟨source, _, hsource⟩ := hc
  exact unitCode_unitizeCmd source c hsource

private theorem execOp_blockSize_irrelevant (o : Op) (h : o ≠ .push)
    (a b : Nat) (s : MState) : execOp o a s = execOp o b s := by
  unfold execOp
  split <;> simp_all

theorem runCode_unitizeCmd (c : BlockCmd) (s : MState) :
    runCode (unitizeCmd c) s = runCode [c] s := by
  cases c with
  | mk o extra =>
    cases o <;> simp only [unitizeCmd]
    case push =>
      rw [runCode_pushNatUnit]
      simp [runCode, BlockCmd.blockSize, execOp]
    all_goals
      simp only [runCode, op, BlockCmd.blockSize]
      apply execOp_blockSize_irrelevant
      simp

theorem runCode_unitize (code : List BlockCmd) (s : MState) :
    runCode (unitize code) s = runCode code s := by
  induction code generalizing s with
  | nil => rfl
  | cons c cs ih =>
    rw [show unitize (c :: cs) = unitizeCmd c ++ unitize cs from rfl,
      runCode_append, runCode_unitizeCmd, ih]
    rfl

/-- Full compiler with singleton command blocks. -/
def compile (P : Program) (inputs : List Nat) : Grid :=
  let base := registerDepth P inputs
  let N := base + 3
  loopGrid (unitize (initialCode N inputs)) (unitize (dispatcherCode P base))

end Langlib.Computability.URMPiet

namespace Langlib.Computability

/-- The tag type naming Piet for `ProgLang`. -/
inductive PietLang : Type

instance : ProgLang PietLang where
  Prog := Langlib.Piet.Grid
  parse := fun src => Langlib.Piet.parseGrid {} src.toUTF8
  run := Langlib.Piet.evalGrid

end Langlib.Computability
