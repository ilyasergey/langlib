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

end Langlib.Computability.URMPiet

namespace Langlib.Computability

/-- The tag type naming Piet for `ProgLang`. -/
inductive PietLang : Type

instance : ProgLang PietLang where
  Prog := Langlib.Piet.Grid
  parse := fun src => Langlib.Piet.parseGrid {} src.toUTF8
  run := Langlib.Piet.evalGrid

end Langlib.Computability
