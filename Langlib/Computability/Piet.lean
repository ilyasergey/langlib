import Langlib.Common.Fuel
import Std.Data.String.ToNat
import Langlib.Common.Computability
import Langlib.Computability.URM
import Langlib.Languages.Piet.Semantics
import Langlib.Languages.Piet.Stability

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

theorem runCode_set_pos (code : List BlockCmd) (s : MState) (p : Nat × Nat) :
    runCode code { s with pos := p } = { runCode code s with pos := p } := by
  induction code generalizing s with
  | nil => rfl
  | cons c cs ih =>
      rw [runCode, execOp_set_pos, ih]
      rfl

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

/-- A command trace whose operations do not change the direction pointer or
codel chooser. -/
def StableCode (code : List BlockCmd) : Prop :=
  ∀ c, c ∈ code → c.op ≠ .pointer ∧ c.op ≠ .switch

/-- Proof-facing description of a horizontal run of isolated singleton
blocks.  Every field is stated against the real grid functions used by
`tryFrom`; generated-grid lemmas discharge these fields. -/
inductive UnitCorridor (g : Grid) : Nat → Hue → Lightness → List BlockCmd → Prop
  | nil (x h l) : UnitCorridor g x h l []
  | cons {x : Nat} {h : Hue} {l : Lightness} (c : BlockCmd) (cs : List BlockCmd)
      (hunit : c.blockSize = 1)
      (hinfo : localInfoAt? g (x, 0) = some (singletonInfo (x, 0)))
      (hcurrent : g.get x 0 = .chromatic h l)
      (hstep : step? g (x, 0) .right = some (x + 1, 0))
      (hnext : g.get (x + 1) 0 =
        .chromatic (advance h l c.op).1 (advance h l c.op).2)
      (tail : UnitCorridor g (x + 1) (advance h l c.op).1
        (advance h l c.op).2 cs) :
      UnitCorridor g x h l (c :: cs)

/-- Exact multi-command bridge from a proof-facing singleton corridor to the
actual fuel evaluator. -/
theorem exec_unitCorridor (g : Grid) (bl : Blocks) (code : List BlockCmd)
    (x : Nat) (h : Hue) (l : Lightness) (trace : UnitCorridor g x h l code)
    (stable : StableCode code) (fuel : Nat) (s : MState)
    (hpos : s.pos = (x, 0)) (hdp : s.dp = .right) :
    exec g bl (fuel + code.length) s =
      exec g bl fuel { runCode code s with pos := (x + code.length, 0) } := by
  induction trace generalizing fuel s with
  | nil x h l =>
      simp only [List.length_nil, Nat.add_zero, runCode]
      rcases s with ⟨pos, dp, cc, stack, input, output⟩
      simp_all
  | cons c cs hunit hinfo hcurrent hstep hnext tail ih =>
      rename_i x' h' l'
      have hcstable := stable c (by simp)
      have htailstable : StableCode cs := by
        intro c' hc'
        exact stable c' (by simp [hc'])
      have hcurrent' : g.get s.pos.1 s.pos.2 = .chromatic h' l' := by
        simpa [hpos] using hcurrent
      have hinfo' : localInfoAt? g s.pos = some (singletonInfo s.pos) := by
        simpa [hpos] using hinfo
      have hstep' : step? g s.pos s.dp = some (x' + 1, 0) := by
        simpa [hpos, hdp] using hstep
      rw [show fuel + (c :: cs).length = (fuel + cs.length) + 1 by simp; omega]
      rw [exec_singleton g bl (fuel + cs.length) s h' l' (x' + 1, 0)
        (advance h' l' c.op).1 (advance h' l' c.op).2 c.op hinfo' hcurrent'
        hstep' hnext (opFor_advance h' l' c.op)]
      let moved : MState := { s with pos := (x' + 1, 0) }
      let s₁ : MState := execOp c.op 1 moved
      have hpos₁ : s₁.pos = (x' + 1, 0) := by
        simp only [s₁, moved, execOp_set_pos]
      have hdp₁ : s₁.dp = .right := by
        simp only [s₁]
        rw [execOp_dp_of_ne_pointer c.op 1 moved hcstable.1]
        simpa [moved] using hdp
      rw [show execOp c.op 1 { s with pos := (x' + 1, 0) } = s₁ from rfl]
      rw [ih htailstable fuel s₁ hpos₁ hdp₁]
      rw [runCode, ← hunit, show s₁ = execOp c.op c.blockSize moved by
        simp [s₁, hunit]]
      rw [show execOp c.op c.blockSize moved
            = { execOp c.op c.blockSize s with pos := (x' + 1, 0) } by
          simp only [moved, execOp_set_pos]]
      rw [runCode_set_pos cs (execOp c.op c.blockSize s) (x' + 1, 0)]
      congr 2
      simp [hunit]
      omega

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

/-- Register indices mentioned by an instruction fit inside a finite stack
register vector. -/
def InstrBelow (N : Nat) : Cslib.URM.Instr → Prop
  | .Z r | .S r => r < N
  | .T m r | .J m r _ => m < N ∧ r < N

/-- The total list transformation performed by one guarded instruction.
`getD` makes the definition executable; the correctness theorem below uses
`InstrBelow` to show every access is in range. -/
def guardedUpdate (next flag : Nat) (instr : Cslib.URM.Instr)
    (regs : List Int) : List Int :=
  match instr with
  | .Z r => regs.set r (boolNotInt (regs.getD flag 0) * regs.getD r 0)
  | .S r => regs.set r (regs.getD r 0 + regs.getD flag 0)
  | .T m r => regs.set r (regs.getD r 0 +
      regs.getD flag 0 * (regs.getD m 0 - regs.getD r 0))
  | .J m r q =>
      let updated := regs.set flag
        (boolNotInt (regs.getD m 0 - regs.getD r 0) * regs.getD flag 0)
      updated.set next (boolNotInt (updated.getD flag 0) * updated.getD next 0 +
        (q : Int) * updated.getD flag 0)

theorem runCode_guardedInstr_list (regs : List Int) (next flag : Nat)
    (instr : Cslib.URM.Instr) (s : MState)
    (hnext : next < regs.length) (hflag : flag < regs.length)
    (hinstr : InstrBelow regs.length instr) (hstack : s.stack = regs) :
    runCode (guardedInstr regs.length next flag instr) s =
      { s with stack := guardedUpdate next flag instr regs } := by
  cases instr with
  | Z r =>
      simp only [InstrBelow] at hinstr
      simpa [guardedInstr, guardedUpdate, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hflag, List.getElem?_eq_getElem hinstr] using
        runCode_guardedZ_list regs flag r s hflag hinstr hstack
  | S r =>
      simp only [InstrBelow] at hinstr
      simpa [guardedInstr, guardedUpdate, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hflag, List.getElem?_eq_getElem hinstr] using
        runCode_guardedS_list regs flag r s hflag hinstr hstack
  | T m r =>
      rcases hinstr with ⟨hm, hr⟩
      simpa [guardedInstr, guardedUpdate, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hflag, List.getElem?_eq_getElem hm,
        List.getElem?_eq_getElem hr] using
        runCode_guardedT_list regs flag m r s hflag hm hr hstack
  | J m r q =>
      rcases hinstr with ⟨hm, hr⟩
      rw [show guardedInstr regs.length next flag (.J m r q) =
          guardedJ regs.length next flag m r q from rfl,
        runCode_guardedJ_list regs next flag m r q s hnext hflag hm hr hstack]
      let updated := regs.set flag
        (boolNotInt (regs[m] - regs[r]) * regs[flag])
      have hflag' : flag < updated.length := by simpa [updated] using hflag
      have hnext' : next < updated.length := by simpa [updated] using hnext
      have hgetflag : updated.getD flag 0 = updated[flag] := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hflag']
      have hgetnext : updated.getD next 0 = updated[next] := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hnext']
      simp only [guardedUpdate]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hflag,
        List.getElem?_eq_getElem hm, List.getElem?_eq_getElem hr]
      simp only [Option.getD_some]
      rw [← hgetflag, ← hgetnext]
      rfl

/-- The total list transformation performed by a dispatcher suffix. -/
def dispatchUpdate (pc next flag : Nat) : Nat → Program → List Int → List Int
  | _, [], regs => regs
  | i, instr :: rest, regs =>
      let selected := regs.set flag
        (if regs.getD pc 0 = (i : Int) then 1 else 0)
      dispatchUpdate pc next flag (i + 1) rest
        (guardedUpdate next flag instr selected)

/-- One linear dispatcher pass, with source positions numbered from `i`. -/
def dispatchFrom (N pc next flag : Nat) : Nat → Program → List BlockCmd
  | _, [] => []
  | i, instr :: rest =>
      selectInstr N pc flag i ++ guardedInstr N next flag instr ++
        dispatchFrom N pc next flag (i + 1) rest

/-- Exact command semantics of a whole dispatcher suffix. -/
theorem runCode_dispatchFrom_list (P : Program) (regs : List Int)
    (pc next flag i : Nat) (s : MState)
    (hpc : pc < regs.length) (hnext : next < regs.length)
    (hflag : flag < regs.length)
    (hbelow : ∀ instr, instr ∈ P → InstrBelow regs.length instr)
    (hstack : s.stack = regs) :
    runCode (dispatchFrom regs.length pc next flag i P) s =
      { s with stack := dispatchUpdate pc next flag i P regs } := by
  induction P generalizing i regs s with
  | nil =>
      rcases s with ⟨pos, dp, cc, stack, input, output⟩
      simp_all [dispatchFrom, dispatchUpdate, runCode]
  | cons instr rest ih =>
      simp only [dispatchFrom, dispatchUpdate, runCode_append]
      rw [runCode_selectInstr_list regs pc flag i s hpc hflag hstack]
      have hgetpc : regs.getD pc 0 = regs[pc] := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hpc]
      rw [← hgetpc]
      let selected := regs.set flag
        (if regs.getD pc 0 = (i : Int) then 1 else 0)
      have hlen : selected.length = regs.length := by simp [selected]
      have hpc' : pc < selected.length := by omega
      have hnext' : next < selected.length := by omega
      have hflag' : flag < selected.length := by omega
      have hinstr : InstrBelow selected.length instr := by
        rw [hlen]
        exact hbelow instr (by simp)
      have hguard := runCode_guardedInstr_list selected next flag instr
        { s with stack := selected } hnext' hflag' hinstr rfl
      rw [show guardedInstr regs.length next flag instr =
          guardedInstr selected.length next flag instr by rw [hlen]]
      rw [hguard]
      let updated := guardedUpdate next flag instr selected
      have hulen : updated.length = regs.length := by
        cases instr <;> simp [updated, guardedUpdate, selected]
      have hrest : ∀ instr', instr' ∈ rest → InstrBelow updated.length instr' := by
        intro instr' hi'
        rw [hulen]
        exact hbelow instr' (by simp [hi'])
      have htail := ih updated (i + 1) { s with stack := updated }
        (by omega) (by omega) (by omega) hrest rfl
      rw [show dispatchFrom regs.length pc next flag (i + 1) rest =
          dispatchFrom updated.length pc next flag (i + 1) rest by rw [hulen]]
      simpa [selected, updated] using htail

/-! ## The dispatcher computes one URM step

`runCode_dispatchFrom_list` says what a dispatcher pass does to the stack.
This section says what that means: with the register prefix holding a URM
register file and the three control slots holding the program counter, the
fall-through counter and the guard, one pass performs exactly one
`Cslib.URM.Step`. -/

/-- The dispatcher's stack for a URM register file: one slot per register,
then the program counter, the fall-through counter and the guard. -/
def stackOf (base : Nat) (regs : Nat → Nat) (pc next flag : Int) : List Int :=
  (List.range base).map (fun r => (regs r : Int)) ++ [pc, next, flag]

@[simp] theorem stackOf_length (base : Nat) (regs : Nat → Nat)
    (pc next flag : Int) : (stackOf base regs pc next flag).length = base + 3 := by
  simp [stackOf]

@[simp] theorem stackOf_getElem_reg (base : Nat) (regs : Nat → Nat)
    (pc next flag : Int) (r : Nat) (hr : r < base) :
    (stackOf base regs pc next flag)[r]'(by simp only [stackOf_length]; omega) = (regs r : Int) := by
  simp only [stackOf]
  rw [List.getElem_append_left (by simpa using hr)]
  simp

@[simp] theorem stackOf_getElem_pc (base : Nat) (regs : Nat → Nat)
    (pc next flag : Int) :
    (stackOf base regs pc next flag)[base]'(by simp only [stackOf_length]; omega) = pc := by
  simp only [stackOf]
  rw [List.getElem_append_right (by simp)]
  simp

@[simp] theorem stackOf_getElem_next (base : Nat) (regs : Nat → Nat)
    (pc next flag : Int) :
    (stackOf base regs pc next flag)[base + 1]'(by simp only [stackOf_length]; omega) = next := by
  simp only [stackOf]
  rw [List.getElem_append_right (by simp)]
  simp

@[simp] theorem stackOf_getElem_flag (base : Nat) (regs : Nat → Nat)
    (pc next flag : Int) :
    (stackOf base regs pc next flag)[base + 2]'(by simp only [stackOf_length]; omega) = flag := by
  simp only [stackOf]
  rw [List.getElem_append_right (by simp)]
  simp

theorem stackOf_getD_reg (base : Nat) (regs : Nat → Nat)
    (pc next flag : Int) (r : Nat) (hr : r < base) :
    (stackOf base regs pc next flag).getD r 0 = (regs r : Int) := by
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (i := r) (by simp only [stackOf_length]; omega)]
  simpa using stackOf_getElem_reg base regs pc next flag r hr

theorem stackOf_getD_pc (base : Nat) (regs : Nat → Nat)
    (pc next flag : Int) : (stackOf base regs pc next flag).getD base 0 = pc := by
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (i := base) (by simp only [stackOf_length]; omega)]
  simp

theorem stackOf_getD_next (base : Nat) (regs : Nat → Nat)
    (pc next flag : Int) :
    (stackOf base regs pc next flag).getD (base + 1) 0 = next := by
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (i := base + 1) (by simp only [stackOf_length]; omega)]
  simp

theorem stackOf_getD_flag (base : Nat) (regs : Nat → Nat)
    (pc next flag : Int) :
    (stackOf base regs pc next flag).getD (base + 2) 0 = flag := by
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (i := base + 2) (by simp only [stackOf_length]; omega)]
  simp

theorem stackOf_set_reg (base : Nat) (regs : Nat → Nat) (pc next flag : Int)
    (r v : Nat) (hr : r < base) :
    (stackOf base regs pc next flag).set r (v : Int) =
      stackOf base (Function.update regs r v) pc next flag := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [stackOf, List.getElem_set]
    by_cases hi : i < base
    · rw [List.getElem_append_left (by simpa using hi),
        List.getElem_append_left (by simpa using hi)]
      simp only [List.getElem_map, List.getElem_range]
      by_cases hir : r = i
      · subst hir
        simp
      · rw [if_neg (by omega)]
        rw [Function.update_of_ne (by omega)]
    · rw [List.getElem_append_right (by simpa using Nat.le_of_not_lt hi),
        List.getElem_append_right (by simpa using Nat.le_of_not_lt hi)]
      rw [if_neg (by omega)]
      simp

theorem stackOf_set_pc (base : Nat) (regs : Nat → Nat) (pc next flag v : Int) :
    (stackOf base regs pc next flag).set base v =
      stackOf base regs v next flag := by
  simp only [stackOf, List.set_append, List.length_map, List.length_range]
  rw [if_neg (by omega)]
  simp

theorem stackOf_set_next (base : Nat) (regs : Nat → Nat) (pc next flag v : Int) :
    (stackOf base regs pc next flag).set (base + 1) v =
      stackOf base regs pc v flag := by
  simp only [stackOf, List.set_append, List.length_map, List.length_range]
  rw [if_neg (by omega)]
  have h : base + 1 - base = 1 := by omega
  rw [h]
  simp

theorem stackOf_set_flag (base : Nat) (regs : Nat → Nat) (pc next flag v : Int) :
    (stackOf base regs pc next flag).set (base + 2) v =
      stackOf base regs pc next v := by
  simp only [stackOf, List.set_append, List.length_map, List.length_range]
  rw [if_neg (by omega)]
  have h : base + 2 - base = 2 := by omega
  rw [h]
  simp

/-- Overwriting a register with what it already holds changes nothing. -/
private theorem update_self_eq (regs : Nat → Nat) (r : Nat) :
    Function.update regs r (regs r) = regs := by
  funext x
  by_cases h : x = r
  · subst h; simp
  · simp [Function.update_of_ne h]

/-- A guarded instruction whose guard is zero changes nothing. -/
theorem guardedUpdate_of_flag_zero (base : Nat) (instr : Cslib.URM.Instr)
    (hb : InstrBelow base instr) (regs : Nat → Nat) (pc next : Int) :
    guardedUpdate (base + 1) (base + 2) instr (stackOf base regs pc next 0) =
      stackOf base regs pc next 0 := by
  cases instr with
  | Z r =>
      simp only [InstrBelow] at hb
      have hval : boolNotInt ((stackOf base regs pc next 0).getD (base + 2) 0) *
          (stackOf base regs pc next 0).getD r 0 = ((regs r : Nat) : Int) := by
        rw [stackOf_getD_flag, stackOf_getD_reg base regs pc next 0 r hb]
        simp [boolNotInt]
      simp only [guardedUpdate, hval]
      rw [stackOf_set_reg base regs pc next 0 r (regs r) hb, update_self_eq]
  | S r =>
      simp only [InstrBelow] at hb
      have hval : (stackOf base regs pc next 0).getD r 0 +
          (stackOf base regs pc next 0).getD (base + 2) 0 = ((regs r : Nat) : Int) := by
        rw [stackOf_getD_flag, stackOf_getD_reg base regs pc next 0 r hb]
        simp
      simp only [guardedUpdate, hval]
      rw [stackOf_set_reg base regs pc next 0 r (regs r) hb, update_self_eq]
  | T m r =>
      obtain ⟨hm, hr⟩ := hb
      have hval : (stackOf base regs pc next 0).getD r 0 +
          (stackOf base regs pc next 0).getD (base + 2) 0 *
            ((stackOf base regs pc next 0).getD m 0 -
              (stackOf base regs pc next 0).getD r 0) = ((regs r : Nat) : Int) := by
        rw [stackOf_getD_flag, stackOf_getD_reg base regs pc next 0 r hr,
          stackOf_getD_reg base regs pc next 0 m hm]
        simp
      simp only [guardedUpdate, hval]
      rw [stackOf_set_reg base regs pc next 0 r (regs r) hr, update_self_eq]
  | J m r q =>
      obtain ⟨hm, hr⟩ := hb
      have h1 : boolNotInt ((stackOf base regs pc next 0).getD m 0 -
          (stackOf base regs pc next 0).getD r 0) *
          (stackOf base regs pc next 0).getD (base + 2) 0 = 0 := by
        rw [stackOf_getD_flag]
        simp
      simp only [guardedUpdate, h1]
      rw [stackOf_set_flag]
      have h2 : boolNotInt ((stackOf base regs pc next 0).getD (base + 2) 0) *
          (stackOf base regs pc next 0).getD (base + 1) 0 +
          (q : Int) * (stackOf base regs pc next 0).getD (base + 2) 0 = next := by
        rw [stackOf_getD_flag, stackOf_getD_next]
        simp [boolNotInt]
      rw [h2, stackOf_set_next]

/-- Dispatcher passes compose along the program list. -/
theorem dispatchUpdate_append (pc next flag : Nat) :
    ∀ (a b : Program) (i : Nat) (regs : List Int),
      dispatchUpdate pc next flag i (a ++ b) regs =
        dispatchUpdate pc next flag (i + a.length) b
          (dispatchUpdate pc next flag i a regs)
  | [], b, i, regs => by simp [dispatchUpdate]
  | x :: a, b, i, regs => by
      simp only [List.cons_append, dispatchUpdate]
      rw [dispatchUpdate_append pc next flag a b (i + 1) _]
      simp [Nat.add_comm, Nat.add_left_comm]

/-- A run of instructions none of which the program counter selects leaves
the register file, the program counter and the fall-through counter alone. -/
theorem dispatchUpdate_miss (base : Nat) :
    ∀ (rest : Program) (i : Nat) (regs : Nat → Nat) (pc next flag : Int),
      (∀ x ∈ rest, InstrBelow base x) →
      (∀ j, j < rest.length → pc ≠ ((i + j : Nat) : Int)) →
      ∃ f, dispatchUpdate base (base + 1) (base + 2) i rest
          (stackOf base regs pc next flag) = stackOf base regs pc next f
  | [], i, regs, pc, next, flag, _, _ => ⟨flag, by simp [dispatchUpdate]⟩
  | instr :: rest, i, regs, pc, next, flag, hbelow, hmiss => by
      have hne : pc ≠ (i : Int) := by simpa using hmiss 0 (by simp)
      simp only [dispatchUpdate, stackOf_getD_pc]
      rw [if_neg hne, stackOf_set_flag]
      rw [guardedUpdate_of_flag_zero base instr (hbelow instr (by simp)) regs pc next]
      exact dispatchUpdate_miss base rest (i + 1) regs pc next 0
        (fun x hx => hbelow x (by simp [hx]))
        (fun j hj => by
          have := hmiss (j + 1) (by simpa using hj)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this)

/-! ### The selected instruction -/

theorem guardedUpdate_Z (base r : Nat) (hr : r < base) (regs : Nat → Nat)
    (pc next : Int) :
    guardedUpdate (base + 1) (base + 2) (.Z r) (stackOf base regs pc next 1) =
      stackOf base (Function.update regs r 0) pc next 1 := by
  have hval : boolNotInt ((stackOf base regs pc next 1).getD (base + 2) 0) *
      (stackOf base regs pc next 1).getD r 0 = ((0 : Nat) : Int) := by
    rw [stackOf_getD_flag, stackOf_getD_reg base regs pc next 1 r hr]
    simp [boolNotInt]
  simp only [guardedUpdate, hval]
  rw [stackOf_set_reg base regs pc next 1 r 0 hr]

theorem guardedUpdate_S (base r : Nat) (hr : r < base) (regs : Nat → Nat)
    (pc next : Int) :
    guardedUpdate (base + 1) (base + 2) (.S r) (stackOf base regs pc next 1) =
      stackOf base (Function.update regs r (regs r + 1)) pc next 1 := by
  have hval : (stackOf base regs pc next 1).getD r 0 +
      (stackOf base regs pc next 1).getD (base + 2) 0 =
        ((regs r + 1 : Nat) : Int) := by
    rw [stackOf_getD_flag, stackOf_getD_reg base regs pc next 1 r hr]
    omega
  simp only [guardedUpdate, hval]
  rw [stackOf_set_reg base regs pc next 1 r (regs r + 1) hr]

theorem guardedUpdate_T (base m r : Nat) (hm : m < base) (hr : r < base)
    (regs : Nat → Nat) (pc next : Int) :
    guardedUpdate (base + 1) (base + 2) (.T m r) (stackOf base regs pc next 1) =
      stackOf base (Function.update regs r (regs m)) pc next 1 := by
  have hval : (stackOf base regs pc next 1).getD r 0 +
      (stackOf base regs pc next 1).getD (base + 2) 0 *
        ((stackOf base regs pc next 1).getD m 0 -
          (stackOf base regs pc next 1).getD r 0) = ((regs m : Nat) : Int) := by
    rw [stackOf_getD_flag, stackOf_getD_reg base regs pc next 1 r hr,
      stackOf_getD_reg base regs pc next 1 m hm]
    omega
  simp only [guardedUpdate, hval]
  rw [stackOf_set_reg base regs pc next 1 r (regs m) hr]

theorem guardedUpdate_J_eq (base m r q : Nat) (hm : m < base) (hr : r < base)
    (regs : Nat → Nat) (heq : regs m = regs r) (pc next : Int) :
    guardedUpdate (base + 1) (base + 2) (.J m r q) (stackOf base regs pc next 1) =
      stackOf base regs pc (q : Int) 1 := by
  have h1 : boolNotInt ((stackOf base regs pc next 1).getD m 0 -
      (stackOf base regs pc next 1).getD r 0) *
      (stackOf base regs pc next 1).getD (base + 2) 0 = 1 := by
    rw [stackOf_getD_flag, stackOf_getD_reg base regs pc next 1 r hr,
      stackOf_getD_reg base regs pc next 1 m hm]
    rw [show ((regs m : Nat) : Int) - ((regs r : Nat) : Int) = 0 by omega]
    simp [boolNotInt]
  simp only [guardedUpdate, h1]
  rw [stackOf_set_flag]
  have h2 : boolNotInt ((stackOf base regs pc next 1).getD (base + 2) 0) *
      (stackOf base regs pc next 1).getD (base + 1) 0 +
      (q : Int) * (stackOf base regs pc next 1).getD (base + 2) 0 = (q : Int) := by
    rw [stackOf_getD_flag, stackOf_getD_next]
    simp [boolNotInt]
  rw [h2, stackOf_set_next]

theorem guardedUpdate_J_ne (base m r q : Nat) (hm : m < base) (hr : r < base)
    (regs : Nat → Nat) (hne : regs m ≠ regs r) (pc next : Int) :
    guardedUpdate (base + 1) (base + 2) (.J m r q) (stackOf base regs pc next 1) =
      stackOf base regs pc next 0 := by
  have h1 : boolNotInt ((stackOf base regs pc next 1).getD m 0 -
      (stackOf base regs pc next 1).getD r 0) *
      (stackOf base regs pc next 1).getD (base + 2) 0 = 0 := by
    rw [stackOf_getD_flag, stackOf_getD_reg base regs pc next 1 r hr,
      stackOf_getD_reg base regs pc next 1 m hm]
    rw [show boolNotInt (((regs m : Nat) : Int) - ((regs r : Nat) : Int)) = 0 by
      simp only [boolNotInt]
      rw [if_neg (by omega)]]
    simp
  simp only [guardedUpdate, h1]
  rw [stackOf_set_flag]
  have h2 : boolNotInt ((stackOf base regs pc next 0).getD (base + 2) 0) *
      (stackOf base regs pc next 0).getD (base + 1) 0 +
      (q : Int) * (stackOf base regs pc next 0).getD (base + 2) 0 = next := by
    rw [stackOf_getD_flag, stackOf_getD_next]
    simp [boolNotInt]
  rw [h2, stackOf_set_next]

/-- Split a program at the instruction its program counter selects. -/
private theorem split_at_getElem : ∀ (l : Program) (i : Nat) (x : Cslib.URM.Instr),
    l[i]? = some x → l = l.take i ++ x :: l.drop (i + 1)
  | [], i, x, h => by simp at h
  | y :: l, 0, x, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp
  | y :: l, i + 1, x, h => by
      simp only [List.getElem?_cons_succ] at h
      have ih := split_at_getElem l i x h
      simp only [List.take_succ_cons, List.drop_succ_cons, List.cons_append]
      exact congrArg (y :: ·) ih

/-- The dispatcher step at the index the program counter selects. -/
theorem dispatchUpdate_cons_hit (base i : Nat) (instr : Cslib.URM.Instr)
    (rest : Program) (regs : Nat → Nat) (next flag : Int) :
    dispatchUpdate base (base + 1) (base + 2) i (instr :: rest)
        (stackOf base regs (i : Int) next flag) =
      dispatchUpdate base (base + 1) (base + 2) (i + 1) rest
        (guardedUpdate (base + 1) (base + 2) instr
          (stackOf base regs (i : Int) next 1)) := by
  simp [dispatchUpdate, stackOf_set_flag]

/-- One dispatcher pass performs exactly one URM step on the stack model. -/
theorem dispatchUpdate_step (base : Nat) (P : Program) {u u' : Cslib.URM.State}
    (hstep : Cslib.URM.Step P u u') (hbelow : ∀ x ∈ P, InstrBelow base x)
    (flag : Int) :
    ∃ f, dispatchUpdate base (base + 1) (base + 2) 0 P
        (stackOf base u.regs (u.pc : Int) ((u.pc : Int) + 1) flag) =
      stackOf base u'.regs (u.pc : Int) (u'.pc : Int) f := by
  have hsplit : ∀ (instr : Cslib.URM.Instr), P[u.pc]? = some instr →
      ∀ (regs : Nat → Nat) (pcOut : Int) (f : Int),
      guardedUpdate (base + 1) (base + 2) instr
          (stackOf base u.regs (u.pc : Int) ((u.pc : Int) + 1) 1) =
        stackOf base regs (u.pc : Int) pcOut f →
      ∃ f', dispatchUpdate base (base + 1) (base + 2) 0 P
          (stackOf base u.regs (u.pc : Int) ((u.pc : Int) + 1) flag) =
        stackOf base regs (u.pc : Int) pcOut f' := by
    intro instr hget regs pcOut f hupd
    have hlen : u.pc < P.length := by
      by_contra hcon
      rw [List.getElem?_eq_none (by omega)] at hget
      simp at hget
    have hP := split_at_getElem P u.pc instr hget
    have htake : (P.take u.pc).length = u.pc := by
      simp only [List.length_take]
      omega
    rw [show dispatchUpdate base (base + 1) (base + 2) 0 P =
        dispatchUpdate base (base + 1) (base + 2) 0
          (P.take u.pc ++ instr :: P.drop (u.pc + 1)) from by rw [← hP]]
    rw [dispatchUpdate_append, htake, Nat.zero_add]
    obtain ⟨f₀, hpre⟩ := dispatchUpdate_miss base (P.take u.pc) 0 u.regs
      ((u.pc : Int)) ((u.pc : Int) + 1) flag
      (fun x hx => hbelow x (by rw [hP]; exact List.mem_append_left _ hx))
      (by
        intro j hj
        rw [htake] at hj
        omega)
    rw [hpre]
    rw [dispatchUpdate_cons_hit, hupd]
    obtain ⟨f₁, hpost⟩ := dispatchUpdate_miss base (P.drop (u.pc + 1)) (u.pc + 1)
      regs ((u.pc : Int)) pcOut f
      (fun x hx => hbelow x (by
        rw [hP]
        exact List.mem_append_right _ (List.mem_cons_of_mem _ hx)))
      (by
        intro j hj
        omega)
    exact ⟨f₁, hpost⟩
  cases hstep with
  | @zero n hget =>
      have h := hsplit (.Z n) hget (Function.update u.regs n 0) ((u.pc : Int) + 1) 1
        (guardedUpdate_Z base n (hbelow _ (List.mem_of_getElem? hget)) u.regs _ _)
      rw [show ((u.pc : Int) + 1) = (((u.pc + 1 : Nat)) : Int) by omega] at h
      exact h
  | @succ n hget =>
      have h := hsplit (.S n) hget (Function.update u.regs n (u.regs n + 1))
        ((u.pc : Int) + 1) 1
        (guardedUpdate_S base n (hbelow _ (List.mem_of_getElem? hget)) u.regs _ _)
      rw [show ((u.pc : Int) + 1) = (((u.pc + 1 : Nat)) : Int) by omega] at h
      exact h
  | @transfer m n hget =>
      obtain ⟨hm, hn⟩ := hbelow _ (List.mem_of_getElem? hget)
      have h := hsplit (.T m n) hget (Function.update u.regs n (u.regs m))
        ((u.pc : Int) + 1) 1 (guardedUpdate_T base m n hm hn u.regs _ _)
      rw [show ((u.pc : Int) + 1) = (((u.pc + 1 : Nat)) : Int) by omega] at h
      exact h
  | @jump_eq m n q hget heq =>
      obtain ⟨hm, hn⟩ := hbelow _ (List.mem_of_getElem? hget)
      exact hsplit (.J m n q) hget u.regs (q : Int) 1
        (guardedUpdate_J_eq base m n q hm hn u.regs heq _ _)
  | @jump_ne m n q hget hne =>
      obtain ⟨hm, hn⟩ := hbelow _ (List.mem_of_getElem? hget)
      have h := hsplit (.J m n q) hget u.regs ((u.pc : Int) + 1) 0
        (guardedUpdate_J_ne base m n q hm hn u.regs hne _ _)
      rw [show ((u.pc : Int) + 1) = (((u.pc + 1 : Nat)) : Int) by omega] at h
      exact h

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

/-! ### One whole dispatcher iteration -/

theorem instrBelow_mono {N M : Nat} (h : N ≤ M) :
    ∀ instr : Cslib.URM.Instr, InstrBelow N instr → InstrBelow M instr := by
  intro instr hb
  cases instr with
  | Z r | S r => exact lt_of_lt_of_le hb h
  | T m r | J m r q => exact ⟨lt_of_lt_of_le hb.1 h, lt_of_lt_of_le hb.2 h⟩

theorem runCode_beginDispatch_stackOf (base : Nat) (regs : Nat → Nat)
    (pc next flag : Int) (s : MState)
    (hstack : s.stack = stackOf base regs pc next flag) :
    runCode (beginDispatch (base + 3) base (base + 1)) s =
      { s with stack := stackOf base regs pc (pc + 1) flag } := by
  rw [show base + 3 = (stackOf base regs pc next flag).length from
    (stackOf_length base regs pc next flag).symm]
  rw [runCode_beginDispatch_list (stackOf base regs pc next flag) base (base + 1)
    s (by simp only [stackOf_length]; omega) (by simp only [stackOf_length]; omega)
    hstack]
  congr 1
  rw [stackOf_getElem_pc, stackOf_set_next]

theorem runCode_dispatchFrom_stackOf (base : Nat) (P : Program)
    (regs : Nat → Nat) (pc next flag : Int) (s : MState)
    (hbelow : ∀ x ∈ P, InstrBelow base x)
    (hstack : s.stack = stackOf base regs pc next flag) :
    runCode (dispatchFrom (base + 3) base (base + 1) (base + 2) 0 P) s =
      { s with
        stack := dispatchUpdate base (base + 1) (base + 2) 0 P
          (stackOf base regs pc next flag) } := by
  rw [show base + 3 = (stackOf base regs pc next flag).length from
    (stackOf_length base regs pc next flag).symm]
  exact runCode_dispatchFrom_list P (stackOf base regs pc next flag)
    base (base + 1) (base + 2) 0 s
    (by simp only [stackOf_length]; omega) (by simp only [stackOf_length]; omega)
    (by simp only [stackOf_length]; omega)
    (fun x hx => instrBelow_mono (by simp only [stackOf_length]; omega) x (hbelow x hx))
    hstack

theorem runCode_endDispatch_stackOf (base : Nat) (regs : Nat → Nat)
    (pc next flag : Int) (s : MState)
    (hstack : s.stack = stackOf base regs pc next flag) :
    runCode (endDispatch (base + 3) base (base + 1)) s =
      { s with stack := stackOf base regs next next flag } := by
  rw [show base + 3 = (stackOf base regs pc next flag).length from
    (stackOf_length base regs pc next flag).symm]
  rw [runCode_endDispatch_list (stackOf base regs pc next flag) base (base + 1)
    s (by simp only [stackOf_length]; omega) (by simp only [stackOf_length]; omega)
    hstack]
  congr 1
  rw [stackOf_getElem_next, stackOf_set_pc]

theorem runCode_prepareBranch_stackOf (base : Nat) (regs : Nat → Nat)
    (pc next flag : Int) (programLength : Nat) (hbase : 0 < base) (s : MState)
    (hstack : s.stack = stackOf base regs pc next flag) :
    runCode (prepareBranch (base + 3) base programLength) s =
      { s with
        stack := (if pc < (programLength : Int) then 1 else 0) ::
          ((regs 0 : Nat) : Int) :: stackOf base regs pc next flag } := by
  rw [show base + 3 = (stackOf base regs pc next flag).length from
    (stackOf_length base regs pc next flag).symm]
  rw [runCode_prepareBranch_list (stackOf base regs pc next flag) base
    programLength s (by simp only [stackOf_length]; omega)
    (by simp only [stackOf_length]; omega) hstack]
  congr 2
  · rw [stackOf_getElem_pc]
  · rw [stackOf_getElem_reg base regs pc next flag 0 hbase]

/-- One complete dispatcher iteration: the stack model advances by one URM
step, the answer is left on top for the pivot, and the direction pointer is
turned iff the run continues. -/
theorem runCode_dispatcherCode (base : Nat) (P : Program) {u u' : Cslib.URM.State}
    (hstep : Cslib.URM.Step P u u') (hbelow : ∀ x ∈ P, InstrBelow base x)
    (hbase : 0 < base) (s : MState) (next flag : Int)
    (hstack : s.stack = stackOf base u.regs (u.pc : Int) next flag) :
    ∃ f, runCode (dispatcherCode P base) s =
      { s with
        dp := if (u'.pc : Int) < (P.length : Int) then s.dp.clockwise else s.dp,
        cc := s.cc.toggle,
        stack := ((u'.regs 0 : Nat) : Int) ::
          stackOf base u'.regs (u'.pc : Int) (u'.pc : Int) f } := by
  obtain ⟨f, hdispatch⟩ := dispatchUpdate_step base P hstep hbelow flag
  refine ⟨f, ?_⟩
  simp only [dispatcherCode, runCode_append]
  rw [runCode_beginDispatch_stackOf base u.regs (u.pc : Int) next flag s hstack]
  rw [runCode_dispatchFrom_stackOf base P u.regs (u.pc : Int) ((u.pc : Int) + 1)
    flag _ hbelow rfl]
  rw [hdispatch]
  rw [runCode_endDispatch_stackOf base u'.regs (u.pc : Int) (u'.pc : Int) f _ rfl]
  rw [runCode_prepareBranch_stackOf base u'.regs (u'.pc : Int) (u'.pc : Int) f
    P.length hbase _ rfl]
  by_cases hrun : (u'.pc : Int) < (P.length : Int)
  · rw [if_pos hrun]
    rw [runCode_steerBranch_one ((u'.regs 0 : Nat) : Int)
      (stackOf base u'.regs (u'.pc : Int) (u'.pc : Int) f) _ rfl]
    rw [if_pos hrun]
  · rw [if_neg hrun]
    rw [runCode_steerBranch_zero ((u'.regs 0 : Nat) : Int)
      (stackOf base u'.regs (u'.pc : Int) (u'.pc : Int) f) _ rfl]
    rw [if_neg hrun]

/-- The colour after every command in a trace has executed. -/
def endColor : Hue → Lightness → List BlockCmd → Hue × Lightness
  | h, l, [] => (h, l)
  | h, l, c :: cs =>
      let next := advance h l c.op
      endColor next.1 next.2 cs

/-- A rectangular three-row grid assembled from row lists.  The loop
compiler uses equal row lengths; the row lookup lemmas below expose its
row-major representation to proofs. -/
def threeRowGrid (top middle bottom : List Codel) : Grid :=
  { width := top.length, height := 3,
    codels := (top ++ middle ++ bottom).toArray }

theorem threeRowGrid_get_top (top middle bottom : List Codel) (x : Nat)
    (hx : x < top.length) :
    (threeRowGrid top middle bottom).get x 0 = top[x] := by
  simp [threeRowGrid, Grid.get, hx]
  rw [List.getElem?_append_left hx, List.getElem?_eq_getElem hx]
  rfl

theorem threeRowGrid_get_middle (top middle bottom : List Codel) (x : Nat)
    (hx : x < top.length) (hmiddle : middle.length = top.length) :
    (threeRowGrid top middle bottom).get x 1 = middle[x]'(by omega) := by
  simp [threeRowGrid, Grid.get, hx, List.getElem?_append, hmiddle]
  split <;> (simp_all; try omega)

theorem threeRowGrid_get_bottom (top middle bottom : List Codel) (x : Nat)
    (hx : x < top.length) (hmiddle : middle.length = top.length)
    (hbottom : bottom.length = top.length) :
    (threeRowGrid top middle bottom).get x 2 = bottom[x]'(by omega) := by
  simp [threeRowGrid, Grid.get, hx, List.getElem?_append, hmiddle]
  split
  · omega
  · split
    · omega
    · have heq : 2 * top.length + x - top.length - top.length = x := by omega
      have hxb : x < bottom.length := by omega
      rw [heq, List.getElem?_eq_getElem hxb]
      rfl

structure LoopRows where
  top : List Codel
  middle : List Codel
  bottom : List Codel

def loopCode (body : List BlockCmd) : List BlockCmd :=
  pushNat 1 ++ [op .pop] ++ body

/-- The three concrete rows of the fixed dispatcher loop. -/
def loopRows (prologue body : List BlockCmd) : LoopRows :=
  let startH := Hue.red
  let startL := Lightness.normal
  let prologuePath := coloredRuns startH startL prologue
  let main := loopCode body
  let path := coloredRuns startH startL main
  let pivot := endColor startH startL main
  let outBlock := advance pivot.1 pivot.2 .outNum
  let loopBlock := advance pivot.1 pivot.2 .pop
  let terminal := Codel.chromatic Hue.yellow Lightness.dark
  let A := prologuePath.length
  let L := path.length
  { top := [.white] ++ prologuePath ++ [.white] ++ path ++
      [.chromatic outBlock.1 outBlock.2, .white, terminal]
    middle := List.replicate (A + 1) .black ++ [.white] ++
      List.replicate (L - 1) .black ++
      [.chromatic loopBlock.1 loopBlock.2, .black, terminal, terminal]
    bottom := List.replicate (A + 1) .black ++ List.replicate (L + 1) .white ++
      [.black, .black, .black] }

theorem loopRows_middle_length (prologue body : List BlockCmd) :
    (loopRows prologue body).middle.length = (loopRows prologue body).top.length := by
  simp only [loopRows, List.length_append, List.length_cons, List.length_nil,
    List.length_replicate]
  have hp : 0 < (coloredRuns Hue.red Lightness.normal
      (loopCode body)).length :=
    List.length_pos_of_ne_nil (coloredRuns_ne_nil Hue.red Lightness.normal _)
  omega

theorem loopRows_bottom_length (prologue body : List BlockCmd) :
    (loopRows prologue body).bottom.length = (loopRows prologue body).top.length := by
  simp only [loopRows, List.length_append, List.length_cons, List.length_nil,
    List.length_replicate]
  omega

/-- A fixed-loop codel layout for the branchless dispatcher.

Execution starts on white at `(0,0)` and slides right into the first source
block.  A running iteration turns down at the final pivot, executes `pop` on
the saved answer, and follows the white bottom/left return corridor.  A
halting iteration continues right, executes `outNum`, steps onto a white
codel and slides into the terminal colour block.

That block is the one place in a generated image where a single codel would
not do.  A singleton block can never halt: the program arrived from
somewhere, that somewhere is an unblocked neighbour, and one of the eight
exits steps back into it.  So the terminal is an L of three codels — the
top-right corner, the codel below it, and the codel to the left of that —
whose leftmost, bottommost and topmost extremes are all blocked by black or
by the edge, while the white codel the program entered through is adjacent
only to a member that is never selected as an exit. -/
def loopGrid (prologue body : List BlockCmd) : Grid :=
  let rows := loopRows prologue body
  threeRowGrid rows.top rows.middle rows.bottom

theorem loopGrid_get_prologue (prologue body : List BlockCmd) (j : Nat)
    (hj : j < (coloredRuns Hue.red Lightness.normal prologue).length) :
    (loopGrid prologue body).get (j + 1) 0 =
      (coloredRuns Hue.red Lightness.normal prologue)[j] := by
  let rows := loopRows prologue body
  have hx : j + 1 < rows.top.length := by
    simp [rows, loopRows]
    omega
  rw [loopGrid, threeRowGrid_get_top rows.top rows.middle rows.bottom (j + 1) hx]
  simp only [rows, loopRows]
  simp [hj]

theorem loopGrid_get_body (prologue body : List BlockCmd) (j : Nat)
    (hj : j < (coloredRuns Hue.red Lightness.normal
      (loopCode body)).length) :
    let A := (coloredRuns Hue.red Lightness.normal prologue).length
    (loopGrid prologue body).get (A + 2 + j) 0 =
      (coloredRuns Hue.red Lightness.normal
        (loopCode body))[j] := by
  dsimp only
  let rows := loopRows prologue body
  have hx : (coloredRuns Hue.red Lightness.normal prologue).length + 2 + j <
      rows.top.length := by
    simp [rows, loopRows]
    omega
  rw [loopGrid, threeRowGrid_get_top rows.top rows.middle rows.bottom _ hx]
  simp only [rows, loopRows]
  let prologuePath := coloredRuns Hue.red Lightness.normal prologue
  let path := coloredRuns Hue.red Lightness.normal (loopCode body)
  let tail :=
    [Codel.chromatic
        (advance (endColor Hue.red Lightness.normal (loopCode body)).1
          (endColor Hue.red Lightness.normal (loopCode body)).2 .outNum).1
        (advance (endColor Hue.red Lightness.normal (loopCode body)).1
          (endColor Hue.red Lightness.normal (loopCode body)).2 .outNum).2,
      .white, Codel.chromatic Hue.yellow Lightness.dark]
  let whole : List Codel :=
    (([Codel.white] ++ prologuePath ++ [Codel.white]) ++ path) ++ tail
  have hwhole : (coloredRuns Hue.red Lightness.normal prologue).length + 2 + j <
      whole.length := by simp [whole, prologuePath, path]; omega
  change whole[(coloredRuns Hue.red Lightness.normal prologue).length + 2 + j]'hwhole =
    path[j]'(by simpa [path] using hj)
  simp only [whole]
  rw [List.getElem_append_left (by simp [prologuePath, path]; omega)]
  rw [List.getElem_append_right (by simp [prologuePath])]
  have heq : (coloredRuns Hue.red Lightness.normal prologue).length + 2 + j -
      ([Codel.white] ++ prologuePath ++ [Codel.white]).length = j := by
    simp [prologuePath]
  simp only [heq]

theorem loopGrid_get_prologue_down (prologue body : List BlockCmd) (j : Nat)
    (hj : j < (coloredRuns Hue.red Lightness.normal prologue).length) :
    (loopGrid prologue body).get (j + 1) 1 = .black := by
  let rows := loopRows prologue body
  have hx : j + 1 < rows.top.length := by
    simp [rows, loopRows]
    omega
  rw [loopGrid, threeRowGrid_get_middle rows.top rows.middle rows.bottom
    (j + 1) hx (loopRows_middle_length prologue body)]
  simp only [rows, loopRows]
  simp [hj]

theorem loopGrid_get_body_down (prologue body : List BlockCmd) (j : Nat)
    (hj : j + 1 < (coloredRuns Hue.red Lightness.normal
      (loopCode body)).length) :
    let A := (coloredRuns Hue.red Lightness.normal prologue).length
    (loopGrid prologue body).get (A + 2 + j) 1 = .black := by
  dsimp only
  let rows := loopRows prologue body
  have hx : (coloredRuns Hue.red Lightness.normal prologue).length + 2 + j <
      rows.top.length := by
    simp [rows, loopRows]
    omega
  rw [loopGrid, threeRowGrid_get_middle rows.top rows.middle rows.bottom _ hx
    (loopRows_middle_length prologue body)]
  simp only [rows, loopRows]
  let A := (coloredRuns Hue.red Lightness.normal prologue).length
  let L := (coloredRuns Hue.red Lightness.normal (loopCode body)).length
  let tail : List Codel :=
    [Codel.chromatic
        (advance (endColor Hue.red Lightness.normal (loopCode body)).1
          (endColor Hue.red Lightness.normal (loopCode body)).2 .pop).1
        (advance (endColor Hue.red Lightness.normal (loopCode body)).1
          (endColor Hue.red Lightness.normal (loopCode body)).2 .pop).2,
      .black, Codel.chromatic Hue.yellow Lightness.dark,
      Codel.chromatic Hue.yellow Lightness.dark]
  let whole : List Codel :=
    ((List.replicate (A + 1) Codel.black ++ [Codel.white]) ++
      List.replicate (L - 1) Codel.black) ++ tail
  have hwhole : A + 2 + j < whole.length := by
    simp [whole, A, L]
    omega
  change whole[A + 2 + j]'hwhole = .black
  simp only [whole]
  rw [List.getElem_append_left (by simp [A, L]; omega)]
  rw [List.getElem_append_right (by simp [A])]
  have heq : A + 2 + j -
      (List.replicate (A + 1) Codel.black ++ [Codel.white]).length = j := by
    simp
  have hj' : j < (List.replicate (L - 1) Codel.black).length := by
    simp [L]
    omega
  simpa only [heq] using (List.getElem_replicate hj')

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

/-! ## Corridor geometry

`exec_unitCorridor` turns a `UnitCorridor` derivation into a statement about
the real evaluator.  This section builds those derivations from row lookups:
a run of singleton colour blocks along row zero, with black underneath, is a
corridor. -/

/-- Two colour blocks with different colours are different codels. -/
theorem chromatic_bne {h₁ h₂ : Hue} {l₁ l₂ : Lightness}
    (hne : (h₁, l₁) ≠ (h₂, l₂)) :
    (Codel.chromatic h₁ l₁ != Codel.chromatic h₂ l₂) = true := by
  cases h₁ <;> cases h₂ <;> cases l₁ <;> cases l₂ <;>
    first
      | rfl
      | exact absurd rfl hne

@[simp] theorem black_bne_chromatic (h : Hue) (l : Lightness) :
    (Codel.black != Codel.chromatic h l) = true := rfl

@[simp] theorem white_bne_chromatic (h : Hue) (l : Lightness) :
    (Codel.white != Codel.chromatic h l) = true := rfl

/-- The colour a unit corridor shows at offset `j`. -/
def colourAt (h : Hue) (l : Lightness) (code : List BlockCmd) (j : Nat) :
    Hue × Lightness := endColor h l (code.take j)

@[simp] theorem colourAt_zero (h : Hue) (l : Lightness) (code : List BlockCmd) :
    colourAt h l code 0 = (h, l) := by
  simp [colourAt, endColor]

theorem colourAt_cons_succ (h : Hue) (l : Lightness) (c : BlockCmd)
    (cs : List BlockCmd) (j : Nat) :
    colourAt h l (c :: cs) (j + 1) =
      colourAt (advance h l c.op).1 (advance h l c.op).2 cs j := by
  simp [colourAt, endColor]

/-- The codel a unit corridor shows at offset `j`. -/
theorem coloredRuns_getElem?_unit (h : Hue) (l : Lightness) (code : List BlockCmd)
    (hu : UnitCode code) (j : Nat) (hj : j ≤ code.length) :
    (coloredRuns h l code)[j]? =
      some (.chromatic (colourAt h l code j).1 (colourAt h l code j).2) := by
  induction code generalizing h l j with
  | nil =>
      have hj0 : j = 0 := by simpa using hj
      subst hj0
      simp [coloredRuns, colourAt, endColor]
  | cons c cs ih =>
      have hc : c.blockSize = 1 := hu c (by simp)
      have hcs : UnitCode cs := fun c' hc' => hu c' (by simp [hc'])
      cases j with
      | zero => simp [coloredRuns, hc, colourAt, endColor]
      | succ j =>
          have hj' : j ≤ cs.length := by simpa using hj
          simp only [colourAt_cons_succ, coloredRuns, hc, List.replicate_one,
            List.cons_append, List.getElem?_cons_succ, List.nil_append]
          exact ih (advance h l c.op).1 (advance h l c.op).2 hcs j hj'

/-- The neighbours of a codel on the top row. -/
theorem mem_neighbours_row0 (g : Grid) (x : Nat) (q : Nat × Nat)
    (hq : q ∈ neighbours g (x, 0)) :
    q = (x + 1, 0) ∨ q = (x, 1) ∨ (0 < x ∧ q = (x - 1, 0)) := by
  by_cases hr : x + 1 < g.width <;> by_cases hd : (0 : Nat) + 1 < g.height <;>
    by_cases hl : 0 < x <;>
    simp [neighbours, pushStep, step?, hr, hd, hl] at hq <;> tauto

/-- A row of singleton colour blocks with black underneath is a corridor. -/
theorem unitCorridor_of_row (g : Grid) (code : List BlockCmd) (hu : UnitCode code)
    (x : Nat) (h : Hue) (l : Lightness) (hheight : 1 < g.height)
    (hwidth : x + code.length < g.width)
    (hcolor : ∀ j, j ≤ code.length →
      g.get (x + j) 0 =
        .chromatic (colourAt h l code j).1 (colourAt h l code j).2)
    (hbelow : ∀ j, j < code.length → g.get (x + j) 1 = .black)
    (hleft : 0 < x → (g.get (x - 1) 0 != Codel.chromatic h l) = true) :
    UnitCorridor g x h l code := by
  induction code generalizing x h l with
  | nil => exact .nil x h l
  | cons c cs ih =>
      have hc : c.blockSize = 1 := hu c (by simp)
      have hcs : UnitCode cs := fun c' hc' => hu c' (by simp [hc'])
      have hcur : g.get x 0 = .chromatic h l := by
        simpa using hcolor 0 (by simp)
      have hnext : g.get (x + 1) 0 =
          .chromatic (advance h l c.op).1 (advance h l c.op).2 := by
        have hone := hcolor 1 (by simp)
        simpa [colourAt_cons_succ] using hone
      have hlenw : x + (c :: cs).length < g.width := hwidth
      have hxw : x + 1 < g.width := by simp only [List.length_cons] at hlenw; omega
      have hstep : step? g (x, 0) .right = some (x + 1, 0) := by
        simp [step?, hxw]
      have hdown : g.get x 1 = .black := by simpa using hbelow 0 (by simp)
      have hinfo : localInfoAt? g (x, 0) = some (singletonInfo (x, 0)) := by
        apply localInfoAt?_isolated g h l (x, 0) (by omega) (by omega) hcur
        intro q hq
        rcases mem_neighbours_row0 g x q hq with rfl | rfl | ⟨hx0, rfl⟩
        · rw [show ((x + 1, 0) : Nat × Nat).1 = x + 1 from rfl,
            show ((x + 1, 0) : Nat × Nat).2 = 0 from rfl, hnext]
          exact chromatic_bne (advance_ne h l c.op)
        · rw [show ((x, 1) : Nat × Nat).1 = x from rfl,
            show ((x, 1) : Nat × Nat).2 = 1 from rfl, hdown]
          rfl
        · exact hleft hx0
      refine .cons c cs hc hinfo hcur hstep hnext ?_
      apply ih hcs (x + 1) (advance h l c.op).1 (advance h l c.op).2
      · simp only [List.length_cons] at hlenw
        omega
      · intro j hj
        have hj1 := hcolor (j + 1) (by simpa using hj)
        simpa [colourAt_cons_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using hj1
      · intro j hj
        have hj1 := hbelow (j + 1) (by simpa using hj)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hj1
      · intro _
        simp only [Nat.add_sub_cancel]
        rw [hcur]
        exact chromatic_bne (Ne.symm (advance_ne h l c.op))

/-! ## White transits

Three of the four movements in a generated image are white slides: the
start, the separator that keeps the return corridor out of the prologue,
and the return corridor itself.  A slide executes no command; it only
moves, and each blocked turn rotates the direction pointer and toggles the
codel chooser. -/

/-- A slide that lands on the very next codel. -/
theorem slide_land_right (g : Grid) (fuel : Nat)
    (seen : List ((Nat × Nat) × Dir)) (x y : Nat) (cc : CC)
    (h : Hue) (l : Lightness)
    (hseen : seen.contains ((x, y), Dir.right) = false)
    (hstep : step? g (x, y) .right = some (x + 1, y))
    (hnext : g.get (x + 1) y = .chromatic h l) :
    slide g (fuel + 1) seen (x, y) .right cc = .landed (x + 1, y) .right cc := by
  simp only [slide, hseen, Bool.false_eq_true, if_false, hstep, hnext]

/-- A transition out of a singleton block onto white that slides to a
landing: no command runs, the position and direction come from the slide. -/
theorem tryFrom_white (g : Grid) (bl : Blocks) (s : MState)
    (h₁ : Hue) (l₁ : Lightness) (w p : Nat × Nat) (dp : Dir) (cc : CC)
    (hinfo : localInfoAt? g s.pos = some (singletonInfo s.pos))
    (hcurrent : g.get s.pos.1 s.pos.2 = .chromatic h₁ l₁)
    (hstep : step? g s.pos s.dp = some w)
    (hwhite : g.get w.1 w.2 = .white)
    (hslide : slide g (slideFuel g) [] w s.dp s.cc = .landed p dp cc) :
    tryFrom g bl 8 s = .ok { s with pos := p, dp := dp, cc := cc } := by
  rw [tryFrom, hinfo, hcurrent]
  simp only
  rw [singletonInfo_exit, hstep]
  simp only
  rw [hwhite]
  simp only
  rw [hslide]

/-- One unit of evaluator fuel follows a white transit. -/
theorem exec_white (g : Grid) (bl : Blocks) (fuel : Nat) (s : MState)
    (h₁ : Hue) (l₁ : Lightness) (w p : Nat × Nat) (dp : Dir) (cc : CC)
    (hinfo : localInfoAt? g s.pos = some (singletonInfo s.pos))
    (hcurrent : g.get s.pos.1 s.pos.2 = .chromatic h₁ l₁)
    (hstep : step? g s.pos s.dp = some w)
    (hwhite : g.get w.1 w.2 = .white)
    (hslide : slide g (slideFuel g) [] w s.dp s.cc = .landed p dp cc) :
    exec g bl (fuel + 1) s = exec g bl fuel { s with pos := p, dp := dp, cc := cc } := by
  rw [show fuel + 1 = Nat.succ fuel from rfl, exec,
    tryFrom_white g bl s h₁ l₁ w p dp cc hinfo hcurrent hstep hwhite hslide]

theorem contains_false_of_forall {α : Type} [BEq α] (l : List α) (a : α)
    (h : ∀ b ∈ l, (a == b) = false) : l.contains a = false := by
  induction l with
  | nil => rfl
  | cons b l ih =>
      simp only [List.contains_cons, Bool.or_eq_false_iff]
      exact ⟨h b (by simp), ih (fun c hc => h c (by simp [hc]))⟩

theorem dir_beq_of_ne {d d' : Dir} (h : d ≠ d') : (d == d') = false := by
  cases d <;> cases d' <;> first | rfl | exact absurd rfl h

theorem pair_beq_false (a b a' b' : Nat) (d d' : Dir)
    (h : a ≠ a' ∨ b ≠ b' ∨ d ≠ d') : (((a, b), d) == ((a', b'), d')) = false := by
  rcases h with h | h | h
  · simp [BEq.beq, h]
  · simp [BEq.beq, h]
  · simp only [BEq.beq]
    rw [show instBEqDir.beq d d' = (d == d') from rfl, dir_beq_of_ne h,
      Bool.and_false]

theorem clockwise_right : Dir.clockwise .right = .down := rfl
theorem clockwise_down : Dir.clockwise .down = .left := rfl
theorem clockwise_left : Dir.clockwise .left = .up := rfl
theorem clockwise_up : Dir.clockwise .up = .right := rfl

/-- Sliding left across a run of white codels. -/
theorem slide_left_run (g : Grid) (y : Nat) (cc : CC) :
    ∀ (n x fuel : Nat) (seen : List ((Nat × Nat) × Dir)),
      (∀ q ∈ seen, q.2 ≠ Dir.left ∨ x < q.1.1) →
      n ≤ x →
      (∀ j, j < n → g.get (x - j - 1) y = .white) →
      ∃ seen', (∀ q ∈ seen', q.2 ≠ Dir.left ∨ (x - n) < q.1.1) ∧
        (∀ q ∈ seen', q.2 = Dir.left ∨ q ∈ seen) ∧
        slide g (fuel + n) seen (x, y) .left cc =
          slide g fuel seen' (x - n, y) .left cc := by
  intro n
  induction n with
  | zero =>
      intro x fuel seen hseen _ _
      exact ⟨seen, by simpa using hseen, fun q hq => Or.inr hq, rfl⟩
  | succ n ih =>
      intro x fuel seen hseen hn hwhite
      have hx : 0 < x := by omega
      have hcontains : seen.contains ((x, y), Dir.left) = false := by
        apply contains_false_of_forall
        intro b hb
        obtain ⟨⟨bx, by'⟩, bd⟩ := b
        rcases hseen _ hb with h | h
        · exact pair_beq_false x y bx by' .left bd (Or.inr (Or.inr fun he => h he.symm))
        · exact pair_beq_false x y bx by' .left bd (Or.inl (by simp at h; omega))
      have hstep : step? g (x, y) .left = some (x - 1, y) := by simp [step?, hx]
      have hw0 : g.get (x - 1) y = .white := by
        have := hwhite 0 (by omega)
        simpa using this
      have hstep1 : slide g (fuel + (n + 1)) seen (x, y) .left cc =
          slide g (fuel + n) (((x, y), Dir.left) :: seen) (x - 1, y) .left cc := by
        rw [show fuel + (n + 1) = (fuel + n) + 1 from rfl]
        simp only [slide, hcontains, Bool.false_eq_true, if_false, hstep, hw0]
      obtain ⟨seen', hinv, hshape, heq⟩ := ih (x - 1) fuel (((x, y), Dir.left) :: seen)
        (by
          intro q hq
          rcases List.mem_cons.mp hq with rfl | hq
          · exact Or.inr (by simp; omega)
          · rcases hseen q hq with h | h
            · exact Or.inl h
            · exact Or.inr (by omega))
        (by omega)
        (by
          intro j hj
          have := hwhite (j + 1) (by omega)
          have harith : x - (j + 1) - 1 = x - 1 - j - 1 := by omega
          rwa [harith] at this)
      refine ⟨seen', ?_, ?_, ?_⟩
      · intro q hq
        rcases hinv q hq with h | h
        · exact Or.inl h
        · exact Or.inr (by omega)
      · intro q hq
        rcases hshape q hq with h | h
        · exact Or.inl h
        · rcases List.mem_cons.mp h with rfl | h
          · exact Or.inl rfl
          · exact Or.inr h
      · rw [hstep1, heq]
        congr 2
        omega

/-- The return corridor: down from the pivot's `pop`, left along the bottom
white run, up the white column, and back into the first codel of the loop
body.  Three blocked turns, so the codel chooser comes back toggled once. -/
theorem slide_return (g : Grid) (A L k : Nat) (cc : CC) (h : Hue) (l : Lightness)
    (_hL : 0 < L)
    (hdown : ∀ p, step? g (p, 2) .down = none)
    (hwhiteRun : ∀ j, j < L → g.get (A + 1 + L - j - 1) 2 = .white)
    (hblack : g.get A 2 = .black)
    (hup1 : g.get (A + 1) 1 = .white)
    (hup0 : g.get (A + 1) 0 = .white)
    (hbody : g.get (A + 2) 0 = .chromatic h l)
    (hwide : A + 2 < g.width) :
    slide g (k + (L + 6)) [] (A + 1 + L, 2) .down cc =
      .landed (A + 2, 0) .right cc.toggle := by
  -- 1. down is blocked by the bottom edge
  have s1 : slide g (k + (L + 6)) [] (A + 1 + L, 2) .down cc =
      slide g (k + 5 + L) [((A + 1 + L, 2), Dir.down)] (A + 1 + L, 2) .left
        cc.toggle := by
    rw [show k + (L + 6) = (k + 5 + L) + 1 from by omega]
    conv_lhs => rw [slide]
    simp only [List.contains_nil, Bool.false_eq_true, if_false, hdown,
      clockwise_down]
  -- 2. the left run along the bottom white corridor
  obtain ⟨seen', hinv, hshape, s2⟩ :=
    slide_left_run g 2 cc.toggle L (A + 1 + L) (k + 5)
      [((A + 1 + L, 2), Dir.down)]
      (by
        intro q hq
        simp only [List.mem_singleton] at hq
        subst hq
        exact Or.inl (by simp))
      (by omega) hwhiteRun
  have harith : A + 1 + L - L = A + 1 := by omega
  rw [harith] at s2 hinv
  -- a `contains` check fails whenever every entry differs in position or
  -- in direction
  have hfree : ∀ (p : Nat × Nat) (d : Dir) (sn : List ((Nat × Nat) × Dir)),
      (∀ q ∈ sn, p.1 ≠ q.1.1 ∨ p.2 ≠ q.1.2 ∨ d ≠ q.2) →
      sn.contains (p, d) = false := by
    intro p d sn hq
    apply contains_false_of_forall
    intro b hb
    obtain ⟨⟨bx, by'⟩, bd⟩ := b
    obtain ⟨px, py⟩ := p
    exact pair_beq_false px py bx by' d bd (hq _ hb)
  -- 3. left is blocked by the black codel under the prologue separator
  have c3 : seen'.contains ((A + 1, 2), Dir.left) = false := by
    apply hfree
    intro q hq
    rcases hinv _ hq with hd | hx
    · exact Or.inr (Or.inr fun he => hd he.symm)
    · exact Or.inl (by omega)
  have s3 : slide g (k + 5) seen' (A + 1, 2) .left cc.toggle =
      slide g (k + 4) (((A + 1, 2), Dir.left) :: seen') (A + 1, 2) .up
        cc.toggle.toggle := by
    rw [show k + 5 = (k + 4) + 1 from rfl]
    conv_lhs => rw [slide]
    simp only [c3, Bool.false_eq_true, if_false,
      show step? g (A + 1, 2) Dir.left = some (A, 2) from by simp [step?],
      hblack, clockwise_left]
  -- 4 and 5. up the white column
  have c4 : (((A + 1, 2), Dir.left) :: seen').contains ((A + 1, 2), Dir.up)
      = false := by
    apply hfree
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Or.inr (Or.inr (by simp))
    · rcases hshape _ hq with hd | hd
      · exact Or.inr (Or.inr (by simp [hd]))
      · simp only [List.mem_singleton] at hd
        subst hd
        exact Or.inr (Or.inr (by simp))
  have s4 : slide g (k + 4) (((A + 1, 2), Dir.left) :: seen') (A + 1, 2) .up
        cc.toggle.toggle =
      slide g (k + 3) (((A + 1, 2), Dir.up) :: ((A + 1, 2), Dir.left) :: seen')
        (A + 1, 1) .up cc.toggle.toggle := by
    rw [show k + 4 = (k + 3) + 1 from rfl]
    conv_lhs => rw [slide]
    simp only [c4, Bool.false_eq_true, if_false,
      show step? g (A + 1, 2) Dir.up = some (A + 1, 1) from by simp [step?],
      hup1]
  have c5 : (((A + 1, 2), Dir.up) :: ((A + 1, 2), Dir.left) :: seen').contains
      ((A + 1, 1), Dir.up) = false := by
    apply hfree
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Or.inr (Or.inl (by simp))
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Or.inr (Or.inl (by simp))
    · rcases hshape _ hq with hd | hd
      · exact Or.inr (Or.inr (by simp [hd]))
      · simp only [List.mem_singleton] at hd
        subst hd
        exact Or.inr (Or.inl (by simp))
  have s5 : slide g (k + 3) (((A + 1, 2), Dir.up) :: ((A + 1, 2), Dir.left) :: seen')
        (A + 1, 1) .up cc.toggle.toggle =
      slide g (k + 2) (((A + 1, 1), Dir.up) :: ((A + 1, 2), Dir.up) ::
          ((A + 1, 2), Dir.left) :: seen') (A + 1, 0) .up cc.toggle.toggle := by
    rw [show k + 3 = (k + 2) + 1 from rfl]
    conv_lhs => rw [slide]
    simp only [c5, Bool.false_eq_true, if_false,
      show step? g (A + 1, 1) Dir.up = some (A + 1, 0) from by simp [step?],
      hup0]
  -- 6. up is blocked by the top edge
  have c6 : (((A + 1, 1), Dir.up) :: ((A + 1, 2), Dir.up) ::
      ((A + 1, 2), Dir.left) :: seen').contains ((A + 1, 0), Dir.up) = false := by
    apply hfree
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Or.inr (Or.inl (by simp))
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Or.inr (Or.inl (by simp))
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Or.inr (Or.inl (by simp))
    · rcases hshape _ hq with hd | hd
      · exact Or.inr (Or.inr (by simp [hd]))
      · simp only [List.mem_singleton] at hd
        subst hd
        exact Or.inr (Or.inl (by simp))
  have s6 : slide g (k + 2) (((A + 1, 1), Dir.up) :: ((A + 1, 2), Dir.up) ::
        ((A + 1, 2), Dir.left) :: seen') (A + 1, 0) .up cc.toggle.toggle =
      slide g (k + 1) (((A + 1, 0), Dir.up) :: ((A + 1, 1), Dir.up) ::
          ((A + 1, 2), Dir.up) :: ((A + 1, 2), Dir.left) :: seen') (A + 1, 0)
        .right cc.toggle.toggle.toggle := by
    rw [show k + 2 = (k + 1) + 1 from rfl]
    conv_lhs => rw [slide]
    simp only [c6, Bool.false_eq_true, if_false,
      show step? g (A + 1, 0) Dir.up = none from by simp [step?],
      clockwise_up]
  -- 7. right lands on the first codel of the loop body
  have c7 : (((A + 1, 0), Dir.up) :: ((A + 1, 1), Dir.up) ::
      ((A + 1, 2), Dir.up) :: ((A + 1, 2), Dir.left) :: seen').contains
        ((A + 1, 0), Dir.right) = false := by
    apply hfree
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Or.inr (Or.inr (by simp))
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Or.inr (Or.inr (by simp))
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Or.inr (Or.inr (by simp))
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Or.inr (Or.inr (by simp))
    · rcases hshape _ hq with hd | hd
      · exact Or.inr (Or.inr (by simp [hd]))
      · simp only [List.mem_singleton] at hd
        subst hd
        exact Or.inr (Or.inr (by simp))
  have s7 : slide g (k + 1) (((A + 1, 0), Dir.up) :: ((A + 1, 1), Dir.up) ::
        ((A + 1, 2), Dir.up) :: ((A + 1, 2), Dir.left) :: seen') (A + 1, 0)
        .right cc.toggle.toggle.toggle =
      .landed (A + 2, 0) .right cc.toggle.toggle.toggle := by
    conv_lhs => rw [slide]
    simp only [c7, Bool.false_eq_true, if_false,
      show step? g (A + 1, 0) Dir.right = some (A + 2, 0) from by
        simp [step?]; omega,
      hbody]
  have hcc : cc.toggle.toggle.toggle = cc.toggle := by cases cc <;> rfl
  rw [s1, s2, s3, s4, s5, s6, s7, hcc]

/-! ## The terminal block

Every command codel in a generated image is an isolated singleton, which
`flood_singleton` already covers.  The one exception is the block the
program halts in, and it has to be an exception: a singleton block can
never halt, because the program arrived from somewhere, that somewhere is
an unblocked neighbour, and one of the eight exits steps back into it.

So the terminal is an L of three codels — the top-right corner, the codel
below it, and the codel to the left of that.  This section computes its
flood fill, its eight exits, and the halt. -/

theorem flood_nil (g : Grid) (color : Codel) (k : Nat) (v : Array Bool)
    (acc : List (Nat × Nat)) : flood g color k [] v acc = (v, acc) := by
  cases k <;> rfl

theorem codel_bne_self (c : Codel) : (c != c) = false := by
  cases c with
  | chromatic h l => cases h <;> cases l <;> rfl
  | white => rfl
  | black => rfl

theorem getElem!_replicate_false (n i : Nat) :
    (Array.replicate n false)[i]! = false := by
  rw [Array.getElem!_eq_getD, Array.getD]
  split
  · simp
  · rfl

theorem getElem!_set!_ne (a : Array Bool) (i j : Nat) (v : Bool) (h : i ≠ j) :
    (a.set! i v)[j]! = a[j]! := by
  simp only [Array.set!, Array.setIfInBounds]
  split
  · next hi =>
    rw [Array.getElem!_eq_getD, Array.getD, Array.getElem!_eq_getD, Array.getD]
    simp only [Array.size_set]
    split
    · next hj =>
      show (a.set i v hi)[j]'(by simpa using hj) = a[j]'hj
      rw [Array.getElem_set hi]
      simp [h]
    · rfl
  · rfl

theorem getElem!_set!_self (a : Array Bool) (i : Nat) (v : Bool) (h : i < a.size) :
    (a.set! i v)[i]! = v := by
  simp [Array.set!, Array.setIfInBounds, h]

/-- The flood fill on the L-shaped terminal block. -/
theorem flood_lblock (g : Grid) (color : Codel) (y k : Nat)
    (hw : g.width = y + 3) (hh : g.height = 3)
    (h00 : g.get (y + 2) 0 = color) (h01 : g.get (y + 2) 1 = color)
    (h11 : g.get (y + 1) 1 = color)
    (n0 : (g.get (y + 1) 0 != color) = true)
    (n1 : (g.get (y + 2) 2 != color) = true)
    (n2 : (g.get (y + 1) 2 != color) = true)
    (n3 : (g.get y 1 != color) = true) :
    (flood g color (k + 11) [(y + 2, 0)]
      (Array.replicate (g.width * g.height) false) []).2 =
      [(y + 1, 1), (y + 2, 1), (y + 2, 0)] := by
  have hsize : (Array.replicate (g.width * g.height) false).size = (y + 3) * 3 := by
    simp [hw, hh]
  -- neighbour lists
  have nb00 : neighbours g (y + 2, 0) = [(y + 1, 0), (y + 2, 1)] := by
    simp [neighbours, pushStep, step?, hw, hh]
  have nb01 : neighbours g (y + 2, 1) = [(y + 2, 0), (y + 1, 1), (y + 2, 2)] := by
    simp [neighbours, pushStep, step?, hw, hh]
  have nb11 : neighbours g (y + 1, 1) =
      [(y + 1, 0), (y, 1), (y + 1, 2), (y + 2, 1)] := by
    simp [neighbours, pushStep, step?, hw, hh]
  -- the visited-array bookkeeping: three distinct indices, all in range
  have hbound0 : 0 * g.width + (y + 2) <
      (Array.replicate (g.width * g.height) false).size := by
    rw [hsize]; omega
  have hne10 : 0 * g.width + (y + 2) ≠ 1 * g.width + (y + 2) := by rw [hw]; omega
  have hne01 : 1 * g.width + (y + 2) ≠ 0 * g.width + (y + 2) := by rw [hw]; omega
  have hne11 : 0 * g.width + (y + 2) ≠ 1 * g.width + (y + 1) := by rw [hw]; omega
  have hne21 : 1 * g.width + (y + 2) ≠ 1 * g.width + (y + 1) := by rw [hw]; omega
  have hne12 : 1 * g.width + (y + 1) ≠ 1 * g.width + (y + 2) := by rw [hw]; omega
  have hbound1 : 1 * g.width + (y + 2) <
      ((Array.replicate (g.width * g.height) false).set!
        (0 * g.width + (y + 2)) true).size := by
    rw [Array.set!, Array.size_setIfInBounds, hsize, hw]
    omega
  have a1 : ((Array.replicate (g.width * g.height) false).set!
      (0 * g.width + (y + 2)) true)[1 * g.width + (y + 2)]! = false := by
    rw [getElem!_set!_ne _ _ _ _ hne10, getElem!_replicate_false]
  have a2 : (((Array.replicate (g.width * g.height) false).set!
      (0 * g.width + (y + 2)) true).set!
      (1 * g.width + (y + 2)) true)[0 * g.width + (y + 2)]! = true := by
    rw [getElem!_set!_ne _ _ _ _ hne01, getElem!_set!_self _ _ _ hbound0]
  have a3 : (((Array.replicate (g.width * g.height) false).set!
      (0 * g.width + (y + 2)) true).set!
      (1 * g.width + (y + 2)) true)[1 * g.width + (y + 1)]! = false := by
    rw [getElem!_set!_ne _ _ _ _ hne21, getElem!_set!_ne _ _ _ _ hne11,
      getElem!_replicate_false]
  have a4 : ((((Array.replicate (g.width * g.height) false).set!
      (0 * g.width + (y + 2)) true).set!
      (1 * g.width + (y + 2)) true).set!
      (1 * g.width + (y + 1)) true)[1 * g.width + (y + 2)]! = true := by
    rw [getElem!_set!_ne _ _ _ _ hne12, getElem!_set!_self _ _ _ hbound1]
  -- ten flood steps, then an empty worklist
  rw [show k + 11 = k + 10 + 1 from rfl]
  simp only [flood, getElem!_replicate_false, h00, h01, h11, n0, n1, n2, n3,
    codel_bne_self, a1, a2, a3, a4, nb00, nb01, nb11,
    Bool.or_self, Bool.or_true, Bool.true_or, Bool.false_eq_true,
    if_false, if_true, List.append_nil, List.cons_append, List.nil_append]

/-- Block information for the L-shaped terminal block. -/
theorem localInfoAt?_lblock (g : Grid) (h : Hue) (l : Lightness) (y : Nat)
    (hw : g.width = y + 3) (hh : g.height = 3)
    (h00 : g.get (y + 2) 0 = .chromatic h l)
    (h01 : g.get (y + 2) 1 = .chromatic h l)
    (h11 : g.get (y + 1) 1 = .chromatic h l)
    (n0 : (g.get (y + 1) 0 != Codel.chromatic h l) = true)
    (n1 : (g.get (y + 2) 2 != Codel.chromatic h l) = true)
    (n2 : (g.get (y + 1) 2 != Codel.chromatic h l) = true)
    (n3 : (g.get y 1 != Codel.chromatic h l) = true) :
    localInfoAt? g (y + 2, 0) =
      some ⟨3, #[(y + 2, 0), (y + 2, 1), (y + 2, 1), (y + 1, 1),
        (y + 1, 1), (y + 1, 1), (y + 2, 0), (y + 2, 0)]⟩ := by
  have hfuel : 5 * (g.width * g.height) + 5 = (15 * y + 39) + 11 := by
    rw [hw, hh]; omega
  simp only [localInfoAt?, h00, hfuel]
  rw [show (flood g (Codel.chromatic h l) ((15 * y + 39) + 11) [(y + 2, 0)]
      (Array.replicate (g.width * g.height) false) []) =
    ((flood g (Codel.chromatic h l) ((15 * y + 39) + 11) [(y + 2, 0)]
      (Array.replicate (g.width * g.height) false) []).1,
     (flood g (Codel.chromatic h l) ((15 * y + 39) + 11) [(y + 2, 0)]
      (Array.replicate (g.width * g.height) false) []).2) from rfl]
  rw [flood_lblock g (.chromatic h l) y (15 * y + 39) hw hh h00 h01 h11 n0 n1 n2 n3]
  simp [mkInfo, betterFor]

/-- Every one of the terminal block's eight exits is blocked, so the
interpreter runs out of attempts and halts. -/
theorem tryFrom_lblock (g : Grid) (bl : Blocks) (h : Hue) (l : Lightness) (y : Nat)
    (hw : g.width = y + 3) (hh : g.height = 3)
    (h00 : g.get (y + 2) 0 = .chromatic h l)
    (h01 : g.get (y + 2) 1 = .chromatic h l)
    (h11 : g.get (y + 1) 1 = .chromatic h l)
    (n0 : (g.get (y + 1) 0 != Codel.chromatic h l) = true)
    (n1 : (g.get (y + 2) 2 != Codel.chromatic h l) = true)
    (n2 : (g.get (y + 1) 2 != Codel.chromatic h l) = true)
    (n3 : (g.get y 1 != Codel.chromatic h l) = true)
    (b1 : g.get (y + 2) 2 = .black) (b2 : g.get (y + 1) 2 = .black)
    (b3 : g.get y 1 = .black)
    (s : MState) (hpos : s.pos = (y + 2, 0)) :
    tryFrom g bl 8 s = .halt s := by
  have hinfo := localInfoAt?_lblock g h l y hw hh h00 h01 h11 n0 n1 n2 n3
  obtain ⟨pos, dp, cc, stack, input, output⟩ := s
  simp only at hpos
  subst hpos
  cases dp <;> cases cc <;>
    simp [tryFrom, hinfo, h00, b1, b2, b3, step?, hw, hh,
      Dir.clockwise, Dir.rotate, Dir.ofNat, Dir.toNat, CC.toggle, CC.toNat]

/-! ## Reading the generated grid

Each of these reads one codel of `loopGrid` out of the three row lists.
They are the interface between the layout and the run: everything above
this point is about lists, everything below is about the evaluator. -/

/-- Width of the prologue corridor, in codels. -/
def pw (prologue : List BlockCmd) : Nat :=
  (coloredRuns Hue.red Lightness.normal prologue).length

/-- Width of the loop-body corridor, in codels. -/
def bw (body : List BlockCmd) : Nat :=
  (coloredRuns Hue.red Lightness.normal (loopCode body)).length

theorem bw_pos (body : List BlockCmd) : 0 < bw body :=
  List.length_pos_of_ne_nil (coloredRuns_ne_nil _ _ _)

theorem top_length (prologue body : List BlockCmd) :
    (loopRows prologue body).top.length = pw prologue + bw body + 5 := by
  simp [loopRows, pw, bw]
  omega

theorem loopGrid_width (prologue body : List BlockCmd) :
    (loopGrid prologue body).width = pw prologue + bw body + 5 := by
  rw [loopGrid, threeRowGrid, top_length]

theorem loopGrid_height (prologue body : List BlockCmd) :
    (loopGrid prologue body).height = 3 := rfl

/-- Read a codel of the top row from the row list. -/
theorem loopGrid_top_of (prologue body : List BlockCmd) (x : Nat) (c : Codel)
    (hx : x < pw prologue + bw body + 5)
    (h : (loopRows prologue body).top[x]? = some c) :
    (loopGrid prologue body).get x 0 = c := by
  have hx' : x < (loopRows prologue body).top.length := by
    rw [top_length]; exact hx
  rw [loopGrid, threeRowGrid_get_top _ _ _ _ hx']
  rw [List.getElem?_eq_getElem hx'] at h
  exact Option.some.inj h

theorem loopGrid_middle_of (prologue body : List BlockCmd) (x : Nat) (c : Codel)
    (hx : x < pw prologue + bw body + 5)
    (h : (loopRows prologue body).middle[x]? = some c) :
    (loopGrid prologue body).get x 1 = c := by
  have hx' : x < (loopRows prologue body).top.length := by
    rw [top_length]; exact hx
  have hm : x < (loopRows prologue body).middle.length := by
    rw [loopRows_middle_length]; exact hx'
  rw [loopGrid, threeRowGrid_get_middle _ _ _ _ hx' (loopRows_middle_length _ _)]
  rw [List.getElem?_eq_getElem hm] at h
  exact Option.some.inj h

theorem loopGrid_bottom_of (prologue body : List BlockCmd) (x : Nat) (c : Codel)
    (hx : x < pw prologue + bw body + 5)
    (h : (loopRows prologue body).bottom[x]? = some c) :
    (loopGrid prologue body).get x 2 = c := by
  have hx' : x < (loopRows prologue body).top.length := by
    rw [top_length]; exact hx
  have hb : x < (loopRows prologue body).bottom.length := by
    rw [loopRows_bottom_length]; exact hx'
  rw [loopGrid, threeRowGrid_get_bottom _ _ _ _ hx' (loopRows_middle_length _ _)
    (loopRows_bottom_length _ _)]
  rw [List.getElem?_eq_getElem hb] at h
  exact Option.some.inj h

theorem loopGrid_get_start (prologue body : List BlockCmd) :
    (loopGrid prologue body).get 0 0 = .white := by
  apply loopGrid_top_of _ _ _ _ (by have := bw_pos body; omega)
  simp [loopRows]

theorem loopGrid_get_sep (prologue body : List BlockCmd) :
    (loopGrid prologue body).get (pw prologue + 1) 0 = .white := by
  apply loopGrid_top_of _ _ _ _ (by have := bw_pos body; omega)
  simp only [loopRows]
  rw [List.getElem?_append_left (by simp [pw]),
    List.getElem?_append_left (by simp [pw]),
    List.getElem?_append_right (by simp [pw])]
  simp [pw]

/-- The last three codels of the top row. -/
theorem loopRows_top_tail (prologue body : List BlockCmd) (j : Nat) :
    (loopRows prologue body).top[pw prologue + bw body + 2 + j]? =
      [Codel.chromatic
          (advance (endColor Hue.red Lightness.normal (loopCode body)).1
            (endColor Hue.red Lightness.normal (loopCode body)).2 .outNum).1
          (advance (endColor Hue.red Lightness.normal (loopCode body)).1
            (endColor Hue.red Lightness.normal (loopCode body)).2 .outNum).2,
        Codel.white, Codel.chromatic Hue.yellow Lightness.dark][j]? := by
  simp only [loopRows]
  rw [List.getElem?_append_right (by simp [pw, bw]; omega)]
  congr 1
  simp [pw, bw]
  omega

/-- The last four codels of the middle row. -/
theorem loopRows_middle_tail (prologue body : List BlockCmd) (j : Nat) :
    (loopRows prologue body).middle[pw prologue + bw body + 1 + j]? =
      [Codel.chromatic
          (advance (endColor Hue.red Lightness.normal (loopCode body)).1
            (endColor Hue.red Lightness.normal (loopCode body)).2 .pop).1
          (advance (endColor Hue.red Lightness.normal (loopCode body)).1
            (endColor Hue.red Lightness.normal (loopCode body)).2 .pop).2,
        Codel.black, Codel.chromatic Hue.yellow Lightness.dark,
        Codel.chromatic Hue.yellow Lightness.dark][j]? := by
  have hb := bw_pos body
  simp only [loopRows]
  rw [List.getElem?_append_right (by simp [pw, bw] at hb ⊢; omega)]
  congr 1
  simp [pw, bw] at hb ⊢
  omega

/-- The last three codels of the bottom row are all black. -/
theorem loopRows_bottom_tail (prologue body : List BlockCmd) (j : Nat) :
    (loopRows prologue body).bottom[pw prologue + bw body + 2 + j]? =
      [Codel.black, Codel.black, Codel.black][j]? := by
  simp only [loopRows]
  rw [List.getElem?_append_right (by simp [pw, bw]; omega)]
  congr 1
  simp [pw, bw]
  omega

/-- The block that prints the answer, at the end of the loop body. -/
theorem loopGrid_get_out (prologue body : List BlockCmd) :
    (loopGrid prologue body).get (pw prologue + bw body + 2) 0 =
      .chromatic
        (advance (endColor Hue.red Lightness.normal (loopCode body)).1
          (endColor Hue.red Lightness.normal (loopCode body)).2 .outNum).1
        (advance (endColor Hue.red Lightness.normal (loopCode body)).1
          (endColor Hue.red Lightness.normal (loopCode body)).2 .outNum).2 := by
  apply loopGrid_top_of _ _ _ _ (by omega)
  simpa using loopRows_top_tail prologue body 0

/-- The white codel between the printing block and the terminal. -/
theorem loopGrid_get_outWhite (prologue body : List BlockCmd) :
    (loopGrid prologue body).get (pw prologue + bw body + 3) 0 = .white := by
  apply loopGrid_top_of _ _ _ _ (by omega)
  have h := loopRows_top_tail prologue body 1
  rw [show pw prologue + bw body + 2 + 1 = pw prologue + bw body + 3 from rfl] at h
  simpa using h

theorem loopGrid_get_term00 (prologue body : List BlockCmd) :
    (loopGrid prologue body).get (pw prologue + bw body + 4) 0 =
      .chromatic Hue.yellow Lightness.dark := by
  apply loopGrid_top_of _ _ _ _ (by omega)
  have h := loopRows_top_tail prologue body 2
  rw [show pw prologue + bw body + 2 + 2 = pw prologue + bw body + 4 from rfl] at h
  simpa using h

/-- The white column the return corridor climbs. -/
theorem loopGrid_get_sepMiddle (prologue body : List BlockCmd) :
    (loopGrid prologue body).get (pw prologue + 1) 1 = .white := by
  apply loopGrid_middle_of _ _ _ _ (by have := bw_pos body; omega)
  simp only [loopRows, pw]
  rw [List.getElem?_append_left (by simp),
    List.getElem?_append_left (by simp),
    List.getElem?_append_right (by simp)]
  simp

/-- The `pop` block the loop turns down through. -/
theorem loopGrid_get_loopBlock (prologue body : List BlockCmd) :
    (loopGrid prologue body).get (pw prologue + bw body + 1) 1 =
      .chromatic
        (advance (endColor Hue.red Lightness.normal (loopCode body)).1
          (endColor Hue.red Lightness.normal (loopCode body)).2 .pop).1
        (advance (endColor Hue.red Lightness.normal (loopCode body)).1
          (endColor Hue.red Lightness.normal (loopCode body)).2 .pop).2 := by
  apply loopGrid_middle_of _ _ _ _ (by omega)
  simpa using loopRows_middle_tail prologue body 0

theorem loopGrid_get_midBlack (prologue body : List BlockCmd) :
    (loopGrid prologue body).get (pw prologue + bw body + 2) 1 = .black := by
  apply loopGrid_middle_of _ _ _ _ (by omega)
  have h := loopRows_middle_tail prologue body 1
  rw [show pw prologue + bw body + 1 + 1 = pw prologue + bw body + 2 from rfl] at h
  simpa using h

theorem loopGrid_get_term10 (prologue body : List BlockCmd) :
    (loopGrid prologue body).get (pw prologue + bw body + 3) 1 =
      .chromatic Hue.yellow Lightness.dark := by
  apply loopGrid_middle_of _ _ _ _ (by omega)
  have h := loopRows_middle_tail prologue body 2
  rw [show pw prologue + bw body + 1 + 2 = pw prologue + bw body + 3 from rfl] at h
  simpa using h

theorem loopGrid_get_term11 (prologue body : List BlockCmd) :
    (loopGrid prologue body).get (pw prologue + bw body + 4) 1 =
      .chromatic Hue.yellow Lightness.dark := by
  apply loopGrid_middle_of _ _ _ _ (by omega)
  have h := loopRows_middle_tail prologue body 3
  rw [show pw prologue + bw body + 1 + 3 = pw prologue + bw body + 4 from rfl] at h
  simpa using h

/-- The bottom white run the return corridor crosses. -/
theorem loopGrid_get_bottomWhite (prologue body : List BlockCmd) (j : Nat)
    (hj : j ≤ bw body) :
    (loopGrid prologue body).get (pw prologue + 1 + j) 2 = .white := by
  apply loopGrid_bottom_of _ _ _ _ (by omega)
  simp only [loopRows, pw, bw] at hj ⊢
  rw [List.getElem?_append_left (by simp; omega),
    List.getElem?_append_right (by simp)]
  rw [show (coloredRuns Hue.red Lightness.normal prologue).length + 1 + j -
      (List.replicate ((coloredRuns Hue.red Lightness.normal prologue).length + 1)
        Codel.black).length = j from by simp]
  rw [List.getElem?_eq_getElem (by simp; omega)]
  simp

/-- The black codel that stops the return corridor. -/
theorem loopGrid_get_bottomBlack (prologue body : List BlockCmd) :
    (loopGrid prologue body).get (pw prologue) 2 = .black := by
  apply loopGrid_bottom_of _ _ _ _ (by have := bw_pos body; omega)
  simp only [loopRows, pw]
  rw [List.getElem?_append_left (by simp; omega),
    List.getElem?_append_left (by simp)]
  simp

theorem loopGrid_get_bottomTail (prologue body : List BlockCmd) (j : Nat)
    (hj : j < 3) :
    (loopGrid prologue body).get (pw prologue + bw body + 2 + j) 2 = .black := by
  apply loopGrid_bottom_of _ _ _ _ (by omega)
  have h := loopRows_bottom_tail prologue body j
  rw [h]
  match j, hj with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl

/-- Landing in the terminal block ends the run. -/
theorem loopGrid_halt (prologue body : List BlockCmd) (bl : Blocks) (s : MState)
    (hpos : s.pos = (pw prologue + bw body + 4, 0)) :
    tryFrom (loopGrid prologue body) bl 8 s = .halt s := by
  have hb1 : (loopGrid prologue body).get (pw prologue + bw body + 4) 2 = .black := by
    have h := loopGrid_get_bottomTail prologue body 2 (by omega)
    rwa [show pw prologue + bw body + 2 + 2 = pw prologue + bw body + 4 from rfl] at h
  have hb2 : (loopGrid prologue body).get (pw prologue + bw body + 3) 2 = .black := by
    have h := loopGrid_get_bottomTail prologue body 1 (by omega)
    rwa [show pw prologue + bw body + 2 + 1 = pw prologue + bw body + 3 from rfl] at h
  exact tryFrom_lblock (loopGrid prologue body) bl Hue.yellow Lightness.dark
    (pw prologue + bw body + 2)
    (by rw [loopGrid_width]) (loopGrid_height _ _)
    (loopGrid_get_term00 prologue body)
    (loopGrid_get_term11 prologue body)
    (loopGrid_get_term10 prologue body)
    (by rw [loopGrid_get_outWhite]; rfl)
    (by rw [hb1]; rfl)
    (by rw [hb2]; rfl)
    (by rw [loopGrid_get_midBlack]; rfl)
    hb1 hb2 (loopGrid_get_midBlack prologue body) s hpos

/-- ... and the evaluator reports it. -/
theorem loopGrid_exec_halt (prologue body : List BlockCmd) (bl : Blocks)
    (fuel : Nat) (s : MState)
    (hpos : s.pos = (pw prologue + bw body + 4, 0)) :
    exec (loopGrid prologue body) bl (fuel + 1) s = (s, Exit.halted) := by
  rw [show fuel + 1 = Nat.succ fuel from rfl, exec,
    loopGrid_halt prologue body bl s hpos]

/-! ## Corridors on the generated grid

The prologue and the dispatcher body are both runs of singleton colour
blocks along the top row, so both are `UnitCorridor`s.  The body's last two
commands are the `switch` and the `pointer`, which move the chooser and the
direction and so cannot be part of a corridor; they are taken one at a
time below. -/

theorem unitize_append (a b : List BlockCmd) :
    unitize (a ++ b) = unitize a ++ unitize b := by
  simp [unitize, List.flatMap_append]

theorem colourAt_append_left (h : Hue) (l : Lightness) (a b : List BlockCmd)
    (j : Nat) (hj : j ≤ a.length) :
    colourAt h l (a ++ b) j = colourAt h l a j := by
  simp only [colourAt]
  rw [List.take_append_of_le_length hj]

theorem unitCode_append {a b : List BlockCmd} (ha : UnitCode a) (hb : UnitCode b) :
    UnitCode (a ++ b) := by
  intro c hc
  rcases List.mem_append.mp hc with h | h
  · exact ha c h
  · exact hb c h

/-- The prologue corridor: the run of singleton blocks that loads the
initial register file. -/
theorem loopGrid_prologue_corridor (prologue body : List BlockCmd)
    (hu : UnitCode prologue) :
    UnitCorridor (loopGrid prologue body) 1 Hue.red Lightness.normal prologue := by
  have hpw : pw prologue = prologue.length + 1 :=
    coloredRuns_length_of_unit _ _ _ hu
  apply unitCorridor_of_row _ _ hu
  · rw [loopGrid_height]; omega
  · rw [loopGrid_width]
    have := bw_pos body
    omega
  · intro j hj
    rw [show (1 : Nat) + j = j + 1 from by omega]
    have hj' : j < (coloredRuns Hue.red Lightness.normal prologue).length := by
      rw [coloredRuns_length_of_unit _ _ _ hu]; omega
    rw [loopGrid_get_prologue prologue body j hj']
    have hg := coloredRuns_getElem?_unit Hue.red Lightness.normal prologue hu j hj
    rw [List.getElem?_eq_getElem hj'] at hg
    exact Option.some.inj hg
  · intro j hj
    rw [show (1 : Nat) + j = j + 1 from by omega]
    exact loopGrid_get_prologue_down prologue body j
      (by rw [coloredRuns_length_of_unit _ _ _ hu]; omega)
  · intro _
    rw [show (1 : Nat) - 1 = 0 from rfl, loopGrid_get_start]
    rfl

/-- The body corridor: every command of the dispatcher up to, but not
including, the two that move the pointer and the chooser. -/
theorem loopGrid_body_corridor (prologue body : List BlockCmd)
    (hu : UnitCode (loopCode body)) (stable rest : List BlockCmd)
    (hsplit : loopCode body = stable ++ rest) (hne : rest ≠ []) :
    UnitCorridor (loopGrid prologue body) (pw prologue + 2) Hue.red
      Lightness.normal stable := by
  have hbw : bw body = (loopCode body).length + 1 :=
    coloredRuns_length_of_unit _ _ _ hu
  have hlen : stable.length + rest.length = (loopCode body).length := by
    rw [hsplit]; simp
  have hrest : 0 < rest.length := List.length_pos_of_ne_nil hne
  have hus : UnitCode stable := fun c hc =>
    hu c (by rw [hsplit]; exact List.mem_append_left _ hc)
  apply unitCorridor_of_row _ _ hus
  · rw [loopGrid_height]; omega
  · rw [loopGrid_width]; omega
  · intro j hj
    have hjb : j < (coloredRuns Hue.red Lightness.normal (loopCode body)).length := by
      show j < bw body
      omega
    have h := loopGrid_get_body prologue body j hjb
    simp only at h
    rw [show pw prologue + 2 + j =
      (coloredRuns Hue.red Lightness.normal prologue).length + 2 + j from rfl, h]
    have hg := coloredRuns_getElem?_unit Hue.red Lightness.normal (loopCode body) hu j
      (by omega)
    rw [List.getElem?_eq_getElem hjb] at hg
    rw [Option.some.inj hg, hsplit, colourAt_append_left _ _ _ _ _ hj]
  · intro j hj
    have h := loopGrid_get_body_down prologue body j
      (by show j + 1 < bw body; omega)
    simp only at h
    exact h
  · intro _
    rw [show pw prologue + 2 - 1 = pw prologue + 1 from by omega, loopGrid_get_sep]
    rfl

/-- Consecutive corridor colours differ: every Piet command changes the
colour, which is what makes each singleton codel its own block. -/
theorem colourAt_succ_ne (h : Hue) (l : Lightness) (code : List BlockCmd)
    (j : Nat) (hj : j < code.length) :
    colourAt h l code (j + 1) ≠ colourAt h l code j := by
  induction code generalizing h l j with
  | nil => simp at hj
  | cons c cs ih =>
      cases j with
      | zero =>
          simp only [colourAt_cons_succ, colourAt_zero]
          exact advance_ne h l c.op
      | succ j =>
          simp only [colourAt_cons_succ]
          exact ih _ _ j (by simpa using hj)

/-- Isolation of a top-row codel, from its three neighbours. -/
theorem localInfoAt?_top (g : Grid) (h : Hue) (l : Lightness) (x : Nat)
    (hx : x < g.width) (hh : 1 < g.height)
    (hcur : g.get x 0 = .chromatic h l)
    (hleft : 0 < x → (g.get (x - 1) 0 != Codel.chromatic h l) = true)
    (hright : (g.get (x + 1) 0 != Codel.chromatic h l) = true)
    (hdown : (g.get x 1 != Codel.chromatic h l) = true) :
    localInfoAt? g (x, 0) = some (singletonInfo (x, 0)) := by
  apply localInfoAt?_isolated g h l (x, 0) (by omega) (by omega) hcur
  intro q hq
  rcases mem_neighbours_row0 g x q hq with rfl | rfl | ⟨hx0, rfl⟩
  · exact hright
  · exact hdown
  · exact hleft hx0

theorem colourAt_full (h : Hue) (l : Lightness) (code : List BlockCmd) :
    colourAt h l code code.length = endColor h l code := by
  simp [colourAt]

/-- The colour of the body corridor at each offset, including the pivot. -/
theorem loopGrid_body_colour (prologue body : List BlockCmd)
    (hu : UnitCode (loopCode body)) (j : Nat) (hj : j ≤ (loopCode body).length) :
    (loopGrid prologue body).get (pw prologue + 2 + j) 0 =
      .chromatic (colourAt Hue.red Lightness.normal (loopCode body) j).1
        (colourAt Hue.red Lightness.normal (loopCode body) j).2 := by
  have hbw : bw body = (loopCode body).length + 1 :=
    coloredRuns_length_of_unit _ _ _ hu
  have hjb : j < (coloredRuns Hue.red Lightness.normal (loopCode body)).length := by
    show j < bw body
    omega
  have h := loopGrid_get_body prologue body j hjb
  simp only at h
  rw [show pw prologue + 2 + j =
    (coloredRuns Hue.red Lightness.normal prologue).length + 2 + j from rfl, h]
  have hg := coloredRuns_getElem?_unit Hue.red Lightness.normal (loopCode body) hu j hj
  rw [List.getElem?_eq_getElem hjb] at hg
  exact Option.some.inj hg

/-- Every codel of the body corridor is its own colour block, the pivot
included: below it is either black or the `pop` block, and both differ from
it in colour. -/
theorem loopGrid_body_isolated (prologue body : List BlockCmd)
    (hu : UnitCode (loopCode body)) (j : Nat) (hj : j ≤ (loopCode body).length) :
    localInfoAt? (loopGrid prologue body) (pw prologue + 2 + j, 0) =
      some (singletonInfo (pw prologue + 2 + j, 0)) := by
  have hbw : bw body = (loopCode body).length + 1 :=
    coloredRuns_length_of_unit _ _ _ hu
  have hcur := loopGrid_body_colour prologue body hu j hj
  apply localInfoAt?_top _ _ _ _ (by rw [loopGrid_width]; omega)
    (by rw [loopGrid_height]; omega) hcur
  · -- the codel to the left
    intro _
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [show pw prologue + 2 + 0 - 1 = pw prologue + 1 from by omega,
        loopGrid_get_sep]
      rfl
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      rw [show pw prologue + 2 + (i + 1) - 1 = pw prologue + 2 + i from by omega,
        loopGrid_body_colour prologue body hu i (by omega)]
      apply chromatic_bne
      exact fun he => colourAt_succ_ne Hue.red Lightness.normal (loopCode body) i
        (by omega) he.symm
  · -- the codel to the right
    rcases Nat.lt_or_ge j (loopCode body).length with hlt | hge
    · rw [show pw prologue + 2 + j + 1 = pw prologue + 2 + (j + 1) from by omega,
        loopGrid_body_colour prologue body hu (j + 1) (by omega)]
      apply chromatic_bne
      exact colourAt_succ_ne Hue.red Lightness.normal (loopCode body) j (by omega)
    · have hjeq : j = (loopCode body).length := by omega
      subst hjeq
      rw [show pw prologue + 2 + (loopCode body).length =
        pw prologue + bw body + 1 from by omega]
      rw [show pw prologue + bw body + 1 + 1 = pw prologue + bw body + 2 from rfl,
        loopGrid_get_out]
      rw [colourAt_full] at hcur ⊢
      apply chromatic_bne
      exact advance_ne _ _ _
  · -- the codel below
    rcases Nat.lt_or_ge j (loopCode body).length with hlt | hge
    · have hd := loopGrid_get_body_down prologue body j
        (by show j + 1 < bw body; omega)
      simp only at hd
      rw [show pw prologue + 2 + j =
        (coloredRuns Hue.red Lightness.normal prologue).length + 2 + j from rfl, hd]
      rfl
    · have hjeq : j = (loopCode body).length := by omega
      subst hjeq
      rw [show pw prologue + 2 + (loopCode body).length =
        pw prologue + bw body + 1 from by omega, loopGrid_get_loopBlock]
      rw [colourAt_full] at hcur ⊢
      apply chromatic_bne
      exact advance_ne _ _ _

/-! ## Which generated code a corridor may contain

A corridor keeps the direction pointer and the codel chooser fixed, so it
may not contain `pointer` or `switch`.  Everything the dispatcher emits
satisfies that except the two commands at the very end, and these lemmas
say so, generator by generator. -/

theorem stableCode_nil : StableCode [] := by intro c hc; simp at hc

theorem stableCode_append {a b : List BlockCmd} (ha : StableCode a)
    (hb : StableCode b) : StableCode (a ++ b) := by
  intro c hc
  rcases List.mem_append.mp hc with h | h
  · exact ha c h
  · exact hb c h

theorem stableCode_single {o : Op} (h : o ≠ .pointer ∧ o ≠ .switch) :
    StableCode [op o] := by
  intro c hc
  simp only [List.mem_singleton] at hc
  subst hc
  exact h

theorem stableCode_pushNat (n : Nat) : StableCode (pushNat n) := by
  intro c hc
  simp only [pushNat] at hc
  split at hc <;> simp at hc
  · rcases hc with rfl | rfl | rfl <;> exact ⟨by simp [op], by simp [op]⟩
  · subst hc; exact ⟨by simp, by simp⟩

theorem stableCode_rollNat (rolls depth : Nat) : StableCode (rollNat rolls depth) := by
  intro c hc
  simp only [rollNat, List.mem_append] at hc
  rcases hc with (h | h) | h
  · exact stableCode_pushNat _ c h
  · exact stableCode_pushNat _ c h
  · simp only [List.mem_singleton] at h
    subst h
    exact ⟨by simp [op], by simp [op]⟩

theorem stableCode_addUnit (n : Nat) : StableCode (addUnit n) := by
  induction n with
  | zero => simp [addUnit]; exact stableCode_nil
  | succ n ih =>
      rw [addUnit]
      apply stableCode_append ih
      intro c hc
      simp at hc
      rcases hc with rfl | rfl <;> exact ⟨by simp [op], by simp [op]⟩

theorem stableCode_pushNatUnit (n : Nat) : StableCode (pushNatUnit n) := by
  cases n with
  | zero => intro c hc; simp [pushNatUnit] at hc; rcases hc with rfl | rfl | rfl <;>
      exact ⟨by simp [op], by simp [op]⟩
  | succ n =>
      intro c hc
      rw [pushNatUnit] at hc
      rcases List.mem_cons.mp hc with rfl | h
      · exact ⟨by simp [op], by simp [op]⟩
      · exact stableCode_addUnit n c h

theorem stableCode_unitize {code : List BlockCmd} (h : StableCode code) :
    StableCode (unitize code) := by
  intro c hc
  simp only [unitize, List.mem_flatMap] at hc
  obtain ⟨d, hd, hc⟩ := hc
  have hdst := h d hd
  simp only [unitizeCmd] at hc
  cases hop : d.op <;> rw [hop] at hc <;>
    first
      | exact stableCode_pushNatUnit _ c hc
      | exact absurd hop hdst.1
      | exact absurd hop hdst.2
      | (simp only [List.mem_singleton] at hc
         subst hc
         exact ⟨by simp [op], by simp [op]⟩)

/-- A list of commands, none of which moves the pointer or the chooser. -/
theorem stableCode_ops (ops : List Op)
    (h : ∀ o ∈ ops, o ≠ .pointer ∧ o ≠ .switch) : StableCode (ops.map op) := by
  intro c hc
  simp only [List.mem_map] at hc
  obtain ⟨o, ho, rfl⟩ := hc
  exact h o ho

theorem stableCode_storeTop (r : Nat) : StableCode (storeTop r) := by
  unfold storeTop
  repeat' apply stableCode_append
  all_goals first
    | exact stableCode_rollNat _ _
    | exact stableCode_pushNat _
    | (apply stableCode_single; exact ⟨by simp, by simp⟩)

theorem stableCode_copyAt (R r : Nat) : StableCode (copyAt R r) := by
  unfold copyAt
  repeat' apply stableCode_append
  all_goals first
    | exact stableCode_rollNat _ _
    | exact stableCode_pushNat _
    | (apply stableCode_single; exact ⟨by simp, by simp⟩)

theorem stableCode_pair {o₁ o₂ : Op} (h₁ : o₁ ≠ .pointer ∧ o₁ ≠ .switch)
    (h₂ : o₂ ≠ .pointer ∧ o₂ ≠ .switch) : StableCode [op o₁, op o₂] := by
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · exact h₁
  · exact h₂

/-- Every generator below is a concatenation of these six shapes. -/
syntax "stable_tac" : tactic
macro_rules
  | `(tactic| stable_tac) =>
    `(tactic|
      (repeat' apply stableCode_append)
      <;> first
        | exact stableCode_copyAt _ _
        | exact stableCode_storeTop _
        | exact stableCode_rollNat _ _
        | exact stableCode_pushNat _
        | (apply stableCode_single; exact ⟨by simp, by simp⟩)
        | (apply stableCode_pair <;> exact ⟨by simp, by simp⟩))

theorem stableCode_beginDispatch (N pc next : Nat) :
    StableCode (beginDispatch N pc next) := by
  unfold beginDispatch
  stable_tac

theorem stableCode_selectInstr (N pc flag i : Nat) :
    StableCode (selectInstr N pc flag i) := by
  unfold selectInstr
  stable_tac

theorem stableCode_guardedZ (N flag r : Nat) : StableCode (guardedZ N flag r) := by
  unfold guardedZ
  stable_tac

theorem stableCode_guardedS (N flag r : Nat) : StableCode (guardedS N flag r) := by
  unfold guardedS
  stable_tac

theorem stableCode_guardedT (N flag m r : Nat) : StableCode (guardedT N flag m r) := by
  unfold guardedT
  stable_tac

theorem stableCode_guardedEq (N flag m r : Nat) : StableCode (guardedEq N flag m r) := by
  unfold guardedEq
  stable_tac

theorem stableCode_guardedNextLeft (N next flag : Nat) :
    StableCode (guardedNextLeft N next flag) := by
  unfold guardedNextLeft
  stable_tac

theorem stableCode_guardedNext (N next flag q : Nat) :
    StableCode (guardedNext N next flag q) := by
  refine stableCode_append (stableCode_append (stableCode_append
    (stableCode_append (stableCode_guardedNextLeft _ _ _)
      (stableCode_copyAt _ _)) (stableCode_pushNat _)) ?_)
    (stableCode_storeTop _)
  apply stableCode_pair <;> exact ⟨by simp, by simp⟩

theorem stableCode_guardedJ (N next flag m r q : Nat) :
    StableCode (guardedJ N next flag m r q) := by
  unfold guardedJ
  exact stableCode_append (stableCode_guardedEq _ _ _ _)
    (stableCode_guardedNext _ _ _ _)

theorem stableCode_guardedInstr (N next flag : Nat) (instr : Cslib.URM.Instr) :
    StableCode (guardedInstr N next flag instr) := by
  cases instr with
  | Z r => exact stableCode_guardedZ _ _ _
  | S r => exact stableCode_guardedS _ _ _
  | T m r => exact stableCode_guardedT _ _ _ _
  | J m r q => exact stableCode_guardedJ _ _ _ _ _ _

theorem stableCode_dispatchFrom (N pc next flag : Nat) :
    ∀ (i : Nat) (P : Cslib.URM.Program), StableCode (dispatchFrom N pc next flag i P)
  | _, [] => stableCode_nil
  | i, instr :: rest => by
      rw [dispatchFrom]
      exact stableCode_append (stableCode_append (stableCode_selectInstr _ _ _ _)
        (stableCode_guardedInstr _ _ _ _))
        (stableCode_dispatchFrom N pc next flag (i + 1) rest)

theorem stableCode_endDispatch (N pc next : Nat) :
    StableCode (endDispatch N pc next) := by
  unfold endDispatch
  stable_tac

theorem stableCode_prepareBranch (N pc programLength : Nat) :
    StableCode (prepareBranch N pc programLength) := by
  unfold prepareBranch
  stable_tac

theorem stableCode_initialCode (R : Nat) (inputs : List Nat) :
    StableCode (initialCode R inputs) := by
  intro c hc
  simp only [initialCode, List.mem_flatMap] at hc
  obtain ⟨n, _, hn⟩ := hc
  exact stableCode_pushNat n c hn

/-- The loop body splits into a corridor-safe prefix and the two commands
that move the pointer and the chooser. -/
theorem loopCode_dispatcher_split (P : Cslib.URM.Program) (base : Nat) :
    ∃ stable, loopCode (unitize (dispatcherCode P base)) =
        stable ++ [op .switch, op .pointer] ∧ StableCode stable := by
  refine ⟨pushNat 1 ++ [op .pop] ++
    unitize (beginDispatch (base + 3) base (base + 1) ++
      dispatchFrom (base + 3) base (base + 1) (base + 2) 0 P ++
      endDispatch (base + 3) base (base + 1) ++
      prepareBranch (base + 3) base P.length) ++ unitize (pushNat 1), ?_, ?_⟩
  · simp only [loopCode, dispatcherCode, steerBranch, unitize_append]
    simp [unitize, unitizeCmd, op, List.append_assoc]
  · have hD : StableCode (beginDispatch (base + 3) base (base + 1) ++
        dispatchFrom (base + 3) base (base + 1) (base + 2) 0 P ++
        endDispatch (base + 3) base (base + 1) ++
        prepareBranch (base + 3) base P.length) :=
      stableCode_append (stableCode_append (stableCode_append
        (stableCode_beginDispatch _ _ _) (stableCode_dispatchFrom _ _ _ _ _ _))
        (stableCode_endDispatch _ _ _)) (stableCode_prepareBranch _ _ _)
    have hpop : StableCode [op Op.pop] := stableCode_single ⟨by simp, by simp⟩
    exact stableCode_append (stableCode_append (stableCode_append
      (stableCode_pushNat 1) hpop) (stableCode_unitize hD))
      (stableCode_unitize (stableCode_pushNat 1))

theorem unitCode_pushNat_one : UnitCode (pushNat 1) := by
  intro c hc
  simp [pushNat] at hc
  subst hc
  rfl

theorem unitCode_op (o : Op) : UnitCode [op o] := by
  intro c hc
  simp at hc
  subst hc
  rfl

/-- Every command source in the generated loop occupies one codel. -/
theorem unitCode_loopCode (code : List BlockCmd) :
    UnitCode (loopCode (unitize code)) := by
  unfold loopCode
  apply unitCode_append (unitCode_append unitCode_pushNat_one (unitCode_op _))
  exact unitCode_unitize code

/-! ## One pass of the dispatcher body

The corridor, then the two commands a corridor may not contain. -/

/-- The colour after the command at offset `j`. -/
theorem colourAt_step (h : Hue) (l : Lightness) (code : List BlockCmd) (j : Nat)
    (hj : j < code.length) :
    colourAt h l code (j + 1) =
      advance (colourAt h l code j).1 (colourAt h l code j).2 (code[j]).op := by
  induction code generalizing h l j with
  | nil => simp at hj
  | cons c cs ih =>
      cases j with
      | zero => simp [colourAt_cons_succ, colourAt_zero]
      | succ j =>
          simp only [colourAt_cons_succ, List.getElem_cons_succ]
          exact ih _ _ j (by simpa using hj)

/-- One command transition along the body corridor, in any direction. -/
theorem loopGrid_body_exec (prologue body : List BlockCmd)
    (hu : UnitCode (loopCode body)) (bl : Blocks) (j : Nat)
    (hj : j < (loopCode body).length) (fuel : Nat) (s : MState)
    (hpos : s.pos = (pw prologue + 2 + j, 0)) (hdp : s.dp = .right) :
    exec (loopGrid prologue body) bl (fuel + 1) s =
      exec (loopGrid prologue body) bl fuel
        (execOp ((loopCode body)[j]).op 1
          { s with pos := (pw prologue + 2 + j + 1, 0) }) := by
  obtain ⟨pos, dp, cc, stack, input, output⟩ := s
  simp only at hpos hdp
  subst hpos
  subst hdp
  have hbw : bw body = (loopCode body).length + 1 :=
    coloredRuns_length_of_unit _ _ _ hu
  have hcur := loopGrid_body_colour prologue body hu j (by omega)
  have hnext := loopGrid_body_colour prologue body hu (j + 1) (by omega)
  rw [colourAt_step Hue.red Lightness.normal (loopCode body) j hj] at hnext
  apply exec_singleton _ _ _ _ _ _ _ _ _ _
    (loopGrid_body_isolated prologue body hu j (by omega))
  · exact hcur
  · simp only [step?]
    rw [if_pos (by rw [loopGrid_width]; omega)]
  · rw [show pw prologue + 2 + j + 1 = pw prologue + 2 + (j + 1) from by omega]
    exact hnext
  · exact opFor_advance _ _ _

theorem runCode_dp_of_stable (code : List BlockCmd) (hst : StableCode code) :
    ∀ s : MState, (runCode code s).dp = s.dp := by
  induction code with
  | nil => intro s; rfl
  | cons c cs ih =>
      intro s
      have hc := hst c (by simp)
      have hcs : StableCode cs := fun c' hc' => hst c' (by simp [hc'])
      rw [runCode, ih hcs]
      exact execOp_dp_of_ne_pointer c.op c.blockSize s hc.1

/-- The whole dispatcher body, run from the first codel of the loop to the
pivot: the corridor, then the `switch` and the `pointer`. -/
theorem exec_toPivot (prologue body : List BlockCmd) (hu : UnitCode (loopCode body))
    (stable : List BlockCmd)
    (hsplit : loopCode body = stable ++ [op .switch, op .pointer])
    (hstable : StableCode stable)
    (bl : Blocks) (fuel : Nat) (s : MState)
    (hpos : s.pos = (pw prologue + 2, 0)) (hdp : s.dp = .right) :
    exec (loopGrid prologue body) bl (fuel + (loopCode body).length) s =
      exec (loopGrid prologue body) bl fuel
        { runCode (loopCode body) s with
          pos := (pw prologue + bw body + 1, 0) } := by
  have hbw : bw body = (loopCode body).length + 1 :=
    coloredRuns_length_of_unit _ _ _ hu
  have hlen : (loopCode body).length = stable.length + 2 := by
    rw [hsplit]; simp
  have hcorr := loopGrid_body_corridor prologue body hu stable
    [op .switch, op .pointer] hsplit (by simp)
  -- the corridor
  rw [show fuel + (loopCode body).length = (fuel + 2) + stable.length from by omega]
  rw [exec_unitCorridor _ bl _ _ _ _ hcorr hstable (fuel + 2) s hpos hdp]
  -- the switch
  have hsw : (loopCode body)[stable.length]'(by omega) = op .switch := by
    have h : (loopCode body)[stable.length]? = some (op .switch) := by
      rw [hsplit, List.getElem?_append_right (by simp)]
      simp
    rw [List.getElem?_eq_getElem (by omega)] at h
    exact Option.some.inj h
  have hpt : (loopCode body)[stable.length + 1]'(by omega) = op .pointer := by
    have h : (loopCode body)[stable.length + 1]? = some (op .pointer) := by
      rw [hsplit, List.getElem?_append_right (by simp)]
      simp
    rw [List.getElem?_eq_getElem (by omega)] at h
    exact Option.some.inj h
  rw [show fuel + 2 = (fuel + 1) + 1 from rfl]
  rw [loopGrid_body_exec prologue body hu bl stable.length (by omega) (fuel + 1) _
    (by simp) (by simp [runCode_dp_of_stable stable hstable, hdp])]
  rw [hsw]
  -- the pointer
  rw [loopGrid_body_exec prologue body hu bl (stable.length + 1) (by omega) fuel _
    (by simp [op, execOp_set_pos]; try omega)
    (by
      simp only [op]
      rw [execOp_dp_of_ne_pointer _ _ _ (by simp)]
      simp [runCode_dp_of_stable stable hstable, hdp])]
  rw [hpt, hsplit, runCode_append]
  simp only [runCode, op, BlockCmd.blockSize, execOp_set_pos]
  congr 2
  rw [show pw prologue + 2 + (stable.length + 1) + 1 =
    pw prologue + bw body + 1 from by omega]

/-! ## The two branches out of the pivot

`pointer` has consumed the running flag, so the direction pointer is either
still right, in which case the run prints the answer and slides into the
terminal, or turned down, in which case it pops the answer and follows the
return corridor back to the first codel of the loop body. -/

/-- The neighbours of any codel. -/
theorem mem_neighbours_any (g : Grid) (x y : Nat) (q : Nat × Nat)
    (hq : q ∈ neighbours g (x, y)) :
    q = (x + 1, y) ∨ q = (x, y + 1) ∨ (0 < x ∧ q = (x - 1, y)) ∨
      (0 < y ∧ q = (x, y - 1)) := by
  by_cases hr : x + 1 < g.width <;> by_cases hd : y + 1 < g.height <;>
    by_cases hl : 0 < x <;> by_cases hu : 0 < y <;>
    simp [neighbours, pushStep, step?, hr, hd, hl, hu] at hq <;> tauto

/-- Isolation of a codel from its four neighbours. -/
theorem localInfoAt?_any (g : Grid) (h : Hue) (l : Lightness) (x y : Nat)
    (hx : x < g.width) (hy : y < g.height)
    (hcur : g.get x y = .chromatic h l)
    (hright : (g.get (x + 1) y != Codel.chromatic h l) = true)
    (hdown : (g.get x (y + 1) != Codel.chromatic h l) = true)
    (hleft : 0 < x → (g.get (x - 1) y != Codel.chromatic h l) = true)
    (hup : 0 < y → (g.get x (y - 1) != Codel.chromatic h l) = true) :
    localInfoAt? g (x, y) = some (singletonInfo (x, y)) := by
  apply localInfoAt?_isolated g h l (x, y) hx hy hcur
  intro q hq
  rcases mem_neighbours_any g x y q hq with rfl | rfl | ⟨h0, rfl⟩ | ⟨h0, rfl⟩
  · exact hright
  · exact hdown
  · exact hleft h0
  · exact hup h0

/-- The block that prints the answer is its own colour block. -/
theorem loopGrid_out_isolated (prologue body : List BlockCmd)
    (hu : UnitCode (loopCode body)) :
    localInfoAt? (loopGrid prologue body) (pw prologue + bw body + 2, 0) =
      some (singletonInfo (pw prologue + bw body + 2, 0)) := by
  have hbw : bw body = (loopCode body).length + 1 :=
    coloredRuns_length_of_unit _ _ _ hu
  have hpivot := loopGrid_body_colour prologue body hu (loopCode body).length (by omega)
  rw [colourAt_full] at hpivot
  rw [show pw prologue + 2 + (loopCode body).length = pw prologue + bw body + 1
    from by omega] at hpivot
  apply localInfoAt?_top _ _ _ _ (by rw [loopGrid_width]; omega)
    (by rw [loopGrid_height]; omega) (loopGrid_get_out prologue body)
  · intro _
    rw [show pw prologue + bw body + 2 - 1 = pw prologue + bw body + 1 from by omega,
      hpivot]
    apply chromatic_bne
    exact fun he => advance_ne _ _ Op.outNum he.symm
  · rw [show pw prologue + bw body + 2 + 1 = pw prologue + bw body + 3 from rfl,
      loopGrid_get_outWhite]
    rfl
  · rw [loopGrid_get_midBlack]
    rfl

/-- The `pop` block the loop turns down through is its own colour block. -/
theorem loopGrid_loopBlock_isolated (prologue body : List BlockCmd)
    (hu : UnitCode (loopCode body)) (hlong : 2 ≤ (loopCode body).length) :
    localInfoAt? (loopGrid prologue body) (pw prologue + bw body + 1, 1) =
      some (singletonInfo (pw prologue + bw body + 1, 1)) := by
  have hbw : bw body = (loopCode body).length + 1 :=
    coloredRuns_length_of_unit _ _ _ hu
  have hpivot := loopGrid_body_colour prologue body hu (loopCode body).length (by omega)
  rw [colourAt_full] at hpivot
  rw [show pw prologue + 2 + (loopCode body).length = pw prologue + bw body + 1
    from by omega] at hpivot
  apply localInfoAt?_any _ _ _ _ _ (by rw [loopGrid_width]; omega)
    (by rw [loopGrid_height]; omega) (loopGrid_get_loopBlock prologue body)
  · rw [show pw prologue + bw body + 1 + 1 = pw prologue + bw body + 2 from rfl,
      loopGrid_get_midBlack]
    rfl
  · rw [show (1 : Nat) + 1 = 2 from rfl]
    rw [show pw prologue + bw body + 1 = pw prologue + 1 + bw body from by omega,
      loopGrid_get_bottomWhite prologue body (bw body) (by omega)]
    rfl
  · intro _
    have hd := loopGrid_get_body_down prologue body ((loopCode body).length - 1)
      (by show (loopCode body).length - 1 + 1 < bw body; omega)
    simp only at hd
    rw [show pw prologue + bw body + 1 - 1 =
      (coloredRuns Hue.red Lightness.normal prologue).length + 2 +
        ((loopCode body).length - 1) from by
      show pw prologue + bw body + 1 - 1 = pw prologue + 2 + ((loopCode body).length - 1)
      omega]
    rw [hd]
    rfl
  · intro _
    rw [show (1 : Nat) - 1 = 0 from rfl, hpivot]
    apply chromatic_bne
    exact fun he => advance_ne _ _ Op.pop he.symm

/-- The halting branch: the pivot leaves the direction pointing right, so
the run prints the answer and slides into the terminal block. -/
theorem exec_halt_branch (prologue body : List BlockCmd)
    (hu : UnitCode (loopCode body)) (bl : Blocks) (fuel : Nat) (s : MState)
    (hpos : s.pos = (pw prologue + bw body + 1, 0)) (hdp : s.dp = .right) :
    exec (loopGrid prologue body) bl (fuel + 3) s =
      ({ execOp .outNum 1 { s with pos := (pw prologue + bw body + 2, 0) } with
          pos := (pw prologue + bw body + 4, 0), dp := .right }, Exit.halted) := by
  have hbw : bw body = (loopCode body).length + 1 :=
    coloredRuns_length_of_unit _ _ _ hu
  have hpivot := loopGrid_body_colour prologue body hu (loopCode body).length (by omega)
  rw [colourAt_full] at hpivot
  rw [show pw prologue + 2 + (loopCode body).length = pw prologue + bw body + 1
    from by omega] at hpivot
  have hsf : slideFuel (loopGrid prologue body) =
      (4 * (pw prologue + bw body + 5) * 3 + 7) + 1 := by
    rw [slideFuel, loopGrid_width, loopGrid_height]
  have hiso : localInfoAt? (loopGrid prologue body) (pw prologue + bw body + 1, 0) =
      some (singletonInfo (pw prologue + bw body + 1, 0)) := by
    have h := loopGrid_body_isolated prologue body hu (loopCode body).length (by omega)
    rwa [show pw prologue + 2 + (loopCode body).length = pw prologue + bw body + 1
      from by omega] at h
  -- print the answer
  rw [show fuel + 3 = (fuel + 2) + 1 from rfl]
  rw [exec_singleton _ bl (fuel + 2) s _ _ (pw prologue + bw body + 2, 0) _ _ .outNum
    (by rw [hpos]; exact hiso)
    (by rw [hpos]; exact hpivot)
    (by rw [hpos, hdp]; simp only [step?]; rw [if_pos (by rw [loopGrid_width]; omega)])
    (loopGrid_get_out prologue body) (opFor_advance _ _ _)]
  -- slide into the terminal
  rw [show fuel + 2 = (fuel + 1) + 1 from rfl]
  rw [exec_white _ bl (fuel + 1) _ _ _ (pw prologue + bw body + 3, 0)
    (pw prologue + bw body + 4, 0) .right _
    (by
      simp only [execOp_set_pos]
      exact loopGrid_out_isolated prologue body hu)
    (by simp only [execOp_set_pos]; exact loopGrid_get_out prologue body)
    (by
      simp only [execOp_set_pos]
      rw [execOp_dp_of_ne_pointer _ _ _ (by simp), hdp]
      simp only [step?]
      rw [if_pos (by rw [loopGrid_width]; omega)])
    (loopGrid_get_outWhite prologue body)
    (by
      simp only [execOp_set_pos]
      rw [execOp_dp_of_ne_pointer _ _ _ (by simp), hdp, hsf]
      exact slide_land_right _ _ _ _ _ _ Hue.yellow Lightness.dark (by simp)
        (by simp only [step?]; rw [if_pos (by rw [loopGrid_width]; omega)])
        (loopGrid_get_term00 prologue body))]
  -- and halt
  rw [loopGrid_exec_halt prologue body bl fuel _ (by simp)]
  simp [execOp_set_pos]

/-- The looping branch: the pivot turns the direction pointer down, so the
run pops the answer and follows the return corridor back to the first codel
of the loop body. -/
theorem exec_loop_branch (prologue body : List BlockCmd)
    (hu : UnitCode (loopCode body)) (hlong : 2 ≤ (loopCode body).length)
    (bl : Blocks) (fuel : Nat) (s : MState)
    (hpos : s.pos = (pw prologue + bw body + 1, 0)) (hdp : s.dp = .down) :
    exec (loopGrid prologue body) bl (fuel + 2) s =
      exec (loopGrid prologue body) bl fuel
        { execOp .pop 1 { s with pos := (pw prologue + bw body + 1, 1) } with
          pos := (pw prologue + 2, 0), dp := .right, cc := s.cc.toggle } := by
  have hbw : bw body = (loopCode body).length + 1 :=
    coloredRuns_length_of_unit _ _ _ hu
  have hpivot := loopGrid_body_colour prologue body hu (loopCode body).length (by omega)
  rw [colourAt_full] at hpivot
  rw [show pw prologue + 2 + (loopCode body).length = pw prologue + bw body + 1
    from by omega] at hpivot
  have hiso : localInfoAt? (loopGrid prologue body) (pw prologue + bw body + 1, 0) =
      some (singletonInfo (pw prologue + bw body + 1, 0)) := by
    have h := loopGrid_body_isolated prologue body hu (loopCode body).length (by omega)
    rwa [show pw prologue + 2 + (loopCode body).length = pw prologue + bw body + 1
      from by omega] at h
  have hsf : slideFuel (loopGrid prologue body) =
      (12 * pw prologue + 11 * bw body + 62) + (bw body + 6) := by
    rw [slideFuel, loopGrid_width, loopGrid_height]
    omega
  have hfirst : (loopGrid prologue body).get (pw prologue + 2) 0 =
      .chromatic Hue.red Lightness.normal := by
    have h := loopGrid_body_colour prologue body hu 0 (by omega)
    simpa using h
  -- pop the answer
  rw [show fuel + 2 = (fuel + 1) + 1 from rfl]
  rw [exec_singleton _ bl (fuel + 1) s _ _ (pw prologue + bw body + 1, 1) _ _ .pop
    (by rw [hpos]; exact hiso)
    (by rw [hpos]; exact hpivot)
    (by rw [hpos, hdp]; simp only [step?]; rw [if_pos (by rw [loopGrid_height]; omega)])
    (loopGrid_get_loopBlock prologue body) (opFor_advance _ _ _)]
  -- and follow the return corridor
  rw [exec_white _ bl fuel _ _ _ (pw prologue + bw body + 1, 2)
    (pw prologue + 2, 0) .right _
    (by
      simp only [execOp_set_pos]
      exact loopGrid_loopBlock_isolated prologue body hu hlong)
    (by simp only [execOp_set_pos]; exact loopGrid_get_loopBlock prologue body)
    (by
      simp only [execOp_set_pos]
      rw [execOp_dp_of_ne_pointer _ _ _ (by simp), hdp]
      simp only [step?]
      rw [if_pos (by rw [loopGrid_height]; omega)])
    (by
      rw [show pw prologue + bw body + 1 = pw prologue + 1 + bw body from by omega]
      exact loopGrid_get_bottomWhite prologue body (bw body) (by omega))
    (by
      simp only [execOp_set_pos]
      rw [execOp_dp_of_ne_pointer _ _ _ (by simp), hdp, hsf,
        execOp_cc_of_ne_switch _ _ _ (by simp)]
      rw [show pw prologue + bw body + 1 = pw prologue + 1 + bw body from by omega]
      exact slide_return (loopGrid prologue body) (pw prologue) (bw body)
        (12 * pw prologue + 11 * bw body + 62) s.cc Hue.red Lightness.normal
        (bw_pos body)
        (by
          intro p
          simp only [step?]
          rw [if_neg (by rw [loopGrid_height]; omega)])
        (by
          intro j hj
          rw [show pw prologue + 1 + bw body - j - 1 =
            pw prologue + 1 + (bw body - j - 1) from by omega]
          exact loopGrid_get_bottomWhite prologue body (bw body - j - 1) (by omega))
        (loopGrid_get_bottomBlack prologue body)
        (loopGrid_get_sepMiddle prologue body)
        (loopGrid_get_sep prologue body)
        hfirst
        (by rw [loopGrid_width]; omega))]

/-- Full compiler with singleton command blocks. -/
def compile (P : Program) (inputs : List Nat) : Grid :=
  let base := registerDepth P inputs
  let N := base + 3
  loopGrid (unitize (initialCode N inputs)) (unitize (dispatcherCode P base))

/-! ## The loop, and the run

One iteration of the compiled loop performs one `Cslib.URM.Step`, and the
iteration whose committed program counter falls off the end of the source
prints the answer and halts.  `exec_run` composes those over the machine's
own steps. -/

/-- An exact-cost `exec` fact is a `Reaches`. -/
theorem reaches_of_exec {g : Grid} {bl : Blocks} {k : Nat} {s t : MState}
    (h : ∀ fuel, exec g bl (fuel + k) s = exec g bl fuel t) :
    Reaches (exec g bl) s t :=
  ⟨k, fun f => by rw [Nat.add_comm]; exact h f⟩

/-- The compiled image of a URM program, named once. -/
def image (P : Program) (inputs : List Nat) : Grid := compile P inputs

theorem image_eq (P : Program) (inputs : List Nat) :
    image P inputs =
      loopGrid (unitize (initialCode (registerDepth P inputs + 3) inputs))
        (unitize (dispatcherCode P (registerDepth P inputs))) := rfl

/-- One whole iteration of the compiled loop, while the run continues. -/
theorem reaches_iteration (P : Program) (inputs : List Nat)
    {u u' : Cslib.URM.State} (hstep : Cslib.URM.Step P u u')
    (hbelow : ∀ x ∈ P, InstrBelow (registerDepth P inputs) x)
    (hbase : 0 < registerDepth P inputs)
    (hrun : (u'.pc : Int) < (P.length : Int))
    (bl : Blocks) (s : MState) (next flag : Int)
    (hpos : s.pos =
      (pw (unitize (initialCode (registerDepth P inputs + 3) inputs)) + 2, 0))
    (hdp : s.dp = .right)
    (hstack : s.stack =
      stackOf (registerDepth P inputs) u.regs (u.pc : Int) next flag) :
    ∃ (f : Int) (s' : MState),
      Reaches (exec (image P inputs) bl) s s' ∧
      s'.pos =
        (pw (unitize (initialCode (registerDepth P inputs + 3) inputs)) + 2, 0) ∧
      s'.dp = .right ∧
      s'.stack =
        stackOf (registerDepth P inputs) u'.regs (u'.pc : Int) (u'.pc : Int) f ∧
      s'.output = s.output ∧ s'.input = s.input := by
  set base := registerDepth P inputs with hbaseDef
  set prologue := unitize (initialCode (base + 3) inputs) with hpro
  set body := unitize (dispatcherCode P base) with hbody
  obtain ⟨stable, hsplit, hstable⟩ := loopCode_dispatcher_split P base
  have hu : UnitCode (loopCode body) := unitCode_loopCode _
  have hlong : 2 ≤ (loopCode body).length := by
    rw [hsplit]
    simp
  -- the corridor, the switch and the pointer
  have h1 : Reaches (exec (image P inputs) bl) s
      { runCode (loopCode body) s with
        pos := (pw prologue + bw body + 1, 0) } := by
    apply reaches_of_exec
    intro fuel
    exact exec_toPivot prologue body hu stable hsplit hstable bl fuel s hpos hdp
  -- what the body computed
  have hnoop : runCode (loopCode body) s = runCode (dispatcherCode P base) s := by
    rw [loopCode, runCode_append, runCode_append, runCode_unitize,
      runCode_pushNat]
    simp [runCode, op, execOp]
  obtain ⟨f, hdisp⟩ := runCode_dispatcherCode base P hstep hbelow hbase s next flag
    hstack
  -- the looping branch
  have hpivdp : ({ runCode (loopCode body) s with
      pos := (pw prologue + bw body + 1, 0) } : MState).dp = .down := by
    simp only [hnoop, hdisp, if_pos hrun, hdp, clockwise_right]
  have h2 := reaches_of_exec (fun fuel =>
    exec_loop_branch prologue body hu hlong bl fuel
      ({ runCode (loopCode body) s with
        pos := (pw prologue + bw body + 1, 0) } : MState) rfl hpivdp)
  refine ⟨f, _, Reaches.trans h1 h2, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp [hnoop, hdisp, hdp, execOp]

set_option maxHeartbeats 1000000 in
/-- A dispatcher pass from a halted program counter changes nothing but the
counters it always writes. -/
theorem runCode_dispatcherCode_halted (base : Nat) (P : Program)
    (u : Cslib.URM.State) (hhalt : P.length ≤ u.pc)
    (hbelow : ∀ x ∈ P, InstrBelow base x) (hbase : 0 < base) (s : MState)
    (next flag : Int)
    (hstack : s.stack = stackOf base u.regs (u.pc : Int) next flag) :
    ∃ f, runCode (dispatcherCode P base) s =
      { s with
        cc := s.cc.toggle,
        stack := ((u.regs 0 : Nat) : Int) ::
          stackOf base u.regs ((u.pc : Int) + 1) ((u.pc : Int) + 1) f } := by
  obtain ⟨f, hmiss⟩ := dispatchUpdate_miss base P 0 u.regs ((u.pc : Int))
    ((u.pc : Int) + 1) flag hbelow (by intro j hj; omega)
  refine ⟨f, ?_⟩
  simp only [dispatcherCode, runCode_append]
  rw [runCode_beginDispatch_stackOf base u.regs (u.pc : Int) next flag s hstack]
  rw [runCode_dispatchFrom_stackOf base P u.regs (u.pc : Int) ((u.pc : Int) + 1)
    flag _ hbelow rfl]
  rw [hmiss]
  rw [runCode_endDispatch_stackOf base u.regs (u.pc : Int) ((u.pc : Int) + 1) f _ rfl]
  rw [runCode_prepareBranch_stackOf base u.regs ((u.pc : Int) + 1) ((u.pc : Int) + 1)
    f P.length hbase _ rfl]
  rw [if_neg (by omega)]
  rw [runCode_steerBranch_zero ((u.regs 0 : Nat) : Int)
    (stackOf base u.regs ((u.pc : Int) + 1) ((u.pc : Int) + 1) f) _ rfl]

set_option maxHeartbeats 1000000 in
/-- Reaching the pivot with the direction pointer still right ends the run,
with the answer printed. -/
theorem exec_halt_at_pivot (P : Program) (inputs : List Nat) (bl : Blocks)
    (s : MState) (answer : Int) (rest : List Int)
    (hpos : s.pos =
      (pw (unitize (initialCode (registerDepth P inputs + 3) inputs)) + 2, 0))
    (hdp : s.dp = .right)
    (hpivot : (runCode (loopCode (unitize (dispatcherCode P (registerDepth P inputs))))
      s).stack = answer :: rest)
    (hpivotdp : (runCode (loopCode (unitize
      (dispatcherCode P (registerDepth P inputs)))) s).dp = .right) :
    ∃ (m : Nat) (s' : MState),
      exec (image P inputs) bl m s = (s', Exit.halted) ∧
      s'.output = (runCode (loopCode (unitize
        (dispatcherCode P (registerDepth P inputs)))) s).output ++
        (toString answer).toUTF8 := by
  set base := registerDepth P inputs with hbaseDef
  set prologue := unitize (initialCode (base + 3) inputs) with hpro
  set body := unitize (dispatcherCode P base) with hbody
  obtain ⟨stable, hsplit, hstable⟩ := loopCode_dispatcher_split P base
  have hu : UnitCode (loopCode body) := unitCode_loopCode _
  have h1 : Reaches (exec (image P inputs) bl) s
      { runCode (loopCode body) s with
        pos := (pw prologue + bw body + 1, 0) } := by
    apply reaches_of_exec
    intro fuel
    exact exec_toPivot prologue body hu stable hsplit hstable bl fuel s hpos hdp
  obtain ⟨c, hc⟩ := h1
  have hfin := exec_halt_branch prologue body hu bl 0
    ({ runCode (loopCode body) s with
      pos := (pw prologue + bw body + 1, 0) } : MState) rfl hpivotdp
  refine ⟨c + 3, _, by rw [hc 3]; exact hfin, ?_⟩
  simp [execOp, hpivot]

/-- The last iteration: the step that lands on a halted program counter
prints the answer and stops. -/
theorem exec_halt_of_step (P : Program) (inputs : List Nat) (bl : Blocks)
    {u u' : Cslib.URM.State} (hstep : Cslib.URM.Step P u u')
    (hbelow : ∀ x ∈ P, InstrBelow (registerDepth P inputs) x)
    (hbase : 0 < registerDepth P inputs)
    (hhalt : ¬((u'.pc : Int) < (P.length : Int)))
    (s : MState) (next flag : Int)
    (hpos : s.pos =
      (pw (unitize (initialCode (registerDepth P inputs + 3) inputs)) + 2, 0))
    (hdp : s.dp = .right)
    (hstack : s.stack =
      stackOf (registerDepth P inputs) u.regs (u.pc : Int) next flag) :
    ∃ (m : Nat) (s' : MState),
      exec (image P inputs) bl m s = (s', Exit.halted) ∧
      s'.output = s.output ++ (toString ((u'.regs 0 : Nat) : Int)).toUTF8 := by
  set base := registerDepth P inputs with hbaseDef
  set body := unitize (dispatcherCode P base) with hbody
  have hnoop : runCode (loopCode body) s = runCode (dispatcherCode P base) s := by
    rw [loopCode, runCode_append, runCode_append, runCode_unitize,
      runCode_pushNat]
    simp [runCode, op, execOp]
  obtain ⟨f, hdisp⟩ := runCode_dispatcherCode base P hstep hbelow hbase s next flag
    hstack
  obtain ⟨m, s', hexec, hout⟩ := exec_halt_at_pivot P inputs bl s
    ((u'.regs 0 : Nat) : Int)
    (stackOf base u'.regs (u'.pc : Int) (u'.pc : Int) f) hpos hdp
    (by rw [hnoop, hdisp])
    (by rw [hnoop, hdisp]; simp only [if_neg hhalt]; exact hdp)
  exact ⟨m, s', hexec, by rw [hout, hnoop, hdisp]⟩

/-- A program whose counter is already past its end halts on the first
iteration, with register zero unchanged. -/
theorem exec_halt_of_halted (P : Program) (inputs : List Nat) (bl : Blocks)
    (u : Cslib.URM.State) (hhalt : P.length ≤ u.pc)
    (hbelow : ∀ x ∈ P, InstrBelow (registerDepth P inputs) x)
    (hbase : 0 < registerDepth P inputs)
    (s : MState) (next flag : Int)
    (hpos : s.pos =
      (pw (unitize (initialCode (registerDepth P inputs + 3) inputs)) + 2, 0))
    (hdp : s.dp = .right)
    (hstack : s.stack =
      stackOf (registerDepth P inputs) u.regs (u.pc : Int) next flag) :
    ∃ (m : Nat) (s' : MState),
      exec (image P inputs) bl m s = (s', Exit.halted) ∧
      s'.output = s.output ++ (toString ((u.regs 0 : Nat) : Int)).toUTF8 := by
  set base := registerDepth P inputs with hbaseDef
  set body := unitize (dispatcherCode P base) with hbody
  have hnoop : runCode (loopCode body) s = runCode (dispatcherCode P base) s := by
    rw [loopCode, runCode_append, runCode_append, runCode_unitize,
      runCode_pushNat]
    simp [runCode, op, execOp]
  obtain ⟨f, hdisp⟩ := runCode_dispatcherCode_halted base P u hhalt hbelow hbase s
    next flag hstack
  obtain ⟨m, s', hexec, hout⟩ := exec_halt_at_pivot P inputs bl s
    ((u.regs 0 : Nat) : Int)
    (stackOf base u.regs ((u.pc : Int) + 1) ((u.pc : Int) + 1) f) hpos hdp
    (by rw [hnoop, hdisp])
    (by rw [hnoop, hdisp]; exact hdp)
  exact ⟨m, s', hexec, by rw [hout, hnoop, hdisp]⟩

/-- The whole run: every iteration of the compiled loop, composed over the
URM's own steps, ending in the halt that prints register zero. -/
theorem exec_run (P : Program) (inputs : List Nat) (bl : Blocks)
    (hbelow : ∀ x ∈ P, InstrBelow (registerDepth P inputs) x)
    (hbase : 0 < registerDepth P inputs) :
    ∀ {u u' : Cslib.URM.State}, Cslib.URM.Steps P u u' → u'.isHalted P →
    ∀ (s : MState) (next flag : Int),
      s.pos =
        (pw (unitize (initialCode (registerDepth P inputs + 3) inputs)) + 2, 0) →
      s.dp = .right →
      s.stack = stackOf (registerDepth P inputs) u.regs (u.pc : Int) next flag →
      ∃ (m : Nat) (s' : MState),
        exec (image P inputs) bl m s = (s', Exit.halted) ∧
        s'.output = s.output ++ (toString ((u'.regs 0 : Nat) : Int)).toUTF8 := by
  intro u u' hsteps
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl =>
      intro hhalt s next flag hpos hdp hstack
      exact exec_halt_of_halted P inputs bl u' hhalt hbelow hbase s next flag
        hpos hdp hstack
  | @head v w hstep hrest ih =>
      intro hhalt s next flag hpos hdp hstack
      by_cases hw : (w.pc : Int) < (P.length : Int)
      · obtain ⟨f, s₁, hreach, hpos₁, hdp₁, hstack₁, hout₁, hin₁⟩ :=
          reaches_iteration P inputs hstep hbelow hbase hw bl s next flag hpos hdp
            hstack
        obtain ⟨m, s₂, hexec, hout₂⟩ := ih hhalt s₁ _ _ hpos₁ hdp₁ hstack₁
        obtain ⟨c, hc⟩ := hreach
        exact ⟨c + m, s₂, by rw [hc m, hexec], by rw [hout₂, hout₁]⟩
      · have hvh : w.isHalted P := by
          simp only [Cslib.URM.State.isHalted]
          omega
        have hwu : w = u' := by
          rcases Relation.ReflTransGen.cases_head hrest with h | ⟨z, hz, _⟩
          · exact h
          · exact absurd hz (Cslib.URM.Step.no_step_of_halted hvh)
        subst hwu
        exact exec_halt_of_step P inputs bl hstep hbelow hbase hw s next flag
          hpos hdp hstack

/-! ## The run, end to end

The start slide, the prologue, the loop, and the answer. -/

/-- Every codel of the prologue corridor is its own colour block. -/
theorem loopGrid_prologue_isolated (prologue body : List BlockCmd)
    (hu : UnitCode prologue) (j : Nat) (hj : j ≤ prologue.length) :
    localInfoAt? (loopGrid prologue body) (1 + j, 0) =
      some (singletonInfo (1 + j, 0)) := by
  have hpw : pw prologue = prologue.length + 1 :=
    coloredRuns_length_of_unit _ _ _ hu
  have hcolour : ∀ i, i ≤ prologue.length →
      (loopGrid prologue body).get (1 + i) 0 =
        .chromatic (colourAt Hue.red Lightness.normal prologue i).1
          (colourAt Hue.red Lightness.normal prologue i).2 := by
    intro i hi
    rw [show (1 : Nat) + i = i + 1 from by omega]
    have hib : i < (coloredRuns Hue.red Lightness.normal prologue).length := by
      rw [coloredRuns_length_of_unit _ _ _ hu]; omega
    rw [loopGrid_get_prologue prologue body i hib]
    have hg := coloredRuns_getElem?_unit Hue.red Lightness.normal prologue hu i hi
    rw [List.getElem?_eq_getElem hib] at hg
    exact Option.some.inj hg
  have hcur := hcolour j hj
  apply localInfoAt?_top _ _ _ _ (by rw [loopGrid_width]; have := bw_pos body; omega)
    (by rw [loopGrid_height]; omega) hcur
  · intro _
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [show (1 : Nat) + 0 - 1 = 0 from rfl, loopGrid_get_start]
      rfl
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      rw [show (1 : Nat) + (i + 1) - 1 = 1 + i from by omega, hcolour i (by omega)]
      apply chromatic_bne
      exact fun he => colourAt_succ_ne Hue.red Lightness.normal prologue i
        (by omega) he.symm
  · rcases Nat.lt_or_ge j prologue.length with hlt | hge
    · rw [show (1 : Nat) + j + 1 = 1 + (j + 1) from by omega,
        hcolour (j + 1) (by omega)]
      apply chromatic_bne
      exact colourAt_succ_ne Hue.red Lightness.normal prologue j (by omega)
    · have hjeq : j = prologue.length := by omega
      subst hjeq
      rw [show (1 : Nat) + prologue.length + 1 = pw prologue + 1 from by omega,
        loopGrid_get_sep]
      rfl
  · rw [show (1 : Nat) + j = j + 1 from by omega]
    rw [loopGrid_get_prologue_down prologue body j
      (by rw [coloredRuns_length_of_unit _ _ _ hu]; omega)]
    rfl

/-- The prologue: from the first codel of the image, load the register file
and slide across the separator into the loop body. -/
theorem exec_entry (P : Program) (inputs : List Nat) (bl : Blocks) (s : MState)
    (hpos : s.pos = (1, 0)) (hdp : s.dp = .right) :
    Reaches (exec (image P inputs) bl) s
      { runCode (unitize (initialCode (registerDepth P inputs + 3) inputs)) s with
        pos := (pw (unitize
          (initialCode (registerDepth P inputs + 3) inputs)) + 2, 0),
        dp := .right } := by
  set base := registerDepth P inputs with hbaseDef
  set prologue := unitize (initialCode (base + 3) inputs) with hpro
  set body := unitize (dispatcherCode P base) with hbody
  have hu : UnitCode prologue := unitCode_unitize _
  have hst : StableCode prologue :=
    stableCode_unitize (stableCode_initialCode _ _)
  have hpw : pw prologue = prologue.length + 1 :=
    coloredRuns_length_of_unit _ _ _ hu
  have hcorr := loopGrid_prologue_corridor prologue body hu
  have hsf : slideFuel (loopGrid prologue body) =
      (4 * (pw prologue + bw body + 5) * 3 + 7) + 1 := by
    rw [slideFuel, loopGrid_width, loopGrid_height]
  have hlast : (loopGrid prologue body).get (pw prologue) 0 =
      .chromatic (colourAt Hue.red Lightness.normal prologue prologue.length).1
        (colourAt Hue.red Lightness.normal prologue prologue.length).2 := by
    have hib : prologue.length <
        (coloredRuns Hue.red Lightness.normal prologue).length := by
      rw [coloredRuns_length_of_unit _ _ _ hu]; omega
    have h := loopGrid_get_prologue prologue body prologue.length hib
    rw [show pw prologue = prologue.length + 1 from hpw, h]
    have hg := coloredRuns_getElem?_unit Hue.red Lightness.normal prologue hu
      prologue.length (by omega)
    rw [List.getElem?_eq_getElem hib] at hg
    exact Option.some.inj hg
  -- the corridor
  have h1 : Reaches (exec (image P inputs) bl) s
      { runCode prologue s with pos := (pw prologue, 0) } := by
    apply reaches_of_exec
    intro fuel
    have h := exec_unitCorridor (loopGrid prologue body) bl prologue 1 Hue.red
      Lightness.normal hcorr hst fuel s hpos hdp
    rw [show (1 : Nat) + prologue.length = pw prologue from by omega] at h
    exact h
  -- the separator
  have h2 : Reaches (exec (image P inputs) bl)
      { runCode prologue s with pos := (pw prologue, 0) }
      { runCode prologue s with pos := (pw prologue + 2, 0), dp := .right } := by
    apply reaches_of_exec
    intro fuel
    have hdp' : ({ runCode prologue s with pos := (pw prologue, 0) } : MState).dp
        = .right := by
      simp only []
      rw [runCode_dp_of_stable prologue hst, hdp]
    have h := exec_white (loopGrid prologue body) bl fuel
      ({ runCode prologue s with pos := (pw prologue, 0) } : MState)
      _ _ (pw prologue + 1, 0) (pw prologue + 2, 0) .right _
      (by
        simp only []
        rw [show pw prologue = 1 + prologue.length from by omega]
        exact loopGrid_prologue_isolated prologue body hu prologue.length (by omega))
      (by simp only []; exact hlast)
      (by
        simp only []
        rw [hdp']
        simp only [step?]
        rw [if_pos (by rw [loopGrid_width]; have := bw_pos body; omega)])
      (loopGrid_get_sep prologue body)
      (by
        rw [hdp', hsf]
        exact slide_land_right _ _ _ _ _ _ Hue.red Lightness.normal (by simp)
          (by
            simp only [step?]
            rw [if_pos (by rw [loopGrid_width]; have := bw_pos body; omega)])
          (by
            have h := loopGrid_body_colour prologue body (unitCode_loopCode _) 0
              (by omega)
            simpa using h))
    exact h
  exact Reaches.trans h1 h2

/-- The prologue leaves the register file on the stack, with the three
control slots zeroed. -/
theorem initial_stack (P : Program) (inputs : List Nat) (s : MState)
    (hstack : s.stack = []) :
    (runCode (unitize (initialCode (registerDepth P inputs + 3) inputs)) s).stack =
      stackOf (registerDepth P inputs) (Cslib.URM.Regs.ofInputs inputs) 0 0 0 := by
  set base := registerDepth P inputs with hbaseDef
  have hlen : inputs.length ≤ base := by
    rw [hbaseDef, registerDepth]
    omega
  have hz : ∀ i, base ≤ i → inputs.getD i 0 = 0 := by
    intro i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl
  rw [runCode_unitize, runCode_initialCode]
  simp only [hstack, List.append_nil]
  simp only [initialRegisters]
  rw [show base + 3 = base + 1 + 1 + 1 from rfl, List.range_succ, List.range_succ,
    List.range_succ]
  simp only [List.map_append, List.map_cons, List.map_nil,
    stackOf, List.append_assoc, List.cons_append, List.nil_append]
  rw [hz base (by omega), hz (base + 1) (by omega), hz (base + 1 + 1) (by omega)]
  simp [Cslib.URM.Regs.ofInputs, List.map_map, Function.comp]

theorem runCode_initialCode_output (R : Nat) (inputs : List Nat) (s : MState) :
    (runCode (unitize (initialCode R inputs)) s).output = s.output := by
  rw [runCode_unitize, runCode_initialCode]

theorem int_toString_ofNat (n : Nat) : toString ((n : Nat) : Int) = toString n := rfl

theorem fromUTF8?_toUTF8 (s : String) : String.fromUTF8? s.toUTF8 = some s := by
  simp only [String.toUTF8_eq_toByteArray, String.fromUTF8?, dif_pos s.isValidUTF8,
    Option.some.injEq, ← String.toByteArray_inj]
  simp [String.fromUTF8]

theorem decodeOutput_toString (n : Nat) :
    decodeOutput ((toString ((n : Nat) : Int)).toUTF8) = some n := by
  rw [int_toString_ofNat]
  simp only [decodeOutput, fromUTF8?_toUTF8]
  rw [show toString n = Nat.repr n by exact Nat.toString_eq_repr]
  simp [Nat.toNat?_repr]

theorem instrBelow_of_maxRegister (N : Nat) (instr : Cslib.URM.Instr)
    (h : instr.maxRegister < N) : InstrBelow N instr := by
  cases instr with
  | Z r | S r => exact h
  | T m r | J m r q =>
      simp only [Cslib.URM.Instr.maxRegister] at h
      exact ⟨by omega, by omega⟩

theorem maxRegister_le (P : Program) : ∀ instr ∈ P,
    instr.maxRegister ≤ P.maxRegister := by
  have le_foldl : ∀ (xs : List Cslib.URM.Instr) (acc : Nat),
      acc ≤ xs.foldl (fun a j => max a j.maxRegister) acc := by
    intro xs
    induction xs with
    | nil => intro acc; exact Nat.le_refl _
    | cons j js ih =>
        intro acc
        exact Nat.le_trans (Nat.le_max_left acc j.maxRegister) (ih _)
  have mem_le : ∀ (xs : List Cslib.URM.Instr) (acc : Nat) (j : Cslib.URM.Instr),
      j ∈ xs → j.maxRegister ≤ xs.foldl (fun a t => max a t.maxRegister) acc := by
    intro xs
    induction xs with
    | nil => intro acc j hj; simp at hj
    | cons k ks ih =>
        intro acc j hj
        rcases List.mem_cons.mp hj with rfl | hj
        · exact Nat.le_trans (Nat.le_max_right acc j.maxRegister) (le_foldl _ _)
        · exact ih _ j hj
  intro instr hi
  exact mem_le P 0 instr hi

theorem below_registerDepth (P : Program) (inputs : List Nat) :
    ∀ x ∈ P, InstrBelow (registerDepth P inputs) x := by
  intro x hx
  apply instrBelow_of_maxRegister
  have := maxRegister_le P x hx
  rw [registerDepth]
  omega

theorem registerDepth_pos (P : Program) (inputs : List Nat) :
    0 < registerDepth P inputs := by
  rw [registerDepth]
  omega

/-- End to end: a halting URM run is simulated by the generated image, and
the printed answer is register zero. -/
theorem simulation (P : Program) (inputs : List Nat) (result : Nat)
    (h : Cslib.URM.HaltsWithResult P inputs result) :
    ∃ fuel,
      (evalGrid (image P inputs) (Input.ofString "") fuel).exit = Exit.halted ∧
      decodeOutput (evalGrid (image P inputs) (Input.ofString "") fuel).output =
        some result := by
  obtain ⟨u, hsteps, hhalt, hresult⟩ := h
  set base := registerDepth P inputs with hbaseDef
  set prologue := unitize (initialCode (base + 3) inputs) with hpro
  set body := unitize (dispatcherCode P base) with hbody
  set bl := computeBlocks (image P inputs) with hbl
  set s₁ : MState :=
    { pos := (1, 0), dp := .right, cc := .left, input := Input.ofString "" }
    with hs₁
  have hw : (image P inputs).width = pw prologue + bw body + 5 :=
    loopGrid_width prologue body
  have hfirst : (image P inputs).get 1 0 = Codel.chromatic Hue.red Lightness.normal := by
    have hib : (0 : Nat) < (coloredRuns Hue.red Lightness.normal prologue).length := by
      rw [coloredRuns_length_of_unit _ _ _ (unitCode_unitize _)]
      omega
    have hg := coloredRuns_getElem?_unit Hue.red Lightness.normal prologue
      (unitCode_unitize _) 0 (by omega)
    rw [List.getElem?_eq_getElem hib] at hg
    have h := loopGrid_get_prologue prologue body 0 hib
    rw [Option.some.inj hg] at h
    rw [image_eq]
    simpa using h
  have hh : (image P inputs).height = 3 := loopGrid_height prologue body
  -- the prologue
  obtain ⟨c, hc⟩ := exec_entry P inputs bl s₁ rfl rfl
  -- the loop
  obtain ⟨m, s', hexec, hout⟩ := exec_run P inputs bl (below_registerDepth P inputs)
    (registerDepth_pos P inputs) hsteps hhalt
    ({ runCode prologue s₁ with pos := (pw prologue + 2, 0), dp := .right } :
      MState) 0 0 rfl rfl
    (by
      simp only []
      exact initial_stack P inputs s₁ rfl)
  have heval : evalGrid (image P inputs) (Input.ofString "") (c + m) =
      { output := s'.output, exit := Exit.halted } := by
    unfold evalGrid
    rw [show (image P inputs).get 0 0 = Codel.white from
      loopGrid_get_start prologue body]
    simp only []
    rw [show slide (image P inputs) (slideFuel (image P inputs)) [] (0, 0) .right .left
      = .landed (1, 0) .right .left from by
        rw [show slideFuel (image P inputs) =
          (4 * (pw prologue + bw body + 5) * 3 + 7) + 1 from by
            rw [slideFuel, hw, hh]]
        exact slide_land_right _ _ _ _ _ _ Hue.red Lightness.normal (by simp)
          (by
            simp only [step?]
            rw [if_pos (by rw [hw]; have := bw_pos body; omega)])
          hfirst]
    simp only []
    rw [hc m, hexec]
  refine ⟨c + m, by rw [heval], ?_⟩
  rw [heval]
  simp only []
  rw [hout]
  have hempty : (runCode prologue s₁).output = ByteArray.empty := by
    rw [runCode_initialCode_output]
  have hr : u.regs 0 = result := hresult
  simp only [hempty, ByteArray.empty_append, hr]
  exact decodeOutput_toString result

end Langlib.Computability.URMPiet

namespace Langlib.Computability

open Langlib.Common

/-- The tag type naming Piet for `ProgLang`. -/
inductive PietLang : Type

instance : ProgLang PietLang where
  Prog := Langlib.Piet.Grid
  parse := fun src => Langlib.Piet.parseGrid {} src.toUTF8
  run := Langlib.Piet.evalGrid

/-- **Piet is lawful**: a completed run is a fixed point of more fuel.
Proved in `Langlib/Languages/Piet/Stability.lean`. -/
instance : LawfulProgLang PietLang where
  halted_stable := Langlib.Piet.evalGrid_stable

set_option maxHeartbeats 1000000 in
/-- Piet is Turing complete, via the verified URM-to-image compiler. -/
def pietComplete : TuringComplete PietLang where
  compile := URMPiet.image
  encodeInput := fun _ => Langlib.Common.Input.ofString ""
  decodeOutput := URMPiet.decodeOutput
  simulates := fun P inputs result h => URMPiet.simulation P inputs result h

end Langlib.Computability
