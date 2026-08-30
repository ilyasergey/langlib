import Langlib.Common.Fuel
import Langlib.Common.Computability
import Langlib.Computability.URM
import Langlib.Languages.Subleq.Semantics
import Langlib.Languages.Subleq.Trace

/-!
# Subleq is Turing complete

This file compiles an arbitrary unlimited register machine into subleq and
proves the simulation, giving the term `subleqComplete : TuringComplete
SubleqLang` that is langlib's statement of the result.

## The representation

Subleq words are arbitrary-precision signed integers and its memory is
unbounded, so there is no encoding to design: **URM register `r` is the
single memory cell at address `regBase P + r`**, holding the register's value
directly. Nothing here is bounded, so no arithmetic lemma carries a
side-condition, and the compiler places no ceiling on the values a compiled
program can hold.

## The memory layout

Code and data share one address space, so the image is laid out as

```
0 .. 2      3 3 8          an unconditional jump over the data cells
3           0              the zero cell, restored by every use
4           -1             the constant that `S` subtracts
5, 6        0 0            two scratch cells
7           49             the byte the epilogue prints
8 ..        the block for URM instruction 0, then 1, …
epiAddr P   the epilogue, 21 words
regBase P   register 0, register 1, …, initialised from the input vector
```

Addresses at or past the image read as 0, so registers beyond the input
vector start at 0, which is exactly `Cslib.URM.Regs.ofInputs`. The input
vector is therefore compiled into the image and the compiled program never
reads its input stream.

## The instruction encodings

Every subleq instruction is `A B C`: `mem[B] -= mem[A]`, then jump to `C`
when the result is `<= 0`. Writing `C` as the address of the *next*
instruction makes the branch invisible, since both outcomes land in the same
place; that is how the straight-line pieces below avoid any reasoning about
signs.

* `Z r` is one instruction, `Rr Rr next`.
* `S r` is one instruction, `4 Rr next`: subtracting the cell holding `-1`
  adds one.
* `T x y` is four: zero the scratch cell, negate `R[x]` into it, zero `R[y]`,
  then subtract the scratch cell from `R[y]`. Negating first is what makes
  `T x x` a no-op, as the URM requires.
* `J x y q` is nine, because subtract-and-branch tests `<= 0` rather than
  equality, and registers hold naturals. It computes `X - Y` in scratch cell
  6 and branches on `X <= Y`; where that holds it negates the difference into
  scratch cell 5 and branches again on `Y <= X`. Both together are `X = Y`.
  Each failing test falls into a `3 3 fall` unconditional jump.

## Halting and the answer

The epilogue keeps `-R[0]` in scratch cell 5, adds one to it each time round
a loop, and prints the byte 49 while the result is still `<= 0`; so it prints
`R[0]` bytes. It then executes `3 3 -1`, and a negative program counter is
how our semantics halts (`docs/subleq/spec.md`).

`decodeOutput` is therefore the *length* of the output, not decimal parsing.
That is a deliberate trade: subleq's only output primitive is one byte, so
printing a decimal numeral means a division routine, and a proof of a
division routine on self-modifying code is out of proportion to the claim
being made. Unary output keeps the decoder a total function of the output
bytes that invents nothing. See `docs/computability-subleq.md`.

## The shape of the proof

`Langlib.Common.Reaches` carries the fuel exactly, as in
`Langlib/Computability/Whitespace.lean`, and the lemmas compose by
`Reaches.trans`.

The state relation is `Ok`: the code region still agrees with the compiled
image, cells 3, 4 and 7 hold their constants, every register cell holds its
register, and memory extends past the whole code region. Cells 5 and 6 are
scratch and are deliberately unconstrained, so each block re-zeroes what it
uses.
-/

namespace Langlib.Computability.URMSubleq

open Langlib.Common
open Langlib.Subleq
open Cslib.URM (Program Regs Step Steps HaltsWithResult)

/-! ## Reading the initial image

`Mem.ofProg` builds the initial memory with a `for` loop over the program
array. These lemmas turn that loop into a recursive function and read the
word at each address back out of it. -/

/-- The recursive form of the loop that `Mem.ofProg` runs. -/
def cellsUpTo (p : Prog) : Nat → Std.HashMap Int Int
  | 0 => ∅
  | n + 1 =>
    let m := cellsUpTo p n
    if (p[n]! != 0) = true then m.insert (n : Int) p[n]! else m

private theorem cellsGo_forIn (l : List Nat) (p : Prog) :
    ∀ m : Std.HashMap Int Int,
      (forIn (m := Id) l m fun (i : Nat) (cells : Std.HashMap Int Int) =>
        if (p[i]! != 0) = true then pure (ForInStep.yield (cells.insert (i : Int) p[i]!))
        else pure (ForInStep.yield cells)) =
      l.foldl (fun (cells : Std.HashMap Int Int) (i : Nat) =>
        if (p[i]! != 0) = true then cells.insert (i : Int) p[i]! else cells) m := by
  induction l with
  | nil => intro m; rfl
  | cons i rest ih =>
    intro m
    rw [List.forIn_cons, List.foldl_cons]
    by_cases h : (p[i]! != 0) = true
    · rw [if_pos h, if_pos h]; exact ih _
    · rw [if_neg h, if_neg h]; exact ih _

theorem cells_ofProg (p : Prog) : (Mem.ofProg p).cells = cellsUpTo p p.size := by
  have key : ∀ n : Nat, (List.range n).foldl
      (fun (cells : Std.HashMap Int Int) (i : Nat) =>
        if (p[i]! != 0) = true then cells.insert (i : Int) p[i]! else cells)
      ∅ = cellsUpTo p n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [List.range_succ, List.foldl_append, ih]; rfl
  have hr : List.range' [:p.size].start [:p.size].size [:p.size].step = List.range p.size := by
    simp [Std.Legacy.Range.size, List.range_eq_range']
  unfold Mem.ofProg
  simp only [Id.run]
  rw [Std.Legacy.Range.forIn_eq_forIn_range', hr]
  show (forIn (m := Id) _ _ _) = _
  rw [cellsGo_forIn, key]

theorem extent_ofProg (p : Prog) : (Mem.ofProg p).extent = (p.size : Int) := by
  unfold Mem.ofProg; rfl



theorem getD_cellsUpTo (p : Prog) (a : Int) :
    ∀ n : Nat, (cellsUpTo p n).getD a 0 = if 0 ≤ a ∧ a < (n : Int) then p[a.toNat]! else 0 := by
  intro n
  induction n with
  | zero => simp [cellsUpTo]
  | succ n ih =>
    show (if (p[n]! != 0) = true then (cellsUpTo p n).insert (n : Int) p[n]! else cellsUpTo p n).getD a 0 = _
    by_cases hz : (p[n]! != 0) = true
    · rw [if_pos hz, Std.HashMap.getD_insert]
      by_cases ha : (n : Int) = a
      · subst ha
        simp only [beq_self_eq_true, if_pos, Int.toNat_natCast]
        rw [if_pos (by omega)]
      · rw [if_neg (by simpa using ha), ih]
        by_cases h1 : 0 ≤ a ∧ a < (n : Int)
        · rw [if_pos h1, if_pos (by omega)]
        · rw [if_neg h1, if_neg (fun h => h1 ⟨h.1, by omega⟩)]
    · rw [if_neg hz, ih]
      have hz' : p[n]! = 0 := by simpa using hz
      by_cases ha : (n : Int) = a
      · subst ha
        rw [if_neg (by omega), if_pos (by omega), Int.toNat_natCast, hz']
      · by_cases h1 : 0 ≤ a ∧ a < (n : Int)
        · rw [if_pos h1, if_pos (by omega)]
        · rw [if_neg h1, if_neg (fun h => h1 ⟨h.1, by omega⟩)]

theorem get_ofProg (p : Prog) (a : Int) :
    (Mem.ofProg p).get a = if 0 ≤ a ∧ a < (p.size : Int) then p[a.toNat]! else 0 := by
  show (Mem.ofProg p).cells.getD a 0 = _
  rw [cells_ofProg, getD_cellsUpTo]



/-! ## The memory layout -/

/-- The number of subleq words emitted for one URM instruction. -/
def instrSize : Cslib.URM.Instr → Nat
  | .Z _ => 3
  | .S _ => 3
  | .T _ _ => 12
  | .J _ _ _ => 27

/-- The number of words emitted for a run of URM instructions. -/
def codeSize : List Cslib.URM.Instr → Nat
  | [] => 0
  | i :: rest => instrSize i + codeSize rest

/-- The address of the block compiled for URM instruction `k`. -/
def entryAddr (P : Program) (k : Nat) : Nat := 8 + codeSize (P.take k)

/-- The address of the epilogue. -/
def epiAddr (P : Program) : Nat := 8 + codeSize P

/-- The address of URM register 0; register `r` lives at `regBase P + r`. -/
def regBase (P : Program) : Nat := epiAddr P + 21

/-- The address of the cell holding URM register `r`. -/
def regAddr (P : Program) (r : Nat) : Int := ((regBase P + r : Nat) : Int)

/-- Where a URM jump to instruction `q` lands. -/
def target (P : Program) (q : Nat) : Int := ((entryAddr P (min q P.length) : Nat) : Int)

/-- Addresses 0-7: an unconditional jump to the first block, then the four
fixed data cells (zero, minus one, two scratch cells) and the byte the
epilogue prints. -/
def header : List Int := [3, 3, 8, 0, -1, 0, 0, 49]

/-- The subleq words for one URM instruction, placed at address `a`. -/
def instrWords (P : Program) (a : Nat) : Cslib.URM.Instr → List Int
  | .Z r => [regAddr P r, regAddr P r, ((a + 3 : Nat) : Int)]
  | .S r => [4, regAddr P r, ((a + 3 : Nat) : Int)]
  | .T m r =>
      [5, 5, ((a + 3 : Nat) : Int),
       regAddr P m, 5, ((a + 6 : Nat) : Int),
       regAddr P r, regAddr P r, ((a + 9 : Nat) : Int),
       5, regAddr P r, ((a + 12 : Nat) : Int)]
  | .J m r q =>
      [5, 5, ((a + 3 : Nat) : Int),
       regAddr P m, 5, ((a + 6 : Nat) : Int),
       6, 6, ((a + 9 : Nat) : Int),
       5, 6, ((a + 12 : Nat) : Int),
       regAddr P r, 6, ((a + 18 : Nat) : Int),
       3, 3, ((a + 27 : Nat) : Int),
       5, 5, ((a + 21 : Nat) : Int),
       6, 5, target P q,
       3, 3, ((a + 27 : Nat) : Int)]

/-- The blocks for a run of URM instructions starting at address `a`. -/
def blocksWords (P : Program) : Nat → List Cslib.URM.Instr → List Int
  | _, [] => []
  | a, i :: rest => instrWords P a i ++ blocksWords P (a + instrSize i) rest

/-- Print register 0 in unary and halt. -/
def epiWords (P : Program) : List Int :=
  [5, 5, ((epiAddr P + 3 : Nat) : Int),
   regAddr P 0, 5, ((epiAddr P + 6 : Nat) : Int),
   4, 5, ((epiAddr P + 12 : Nat) : Int),
   3, 3, ((epiAddr P + 18 : Nat) : Int),
   7, -1, 0,
   3, 3, ((epiAddr P + 6 : Nat) : Int),
   3, 3, -1]

/-- The compiled image, as a list of words. -/
def compileList (P : Program) (inputs : List Nat) : List Int :=
  header ++ blocksWords P 8 P ++ epiWords P ++ inputs.map Int.ofNat

/-- The compiler. Total and runnable: `#eval (compile P inputs).size` works. -/
def compile (P : Program) (inputs : List Nat) : Prog := (compileList P inputs).toArray

/-! ## Sizes -/

theorem instrWords_length (P : Program) (a : Nat) (i : Cslib.URM.Instr) :
    (instrWords P a i).length = instrSize i := by cases i <;> rfl

theorem blocksWords_length (P : Program) : ∀ (a : Nat) (Q : List Cslib.URM.Instr),
    (blocksWords P a Q).length = codeSize Q := by
  intro a Q
  induction Q generalizing a with
  | nil => rfl
  | cons i rest ih =>
    simp only [blocksWords, List.length_append, instrWords_length, ih, codeSize]

theorem codeSize_append (Q₁ Q₂ : List Cslib.URM.Instr) :
    codeSize (Q₁ ++ Q₂) = codeSize Q₁ + codeSize Q₂ := by
  induction Q₁ with
  | nil => simp [codeSize]
  | cons i rest ih => simp only [List.cons_append, codeSize, ih]; omega

theorem blocksWords_append (P : Program) (Q₁ : List Cslib.URM.Instr) :
    ∀ (a : Nat) (Q₂ : List Cslib.URM.Instr),
      blocksWords P a (Q₁ ++ Q₂) = blocksWords P a Q₁ ++ blocksWords P (a + codeSize Q₁) Q₂ := by
  intro a Q₂
  induction Q₁ generalizing a with
  | nil => simp [blocksWords, codeSize]
  | cons i rest ih =>
    simp only [List.cons_append, blocksWords, ih, List.append_assoc, codeSize,
      show a + instrSize i + codeSize rest = a + (instrSize i + codeSize rest) from by omega]

theorem entryAddr_length (P : Program) : entryAddr P P.length = epiAddr P := by
  simp [entryAddr, epiAddr]

theorem entryAddr_succ (P : Program) (k : Nat) (hk : k < P.length) :
    entryAddr P k + instrSize P[k] = entryAddr P (k + 1) := by
  have hsplit : P.take (k + 1) = P.take k ++ [P[k]] := List.take_succ_eq_append_getElem hk
  simp only [entryAddr, hsplit, codeSize_append, codeSize]
  omega

theorem epiWords_length (P : Program) : (epiWords P).length = 21 := rfl

theorem compileList_length (P : Program) (inputs : List Nat) :
    (compileList P inputs).length = regBase P + inputs.length := by
  simp only [compileList, List.length_append, blocksWords_length, epiWords_length,
    List.length_map, regBase, epiAddr, header]
  simp



/-! ## Reading words out of the compiled image -/

/-- The word the compiled image holds at address `a`. -/
def wordAt (P : Program) (inputs : List Nat) (a : Int) : Int :=
  (compileList P inputs).getD a.toNat 0

theorem img_get (P : Program) (inputs : List Nat) (a : Int) (h : 0 ≤ a) :
    (Mem.ofProg (compile P inputs)).get a = wordAt P inputs a := by
  rw [get_ofProg]
  by_cases hlt : a < ((compile P inputs).size : Int)
  · rw [if_pos ⟨h, hlt⟩, compile]
    simp [wordAt, List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  · rw [if_neg (fun hc => hlt hc.2), wordAt, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none, Option.getD_none]
    simp only [compile, List.size_toArray] at hlt ⊢
    omega

private theorem getD_append_shift (pre suf : List Int) (j : Nat) :
    (pre ++ suf).getD (pre.length + j) 0 = suf.getD j 0 := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (Nat.le_add_right _ _)]
  simp

private theorem getD_append_left' (pre suf : List Int) (j : Nat) (hj : j < pre.length) :
    (pre ++ suf).getD j 0 = pre.getD j 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

theorem blocksWords_split (R : Program) (Q : List Cslib.URM.Instr) (a k : Nat)
    (hk : k < Q.length) :
    blocksWords R a Q = blocksWords R a (Q.take k)
      ++ (instrWords R (a + codeSize (Q.take k)) Q[k]
          ++ blocksWords R (a + codeSize (Q.take k) + instrSize Q[k]) (Q.drop (k + 1))) := by
  conv_lhs => rw [← List.take_append_drop k Q]
  rw [blocksWords_append, List.drop_eq_getElem_cons hk]
  simp only [blocksWords]

theorem blocksWords_split_self (P : Program) (k : Nat) (hk : k < P.length) :
    blocksWords P 8 P = blocksWords P 8 (P.take k) ++
      (instrWords P (entryAddr P k) P[k]
        ++ blocksWords P (entryAddr P (k + 1)) (P.drop (k + 1))) := by
  rw [blocksWords_split P P 8 k hk]
  simp only [show 8 + codeSize (P.take k) = entryAddr P k from rfl, entryAddr_succ P k hk]

theorem prefix_len (P : Program) (k : Nat) :
    (header ++ blocksWords P 8 (P.take k)).length = entryAddr P k := by
  simp only [List.length_append, blocksWords_length, header, entryAddr]
  simp

theorem prefix_len_end (P : Program) :
    (header ++ blocksWords P 8 P).length = epiAddr P := by
  simp only [List.length_append, blocksWords_length, header, epiAddr]
  simp

theorem wordAt_block (P : Program) (inputs : List Nat) (k j : Nat) (hk : k < P.length)
    (hj : j < instrSize P[k]) :
    wordAt P inputs ((entryAddr P k + j : Nat) : Int)
      = (instrWords P (entryAddr P k) P[k]).getD j 0 := by
  have hsplit : compileList P inputs =
      (header ++ blocksWords P 8 (P.take k)) ++
        (instrWords P (entryAddr P k) P[k] ++
          (blocksWords P (entryAddr P (k + 1)) (P.drop (k + 1)) ++
            (epiWords P ++ inputs.map Int.ofNat))) := by
    simp only [compileList, blocksWords_split_self P k hk, List.append_assoc]
  rw [wordAt, Int.toNat_natCast, hsplit, ← prefix_len P k, getD_append_shift,
    getD_append_left' _ _ _ (by rw [instrWords_length]; exact hj)]

theorem wordAt_epi (P : Program) (inputs : List Nat) (j : Nat) (hj : j < 21) :
    wordAt P inputs ((epiAddr P + j : Nat) : Int) = (epiWords P).getD j 0 := by
  have hsplit : compileList P inputs =
      (header ++ blocksWords P 8 P) ++ (epiWords P ++ inputs.map Int.ofNat) := by
    simp only [compileList, List.append_assoc]
  rw [wordAt, Int.toNat_natCast, hsplit, ← prefix_len_end P, getD_append_shift,
    getD_append_left' _ _ _ (by rw [epiWords_length]; exact hj)]

theorem wordAt_header (P : Program) (inputs : List Nat) (j : Nat) (hj : j < 8) :
    wordAt P inputs ((j : Nat) : Int) = header.getD j 0 := by
  have hsplit : compileList P inputs =
      header ++ (blocksWords P 8 P ++ (epiWords P ++ inputs.map Int.ofNat)) := by
    simp only [compileList, List.append_assoc]
  rw [wordAt, Int.toNat_natCast, hsplit]
  exact getD_append_left' _ _ _ (by simpa [header] using hj)

theorem wordAt_reg (P : Program) (inputs : List Nat) (r : Nat) :
    wordAt P inputs (regAddr P r) = ((inputs.getD r 0 : Nat) : Int) := by
  have hsplit : compileList P inputs =
      (header ++ blocksWords P 8 P ++ epiWords P) ++ inputs.map Int.ofNat := by
    simp only [compileList, List.append_assoc]
  have hlen : (header ++ blocksWords P 8 P ++ epiWords P).length = regBase P := by
    simp only [List.length_append, blocksWords_length, epiWords_length, header, regBase, epiAddr]
    simp
  rw [regAddr, wordAt, Int.toNat_natCast, hsplit, ← hlen, getD_append_shift]
  by_cases h : r < inputs.length
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_map, List.getElem?_eq_getElem h]
    rfl
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simpa using Nat.le_of_not_lt h),
      List.getElem?_eq_none (by simpa using Nat.le_of_not_lt h)]
    simp



/-! ## Memory writes -/

theorem get_set (m : Mem) (a v b : Int) : (m.set a v).get b = if b = a then v else m.get b := by
  show (if v == 0 then m.cells.erase a else m.cells.insert a v).getD b 0 = _
  by_cases hv : (v == 0) = true
  · have hv' : v = 0 := by simpa using hv
    rw [if_pos hv, Std.HashMap.getD_erase]
    by_cases hb : b = a
    · rw [if_pos (by simp [hb]), if_pos hb, hv']
    · rw [if_neg (by simpa using fun h => hb h.symm), if_neg hb]
      rfl
  · rw [if_neg hv, Std.HashMap.getD_insert]
    by_cases hb : b = a
    · rw [if_pos (by simp [hb]), if_pos hb]
    · rw [if_neg (by simpa using fun h => hb h.symm), if_neg hb]
      rfl

theorem extent_set (m : Mem) (a v : Int) : (m.set a v).extent = max m.extent (a + 1) := rfl

/-! ## One subleq instruction -/

/-- The subtract-and-branch case. -/
theorem reaches_sub (m : Mem) (pc : Int) (inp : Input) (out : ByteArray) (es : List Event)
    (hpc : 0 ≤ pc) (hext : pc < m.extent)
    (hA : 0 ≤ m.get pc) (hB : 0 ≤ m.get (pc + 1)) :
    Reaches exec ⟨m, pc, inp, out, es⟩
      ⟨m.set (m.get (pc + 1)) (m.get (m.get (pc + 1)) - m.get (m.get pc)),
        (if m.get (m.get (pc + 1)) - m.get (m.get pc) ≤ 0 then m.get (pc + 2) else pc + 3),
        inp, out, es⟩ :=
  Reaches.one fun f => by
    have hrun : ¬ (decide (pc < 0) || decide (pc ≥ m.extent)) = true := by
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      omega
    have hA1 : ¬ (m.get pc == -1) = true := by simp only [beq_iff_eq]; omega
    have hB1 : ¬ (m.get (pc + 1) == -1) = true := by simp only [beq_iff_eq]; omega
    have hA2 : ¬ m.get pc < 0 := by omega
    have hB2 : ¬ m.get (pc + 1) < 0 := by omega
    simp only [exec, if_neg hrun, if_neg hA1, if_neg hB1, if_neg hA2, if_neg hB2]

/-- The output case: `B == -1` writes one byte and never branches. -/
theorem reaches_out (m : Mem) (pc : Int) (inp : Input) (out : ByteArray) (es : List Event)
    (hpc : 0 ≤ pc) (hext : pc < m.extent)
    (hA : 0 ≤ m.get pc) (hB : m.get (pc + 1) = -1) :
    Reaches exec ⟨m, pc, inp, out, es⟩
      ⟨m, pc + 3, inp, out.push (((m.get (m.get pc)).emod 256).toNat.toUInt8),
        Event.out (((m.get (m.get pc)).emod 256).toNat.toUInt8) :: es⟩ :=
  Reaches.one fun f => by
    have hrun : ¬ (decide (pc < 0) || decide (pc ≥ m.extent)) = true := by
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      omega
    have hA1 : ¬ (m.get pc == -1) = true := by simp only [beq_iff_eq]; omega
    have hB1 : (m.get (pc + 1) == -1) = true := by simp only [beq_iff_eq]; omega
    have hA2 : ¬ m.get pc < 0 := by omega
    simp only [exec, if_neg hrun, if_neg hA1, if_pos hB1, if_neg hA2, State.emit]

/-- A negative program counter halts. -/
theorem exec_halt (m : Mem) (pc : Int) (inp : Input) (out : ByteArray) (es : List Event) (h : pc < 0) (f : Nat) :
    exec (f + 1) ⟨m, pc, inp, out, es⟩ = (⟨m, pc, inp, out, es⟩, Exit.halted) := by
  have hrun : (decide (pc < 0) || decide (pc ≥ m.extent)) = true := by
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact Or.inl h
  simp only [exec, if_pos hrun]



/-! ## Address arithmetic -/

theorem codeSize_take_le (P : Program) (k : Nat) : codeSize (P.take k) ≤ codeSize P := by
  conv_rhs => rw [← List.take_append_drop k P]
  rw [codeSize_append]
  omega

theorem entryAddr_le_epi (P : Program) (k : Nat) : entryAddr P k ≤ epiAddr P := by
  simp only [entryAddr, epiAddr]
  have := codeSize_take_le P k
  omega

theorem eight_le_entryAddr (P : Program) (k : Nat) : 8 ≤ entryAddr P k := by
  simp [entryAddr]

theorem code_bound (P : Program) (k : Nat) (hk : k < P.length) (j : Nat)
    (hj : j < instrSize P[k]) : entryAddr P k + j < regBase P := by
  have h1 : entryAddr P k + instrSize P[k] = entryAddr P (k + 1) := entryAddr_succ P k hk
  have h2 : entryAddr P (k + 1) ≤ epiAddr P := entryAddr_le_epi P (k + 1)
  have h3 : epiAddr P + 21 = regBase P := rfl
  omega

theorem regBase_ge (P : Program) : 29 ≤ regBase P := by
  simp only [regBase, epiAddr]
  omega

theorem regAddr_ge (P : Program) (r : Nat) : (regBase P : Int) ≤ regAddr P r := by
  simp only [regAddr]
  omega

theorem regAddr_inj (P : Program) {r r' : Nat} (h : regAddr P r = regAddr P r') : r = r' := by
  have h' : regBase P + r = regBase P + r' := by
    simp only [regAddr] at h
    exact_mod_cast h
  omega

/-! ## The simulation invariant -/

/-- The compiled machine is in step with the URM: the code region still holds
the compiled image, the four fixed cells hold their constants, and the cell
for each URM register holds that register. Cells 5 and 6 are scratch and are
deliberately unconstrained. -/
structure Ok (P : Program) (inputs : List Nat) (m : Mem) (regs : Regs) : Prop where
  /-- The code region is untouched. -/
  code : ∀ a : Int, 8 ≤ a → a < (regBase P : Int) → m.get a = wordAt P inputs a
  /-- Cell 3 holds zero. -/
  zero : m.get 3 = 0
  /-- Cell 4 holds minus one. -/
  neg : m.get 4 = -1
  /-- Cell 7 holds the byte the epilogue prints. -/
  outc : m.get 7 = 49
  /-- Each register cell holds its register. -/
  reg : ∀ r : Nat, m.get (regAddr P r) = ((regs r : Nat) : Int)
  /-- Memory extends past the whole code region. -/
  ext : (regBase P : Int) ≤ m.extent

theorem Ok.set_scratch {P : Program} {inputs : List Nat} {m : Mem} {regs : Regs}
    (h : Ok P inputs m regs) {b : Int} (hb : b = 3 ∨ b = 5 ∨ b = 6) (v : Int)
    (hv : b = 3 → v = 0) : Ok P inputs (m.set b v) regs := by
  have hbne : ∀ a : Int, 8 ≤ a → a ≠ b := by
    intro a ha hc
    rcases hb with h | h | h <;> omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha hlt
    rw [get_set, if_neg (hbne a ha), h.code a ha hlt]
  · rw [get_set]
    by_cases h3 : (3 : Int) = b
    · rw [if_pos h3, hv h3.symm]
    · rw [if_neg h3]; exact h.zero
  · rw [get_set, if_neg (by omega), h.neg]
  · rw [get_set, if_neg (by omega), h.outc]
  · intro r
    have := regAddr_ge P r
    have := regBase_ge P
    rw [get_set, if_neg (by omega), h.reg r]
  · rw [extent_set]
    exact le_trans h.ext (le_max_left _ _)

theorem Ok.set_reg {P : Program} {inputs : List Nat} {m : Mem} {regs : Regs}
    (h : Ok P inputs m regs) (r : Nat) (v : Nat) :
    Ok P inputs (m.set (regAddr P r) ((v : Nat) : Int)) (regs.write r v) := by
  have hge := regAddr_ge P r
  have hb := regBase_ge P
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha hlt
    rw [get_set, if_neg (by omega), h.code a ha hlt]
  · rw [get_set, if_neg (by omega)]; exact h.zero
  · rw [get_set, if_neg (by omega)]; exact h.neg
  · rw [get_set, if_neg (by omega)]; exact h.outc
  · intro r'
    rw [get_set]
    by_cases hr : r' = r
    · subst hr
      rw [if_pos rfl]
      simp [Cslib.URM.Regs.write]
    · rw [if_neg (fun hc => hr (regAddr_inj P hc)), h.reg r', Cslib.URM.Regs.write,
        Function.update_of_ne hr]
  · rw [extent_set]
    exact le_trans h.ext (le_max_left _ _)



variable {P : Program} {inputs : List Nat} {m : Mem} {regs : Regs}

/-! ## Fetching instructions -/

theorem get_code (hok : Ok P inputs m regs) {k : Nat} (i : Cslib.URM.Instr)
    (hk : k < P.length) (hPk : P[k] = i) (j : Nat) (hj : j < instrSize i) :
    m.get ((entryAddr P k + j : Nat) : Int) = (instrWords P (entryAddr P k) i).getD j 0 := by
  have hj' : j < instrSize P[k] := by rw [hPk]; exact hj
  have hb := code_bound P k hk j hj'
  have h8 : 8 ≤ entryAddr P k + j := by have := eight_le_entryAddr P k; omega
  rw [hok.code _ (by exact_mod_cast h8) (by exact_mod_cast hb),
    wordAt_block P inputs k j hk hj', hPk]

theorem get_epi (hok : Ok P inputs m regs) (j : Nat) (hj : j < 21) :
    m.get ((epiAddr P + j : Nat) : Int) = (epiWords P).getD j 0 := by
  have h8 : 8 ≤ epiAddr P + j := by simp only [epiAddr]; omega
  have hb : epiAddr P + j < regBase P := by simp only [regBase]; omega
  rw [hok.code _ (by exact_mod_cast h8) (by exact_mod_cast hb), wordAt_epi P inputs j hj]

/-! ## One subleq instruction, with its operands named -/

theorem reaches_word (m : Mem) (p A B C : Int) (inp : Input) (out : ByteArray) (es : List Event)
    (hp : 0 ≤ p) (hext : p < m.extent)
    (hA : m.get p = A) (hB : m.get (p + 1) = B) (hC : m.get (p + 2) = C)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) :
    Reaches exec ⟨m, p, inp, out, es⟩
      ⟨m.set B (m.get B - m.get A),
        (if m.get B - m.get A ≤ 0 then C else p + 3), inp, out, es⟩ := by
  have h := reaches_sub m p inp out es hp hext (by rw [hA]; exact hA0) (by rw [hB]; exact hB0)
  rw [hA, hB, hC] at h
  exact h

theorem step_code (hok : Ok P inputs m regs) {k : Nat} (i : Cslib.URM.Instr)
    (hk : k < P.length) (hPk : P[k] = i) (j : Nat) (hj : j + 2 < instrSize i)
    {A B C : Int}
    (hA : (instrWords P (entryAddr P k) i).getD j 0 = A)
    (hB : (instrWords P (entryAddr P k) i).getD (j + 1) 0 = B)
    (hC : (instrWords P (entryAddr P k) i).getD (j + 2) 0 = C)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (inp : Input) (out : ByteArray) (es : List Event) :
    Reaches exec ⟨m, ((entryAddr P k + j : Nat) : Int), inp, out, es⟩
      ⟨m.set B (m.get B - m.get A),
        (if m.get B - m.get A ≤ 0 then C else ((entryAddr P k + (j + 3) : Nat) : Int)),
        inp, out, es⟩ := by
  have hj' : j < instrSize P[k] := by rw [hPk]; omega
  have hb := code_bound P k hk j hj'
  have hext : ((entryAddr P k + j : Nat) : Int) < m.extent := by
    have := hok.ext
    have : ((entryAddr P k + j : Nat) : Int) < (regBase P : Int) := by exact_mod_cast hb
    omega
  have e1 : ((entryAddr P k + j : Nat) : Int) + 1 = ((entryAddr P k + (j + 1) : Nat) : Int) := by
    push_cast; omega
  have e2 : ((entryAddr P k + j : Nat) : Int) + 2 = ((entryAddr P k + (j + 2) : Nat) : Int) := by
    push_cast; omega
  have e3 : ((entryAddr P k + j : Nat) : Int) + 3 = ((entryAddr P k + (j + 3) : Nat) : Int) := by
    push_cast; omega
  have h := reaches_word m ((entryAddr P k + j : Nat) : Int) A B C inp out es
    (Int.natCast_nonneg _) hext
    (by rw [get_code hok i hk hPk j (by omega), hA])
    (by rw [e1, get_code hok i hk hPk (j + 1) (by omega), hB])
    (by rw [e2, get_code hok i hk hPk (j + 2) (by omega), hC])
    hA0 hB0
  rw [e3] at h
  exact h

theorem step_epi (hok : Ok P inputs m regs) (j : Nat) (hj : j + 2 < 21)
    {A B C : Int}
    (hA : (epiWords P).getD j 0 = A)
    (hB : (epiWords P).getD (j + 1) 0 = B)
    (hC : (epiWords P).getD (j + 2) 0 = C)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (inp : Input) (out : ByteArray) (es : List Event) :
    Reaches exec ⟨m, ((epiAddr P + j : Nat) : Int), inp, out, es⟩
      ⟨m.set B (m.get B - m.get A),
        (if m.get B - m.get A ≤ 0 then C else ((epiAddr P + (j + 3) : Nat) : Int)),
        inp, out, es⟩ := by
  have hb : epiAddr P + j < regBase P := by simp only [regBase]; omega
  have hext : ((epiAddr P + j : Nat) : Int) < m.extent := by
    have h1 := hok.ext
    have h2 : ((epiAddr P + j : Nat) : Int) < (regBase P : Int) := by exact_mod_cast hb
    omega
  have e1 : ((epiAddr P + j : Nat) : Int) + 1 = ((epiAddr P + (j + 1) : Nat) : Int) := by
    push_cast; omega
  have e2 : ((epiAddr P + j : Nat) : Int) + 2 = ((epiAddr P + (j + 2) : Nat) : Int) := by
    push_cast; omega
  have e3 : ((epiAddr P + j : Nat) : Int) + 3 = ((epiAddr P + (j + 3) : Nat) : Int) := by
    push_cast; omega
  have h := reaches_word m ((epiAddr P + j : Nat) : Int) A B C inp out es
    (Int.natCast_nonneg _) hext
    (by rw [get_epi hok j (by omega), hA])
    (by rw [e1, get_epi hok (j + 1) (by omega), hB])
    (by rw [e2, get_epi hok (j + 2) (by omega), hC])
    hA0 hB0
  rw [e3] at h
  exact h

/-- The one output instruction, in the epilogue. -/
theorem step_epi_out (hok : Ok P inputs m regs) (inp : Input) (out : ByteArray) (es : List Event) :
    Reaches exec ⟨m, ((epiAddr P + 12 : Nat) : Int), inp, out, es⟩
      ⟨m, ((epiAddr P + 15 : Nat) : Int), inp, out.push 49, Event.out 49 :: es⟩ := by
  have hb : epiAddr P + 12 < regBase P := by simp only [regBase]; omega
  have hext : ((epiAddr P + 12 : Nat) : Int) < m.extent := by
    have h1 := hok.ext
    have h2 : ((epiAddr P + 12 : Nat) : Int) < (regBase P : Int) := by exact_mod_cast hb
    omega
  have e1 : ((epiAddr P + 12 : Nat) : Int) + 1 = ((epiAddr P + 13 : Nat) : Int) := by
    push_cast; omega
  have e3 : ((epiAddr P + 12 : Nat) : Int) + 3 = ((epiAddr P + 15 : Nat) : Int) := by
    push_cast; omega
  have hA : m.get ((epiAddr P + 12 : Nat) : Int) = 7 := by
    rw [get_epi hok 12 (by omega)]; rfl
  have hB : m.get (((epiAddr P + 12 : Nat) : Int) + 1) = -1 := by
    rw [e1, get_epi hok 13 (by omega)]; rfl
  have h := reaches_out m ((epiAddr P + 12 : Nat) : Int) inp out es (Int.natCast_nonneg _) hext
    (by rw [hA]; omega) hB
  rw [hA, hok.outc, e3] at h
  have : ((49 : Int).emod 256).toNat.toUInt8 = (49 : UInt8) := by decide
  rw [this] at h
  exact h




/-! ## One URM instruction at a time

Each block lemma takes a memory satisfying `Ok` at the entry of block `k` and
produces one satisfying `Ok` at the entry of the block the URM would go to,
with the registers the URM would have. -/

theorem write_write (σ : Regs) (n a b : Nat) : (σ.write n a).write n b = σ.write n b := by
  funext j
  simp only [Cslib.URM.Regs.write, Function.update]
  split <;> rfl

private theorem scratch5 (h : Ok P inputs m regs) (v : Int) :
    Ok P inputs (m.set 5 v) regs := h.set_scratch (Or.inr (Or.inl rfl)) v (by omega)

private theorem scratch6 (h : Ok P inputs m regs) (v : Int) :
    Ok P inputs (m.set 6 v) regs := h.set_scratch (Or.inr (Or.inr rfl)) v (by omega)

private theorem scratch3 (h : Ok P inputs m regs) :
    Ok P inputs (m.set 3 0) regs := h.set_scratch (Or.inl rfl) 0 (fun _ => rfl)

private theorem get_set_self (m : Mem) (a v : Int) : (m.set a v).get a = v := by
  rw [get_set, if_pos rfl]

private theorem get_set_other (m : Mem) {a b : Int} (h : b ≠ a) (v : Int) :
    (m.set a v).get b = m.get b := by rw [get_set, if_neg h]

theorem block_Z (hok : Ok P inputs m regs) {k r : Nat} (hk : k < P.length)
    (hPk : P[k] = .Z r) (inp : Input) (out : ByteArray) (es : List Event) :
    ∃ m', Reaches exec ⟨m, ((entryAddr P k : Nat) : Int), inp, out, es⟩
        ⟨m', ((entryAddr P (k + 1) : Nat) : Int), inp, out, es⟩
      ∧ Ok P inputs m' (regs.write r 0) := by
  have hsucc : entryAddr P k + 3 = entryAddr P (k + 1) := by
    have h := entryAddr_succ P k hk
    rw [hPk] at h
    simpa [instrSize] using h
  have s0 := step_code (A := regAddr P r) (B := regAddr P r)
      (C := ((entryAddr P k + 3 : Nat) : Int)) hok (.Z r) hk hPk 0 (by simp [instrSize])
      rfl rfl rfl (Int.natCast_nonneg _) (Int.natCast_nonneg _) inp out es
  rw [show m.get (regAddr P r) - m.get (regAddr P r) = 0 from by omega,
    if_pos (le_refl 0), Nat.add_zero, hsucc] at s0
  refine ⟨m.set (regAddr P r) 0, s0, ?_⟩
  have := hok.set_reg r 0
  simpa using this

theorem block_S (hok : Ok P inputs m regs) {k r : Nat} (hk : k < P.length)
    (hPk : P[k] = .S r) (inp : Input) (out : ByteArray) (es : List Event) :
    ∃ m', Reaches exec ⟨m, ((entryAddr P k : Nat) : Int), inp, out, es⟩
        ⟨m', ((entryAddr P (k + 1) : Nat) : Int), inp, out, es⟩
      ∧ Ok P inputs m' (regs.write r (regs.read r + 1)) := by
  have hsucc : entryAddr P k + 3 = entryAddr P (k + 1) := by
    have h := entryAddr_succ P k hk
    rw [hPk] at h
    simpa [instrSize] using h
  have s0 := step_code (A := 4) (B := regAddr P r)
      (C := ((entryAddr P k + 3 : Nat) : Int)) hok (.S r) hk hPk 0 (by simp [instrSize])
      rfl rfl rfl (by omega) (Int.natCast_nonneg _) inp out es
  have hval : m.get (regAddr P r) - m.get 4 = ((regs.read r + 1 : Nat) : Int) := by
    rw [hok.reg r, hok.neg]
    simp [Cslib.URM.Regs.read]
  rw [hval, if_neg (by omega), Nat.add_zero,
    show entryAddr P k + (0 + 3) = entryAddr P (k + 1) from by omega] at s0
  exact ⟨_, s0, hok.set_reg r (regs.read r + 1)⟩




private theorem reg_ne_scratch (P : Program) (r : Nat) (a : Int) (ha : a ≤ 7) :
    regAddr P r ≠ a := by
  have h1 := regAddr_ge P r
  have h2 := regBase_ge P
  omega

theorem block_T (hok : Ok P inputs m regs) {k x y : Nat} (hk : k < P.length)
    (hPk : P[k] = .T x y) (inp : Input) (out : ByteArray) (es : List Event) :
    ∃ m', Reaches exec ⟨m, ((entryAddr P k : Nat) : Int), inp, out, es⟩
        ⟨m', ((entryAddr P (k + 1) : Nat) : Int), inp, out, es⟩
      ∧ Ok P inputs m' (regs.write y (regs.read x)) := by
  have hsucc : entryAddr P k + 12 = entryAddr P (k + 1) := by
    have h := entryAddr_succ P k hk
    rw [hPk] at h
    simpa [instrSize] using h
  -- `T1 := 0`
  have s0 := step_code (A := 5) (B := 5) (C := ((entryAddr P k + 3 : Nat) : Int))
      hok (.T x y) hk hPk 0 (by simp [instrSize]) rfl rfl rfl (by omega) (by omega) inp out es
  rw [show m.get 5 - m.get 5 = 0 from by omega, if_pos (le_refl 0), Nat.add_zero] at s0
  have ok1 : Ok P inputs (m.set 5 0) regs := scratch5 hok 0
  have g1_5 : (m.set 5 0).get 5 = 0 := get_set_self m 5 0
  have g1_x : (m.set 5 0).get (regAddr P x) = ((regs.read x : Nat) : Int) := by
    rw [get_set_other m (reg_ne_scratch P x 5 (by omega)) 0]; exact hok.reg x
  -- `T1 := -R[x]`
  have s1 := step_code (A := regAddr P x) (B := 5) (C := ((entryAddr P k + 6 : Nat) : Int))
      ok1 (.T x y) hk hPk 3 (by simp [instrSize]) rfl rfl rfl
      (Int.natCast_nonneg _) (by omega) inp out es
  rw [g1_5, g1_x, if_pos (by omega)] at s1
  have ok2 : Ok P inputs ((m.set 5 0).set 5 (0 - ((regs.read x : Nat) : Int))) regs :=
    scratch5 ok1 _
  have g2_5 : ((m.set 5 0).set 5 (0 - ((regs.read x : Nat) : Int))).get 5
      = 0 - ((regs.read x : Nat) : Int) := get_set_self _ 5 _
  -- `R[y] := 0`
  have s2 := step_code (A := regAddr P y) (B := regAddr P y)
      (C := ((entryAddr P k + 9 : Nat) : Int)) ok2 (.T x y) hk hPk 6 (by simp [instrSize])
      rfl rfl rfl (Int.natCast_nonneg _) (Int.natCast_nonneg _) inp out es
  rw [show ((m.set 5 0).set 5 (0 - ((regs.read x : Nat) : Int))).get (regAddr P y)
        - ((m.set 5 0).set 5 (0 - ((regs.read x : Nat) : Int))).get (regAddr P y) = 0 from by omega,
    if_pos (le_refl 0)] at s2
  have ok3 : Ok P inputs
      (((m.set 5 0).set 5 (0 - ((regs.read x : Nat) : Int))).set (regAddr P y) 0)
      (regs.write y 0) := by
    have := ok2.set_reg y 0
    simpa using this
  have g3_y : (((m.set 5 0).set 5 (0 - ((regs.read x : Nat) : Int))).set (regAddr P y) 0).get
      (regAddr P y) = 0 := get_set_self _ _ _
  have g3_5 : (((m.set 5 0).set 5 (0 - ((regs.read x : Nat) : Int))).set (regAddr P y) 0).get 5
      = 0 - ((regs.read x : Nat) : Int) := by
    rw [get_set_other _ (fun hc => reg_ne_scratch P y 5 (by omega) hc.symm) 0, g2_5]
  -- `R[y] := R[x]`
  have s3 := step_code (A := 5) (B := regAddr P y) (C := ((entryAddr P k + 12 : Nat) : Int))
      ok3 (.T x y) hk hPk 9 (by simp [instrSize]) rfl rfl rfl (by omega)
      (Int.natCast_nonneg _) inp out es
  rw [g3_y, g3_5, show (0 : Int) - (0 - ((regs.read x : Nat) : Int))
      = ((regs.read x : Nat) : Int) from by omega,
    show entryAddr P k + (9 + 3) = entryAddr P k + 12 from by omega, hsucc] at s3
  rw [show (if ((regs.read x : Nat) : Int) ≤ 0 then ((entryAddr P (k + 1) : Nat) : Int)
        else ((entryAddr P (k + 1) : Nat) : Int)) = ((entryAddr P (k + 1) : Nat) : Int) from by
    split <;> rfl] at s3
  refine ⟨_, Reaches.trans s0 (Reaches.trans s1 (Reaches.trans s2 s3)), ?_⟩
  have := ok3.set_reg y (regs.read x)
  rwa [write_write] at this




/-- The first five subleq instructions of a `J` block: they leave `X - Y` in
scratch cell 6 and `-X` in scratch cell 5, and branch on `X <= Y`. -/
private theorem J_prefix (hok : Ok P inputs m regs) {k x y q : Nat} (hk : k < P.length)
    (hPk : P[k] = .J x y q) (inp : Input) (out : ByteArray) (es : List Event) :
    ∃ m5, Reaches exec ⟨m, ((entryAddr P k : Nat) : Int), inp, out, es⟩
        ⟨m5, (if ((regs.read x : Nat) : Int) - ((regs.read y : Nat) : Int) ≤ 0
              then ((entryAddr P k + 18 : Nat) : Int) else ((entryAddr P k + 15 : Nat) : Int)),
          inp, out, es⟩
      ∧ Ok P inputs m5 regs
      ∧ m5.get 5 = 0 - ((regs.read x : Nat) : Int)
      ∧ m5.get 6 = ((regs.read x : Nat) : Int) - ((regs.read y : Nat) : Int) := by
  have s0 := step_code (A := 5) (B := 5) (C := ((entryAddr P k + 3 : Nat) : Int))
      hok (.J x y q) hk hPk 0 (by simp [instrSize]) rfl rfl rfl (by omega) (by omega) inp out es
  rw [show m.get 5 - m.get 5 = 0 from by omega, if_pos (le_refl 0), Nat.add_zero] at s0
  have ok1 : Ok P inputs (m.set 5 0) regs := scratch5 hok 0
  have g1_5 : (m.set 5 0).get 5 = 0 := get_set_self m 5 0
  have g1_x : (m.set 5 0).get (regAddr P x) = ((regs.read x : Nat) : Int) := by
    rw [get_set_other m (reg_ne_scratch P x 5 (by omega)) 0]; exact hok.reg x
  have s1 := step_code (A := regAddr P x) (B := 5) (C := ((entryAddr P k + 6 : Nat) : Int))
      ok1 (.J x y q) hk hPk 3 (by simp [instrSize]) rfl rfl rfl
      (Int.natCast_nonneg _) (by omega) inp out es
  rw [g1_5, g1_x, if_pos (by omega)] at s1
  set m2 := (m.set 5 0).set 5 (0 - ((regs.read x : Nat) : Int)) with hm2
  have ok2 : Ok P inputs m2 regs := scratch5 ok1 _
  have g2_5 : m2.get 5 = 0 - ((regs.read x : Nat) : Int) := get_set_self _ 5 _
  have s2 := step_code (A := 6) (B := 6) (C := ((entryAddr P k + 9 : Nat) : Int))
      ok2 (.J x y q) hk hPk 6 (by simp [instrSize]) rfl rfl rfl (by omega) (by omega) inp out es
  rw [show m2.get 6 - m2.get 6 = 0 from by omega, if_pos (le_refl 0)] at s2
  set m3 := m2.set 6 0 with hm3
  have ok3 : Ok P inputs m3 regs := scratch6 ok2 0
  have g3_6 : m3.get 6 = 0 := get_set_self _ 6 0
  have g3_5 : m3.get 5 = 0 - ((regs.read x : Nat) : Int) := by
    rw [hm3, get_set_other _ (by omega) 0, g2_5]
  have s3 := step_code (A := 5) (B := 6) (C := ((entryAddr P k + 12 : Nat) : Int))
      ok3 (.J x y q) hk hPk 9 (by simp [instrSize]) rfl rfl rfl (by omega) (by omega) inp out es
  rw [g3_6, g3_5, show (0 : Int) - (0 - ((regs.read x : Nat) : Int))
      = ((regs.read x : Nat) : Int) from by omega,
    show entryAddr P k + (9 + 3) = entryAddr P k + 12 from by omega,
    show (if ((regs.read x : Nat) : Int) ≤ 0 then ((entryAddr P k + 12 : Nat) : Int)
        else ((entryAddr P k + 12 : Nat) : Int)) = ((entryAddr P k + 12 : Nat) : Int) from by
      split <;> rfl] at s3
  set m4 := m3.set 6 ((regs.read x : Nat) : Int) with hm4
  have ok4 : Ok P inputs m4 regs := scratch6 ok3 _
  have g4_6 : m4.get 6 = ((regs.read x : Nat) : Int) := get_set_self _ 6 _
  have g4_5 : m4.get 5 = 0 - ((regs.read x : Nat) : Int) := by
    rw [hm4, get_set_other _ (by omega) _, g3_5]
  have g4_y : m4.get (regAddr P y) = ((regs.read y : Nat) : Int) := ok4.reg y
  have s4 := step_code (A := regAddr P y) (B := 6) (C := ((entryAddr P k + 18 : Nat) : Int))
      ok4 (.J x y q) hk hPk 12 (by simp [instrSize]) rfl rfl rfl
      (Int.natCast_nonneg _) (by omega) inp out es
  rw [g4_6, g4_y, show entryAddr P k + (12 + 3) = entryAddr P k + 15 from by omega] at s4
  refine ⟨m4.set 6 (((regs.read x : Nat) : Int) - ((regs.read y : Nat) : Int)),
    Reaches.trans s0 (Reaches.trans s1 (Reaches.trans s2 (Reaches.trans s3 s4))),
    scratch6 ok4 _, ?_, get_set_self _ 6 _⟩
  rw [get_set_other _ (by omega) _, g4_5]

theorem block_J_taken (hok : Ok P inputs m regs) {k x y q : Nat} (hk : k < P.length)
    (hPk : P[k] = .J x y q) (heq : regs.read x = regs.read y)
    (inp : Input) (out : ByteArray) (es : List Event) :
    ∃ m', Reaches exec ⟨m, ((entryAddr P k : Nat) : Int), inp, out, es⟩
        ⟨m', target P q, inp, out, es⟩ ∧ Ok P inputs m' regs := by
  obtain ⟨m5, hr, ok5, g5_5, g5_6⟩ := J_prefix hok hk hPk inp out es
  rw [heq] at g5_6
  rw [heq, if_pos (by omega)] at hr
  have s5 := step_code (A := 5) (B := 5) (C := ((entryAddr P k + 21 : Nat) : Int))
      ok5 (.J x y q) hk hPk 18 (by simp [instrSize]) rfl rfl rfl (by omega) (by omega) inp out es
  rw [show m5.get 5 - m5.get 5 = 0 from by omega, if_pos (le_refl 0)] at s5
  set m6 := m5.set 5 0 with hm6
  have ok6 : Ok P inputs m6 regs := scratch5 ok5 0
  have g6_5 : m6.get 5 = 0 := get_set_self _ 5 0
  have g6_6 : m6.get 6 = 0 := by rw [hm6, get_set_other _ (by omega) 0, g5_6]; omega
  have s6 := step_code (A := 6) (B := 5) (C := target P q)
      ok6 (.J x y q) hk hPk 21 (by simp [instrSize]) rfl rfl rfl (by omega) (by omega) inp out es
  rw [g6_5, g6_6, show (0 : Int) - 0 = 0 from by omega, if_pos (le_refl 0)] at s6
  exact ⟨m6.set 5 0, Reaches.trans hr (Reaches.trans s5 s6), scratch5 ok6 0⟩

theorem block_J_untaken (hok : Ok P inputs m regs) {k x y q : Nat} (hk : k < P.length)
    (hPk : P[k] = .J x y q) (hne : regs.read x ≠ regs.read y)
    (inp : Input) (out : ByteArray) (es : List Event) :
    ∃ m', Reaches exec ⟨m, ((entryAddr P k : Nat) : Int), inp, out, es⟩
        ⟨m', ((entryAddr P (k + 1) : Nat) : Int), inp, out, es⟩ ∧ Ok P inputs m' regs := by
  have hsucc : entryAddr P k + 27 = entryAddr P (k + 1) := by
    have h := entryAddr_succ P k hk
    rw [hPk] at h
    simpa [instrSize] using h
  have hxy : ((regs.read x : Nat) : Int) ≠ ((regs.read y : Nat) : Int) := by
    intro hc; exact hne (by exact_mod_cast hc)
  obtain ⟨m5, hr, ok5, g5_5, g5_6⟩ := J_prefix hok hk hPk inp out es
  by_cases hlt : ((regs.read x : Nat) : Int) - ((regs.read y : Nat) : Int) ≤ 0
  · -- `X < Y`: the second comparison fails and falls through
    rw [if_pos hlt] at hr
    have s5 := step_code (A := 5) (B := 5) (C := ((entryAddr P k + 21 : Nat) : Int))
        ok5 (.J x y q) hk hPk 18 (by simp [instrSize]) rfl rfl rfl (by omega) (by omega) inp out es
    rw [show m5.get 5 - m5.get 5 = 0 from by omega, if_pos (le_refl 0)] at s5
    set m6 := m5.set 5 0 with hm6
    have ok6 : Ok P inputs m6 regs := scratch5 ok5 0
    have g6_5 : m6.get 5 = 0 := get_set_self _ 5 0
    have g6_6 : m6.get 6 = ((regs.read x : Nat) : Int) - ((regs.read y : Nat) : Int) := by
      rw [hm6, get_set_other _ (by omega) 0, g5_6]
    have s6 := step_code (A := 6) (B := 5) (C := target P q)
        ok6 (.J x y q) hk hPk 21 (by simp [instrSize]) rfl rfl rfl (by omega) (by omega) inp out es
    rw [g6_5, g6_6, if_neg (by omega),
      show entryAddr P k + (21 + 3) = entryAddr P k + 24 from by omega] at s6
    set m7 := m6.set 5 (0 - (((regs.read x : Nat) : Int) - ((regs.read y : Nat) : Int))) with hm7
    have ok7 : Ok P inputs m7 regs := scratch5 ok6 _
    have s7 := step_code (A := 3) (B := 3) (C := ((entryAddr P k + 27 : Nat) : Int))
        ok7 (.J x y q) hk hPk 24 (by simp [instrSize]) rfl rfl rfl (by omega) (by omega) inp out es
    rw [show m7.get 3 - m7.get 3 = 0 from by omega, if_pos (le_refl 0), hsucc] at s7
    exact ⟨m7.set 3 0, Reaches.trans hr (Reaches.trans s5 (Reaches.trans s6 s7)),
      scratch3 ok7⟩
  · -- `X > Y`: the first comparison already falls through
    rw [if_neg hlt] at hr
    have s5 := step_code (A := 3) (B := 3) (C := ((entryAddr P k + 27 : Nat) : Int))
        ok5 (.J x y q) hk hPk 15 (by simp [instrSize]) rfl rfl rfl (by omega) (by omega) inp out es
    rw [show m5.get 3 - m5.get 3 = 0 from by omega, if_pos (le_refl 0), hsucc] at s5
    exact ⟨m5.set 3 0, Reaches.trans hr s5, scratch3 ok5⟩




/-! ## The epilogue

Register 0 is printed in unary: `d` copies of the byte 49. The loop keeps the
count negated in scratch cell 5 and adds one to it each time round, which is
the only test subtract-and-branch offers. -/

theorem epi_loop (inp : Input) : ∀ (d : Nat) (m : Mem) (regs : Regs) (out : ByteArray) (es : List Event),
    Ok P inputs m regs → m.get 5 = -(d : Int) →
    ∃ m' out' es', Reaches exec ⟨m, ((epiAddr P + 6 : Nat) : Int), inp, out, es⟩
        ⟨m', ((epiAddr P + 18 : Nat) : Int), inp, out', es'⟩
      ∧ Ok P inputs m' regs ∧ out'.size = out.size + d := by
  intro d
  induction d with
  | zero =>
    intro m regs out es hok h5
    have s0 := step_epi (A := 4) (B := 5) (C := ((epiAddr P + 12 : Nat) : Int))
        hok 6 (by omega) rfl rfl rfl (by omega) (by omega) inp out es
    rw [h5, hok.neg, if_neg (by omega),
      show epiAddr P + (6 + 3) = epiAddr P + 9 from by omega] at s0
    set m1 := m.set 5 (-((0 : Nat) : Int) - -1) with hm1
    have ok1 : Ok P inputs m1 regs := scratch5 hok _
    have s1 := step_epi (A := 3) (B := 3) (C := ((epiAddr P + 18 : Nat) : Int))
        ok1 9 (by omega) rfl rfl rfl (by omega) (by omega) inp out es
    rw [show m1.get 3 - m1.get 3 = 0 from by omega, if_pos (le_refl 0)] at s1
    exact ⟨m1.set 3 0, out, es, Reaches.trans s0 s1, scratch3 ok1, by simp⟩
  | succ d ih =>
    intro m regs out es hok h5
    have s0 := step_epi (A := 4) (B := 5) (C := ((epiAddr P + 12 : Nat) : Int))
        hok 6 (by omega) rfl rfl rfl (by omega) (by omega) inp out es
    rw [h5, hok.neg, if_pos (by push_cast; omega)] at s0
    set m1 := m.set 5 (-((d + 1 : Nat) : Int) - -1) with hm1
    have ok1 : Ok P inputs m1 regs := scratch5 hok _
    have g1_5 : m1.get 5 = -(d : Int) := by
      rw [hm1, get_set_self]
      push_cast
      omega
    have s1 := step_epi_out ok1 inp out es
    set m2 := m1 with hm2
    have s2 := step_epi (A := 3) (B := 3) (C := ((epiAddr P + 6 : Nat) : Int))
        ok1 15 (by omega) rfl rfl rfl (by omega) (by omega) inp (out.push 49)
        (Event.out 49 :: es)
    rw [show m1.get 3 - m1.get 3 = 0 from by omega, if_pos (le_refl 0)] at s2
    have ok3 : Ok P inputs (m1.set 3 0) regs := scratch3 ok1
    have g3_5 : (m1.set 3 0).get 5 = -(d : Int) := by
      rw [get_set_other _ (by omega) 0, g1_5]
    obtain ⟨m', out', es', hr, ok', hsize⟩ :=
      ih (m1.set 3 0) regs (out.push 49) (Event.out 49 :: es) ok3 g3_5
    refine ⟨m', out', es', Reaches.trans s0 (Reaches.trans s1 (Reaches.trans s2 hr)), ok', ?_⟩
    rw [hsize, ByteArray.size_push]
    omega

/-- The epilogue prints register 0 in unary and halts. -/
theorem exec_epilogue (hok : Ok P inputs m regs) (inp : Input) (out : ByteArray) (es : List Event) :
    ∃ (f : Nat) (s : Langlib.Subleq.State),
      exec f ⟨m, ((epiAddr P : Nat) : Int), inp, out, es⟩ = (s, Exit.halted) ∧
      s.output.size = out.size + regs 0 := by
  have s0 := step_epi (A := 5) (B := 5) (C := ((epiAddr P + 3 : Nat) : Int))
      hok 0 (by omega) rfl rfl rfl (by omega) (by omega) inp out es
  rw [show m.get 5 - m.get 5 = 0 from by omega, if_pos (le_refl 0), Nat.add_zero] at s0
  have ok1 : Ok P inputs (m.set 5 0) regs := scratch5 hok 0
  have g1_5 : (m.set 5 0).get 5 = 0 := get_set_self m 5 0
  have g1_0 : (m.set 5 0).get (regAddr P 0) = ((regs 0 : Nat) : Int) := by
    rw [get_set_other m (reg_ne_scratch P 0 5 (by omega)) 0]; exact hok.reg 0
  have s1 := step_epi (A := regAddr P 0) (B := 5) (C := ((epiAddr P + 6 : Nat) : Int))
      ok1 3 (by omega) rfl rfl rfl (Int.natCast_nonneg _) (by omega) inp out es
  rw [g1_5, g1_0, if_pos (by omega)] at s1
  set m2 := (m.set 5 0).set 5 (0 - ((regs 0 : Nat) : Int)) with hm2
  have ok2 : Ok P inputs m2 regs := scratch5 ok1 _
  have g2_5 : m2.get 5 = -((regs 0 : Nat) : Int) := by
    rw [hm2, get_set_self]; omega
  obtain ⟨m3, out3, es3, hr, ok3, hsize⟩ := epi_loop inp (regs 0) m2 regs out es ok2 g2_5
  have s3 := step_epi (A := 3) (B := 3) (C := -1)
      ok3 18 (by omega) rfl rfl rfl (by omega) (by omega) inp out3 es3
  rw [show m3.get 3 - m3.get 3 = 0 from by omega, if_pos (le_refl 0)] at s3
  obtain ⟨c, hc⟩ :=
    Reaches.trans s0 (Reaches.trans s1 (Reaches.trans hr s3))
  refine ⟨c + 1, ⟨m3.set 3 0, -1, inp, out3, es3⟩, ?_, hsize⟩
  rw [hc 1]
  exact exec_halt _ (-1) inp out3 es3 (by omega) 0



/-! ## The initial state -/

theorem entryAddr_zero (P : Program) : entryAddr P 0 = 8 := by
  simp [entryAddr, codeSize]

theorem ok_init (P : Program) (inputs : List Nat) :
    Ok P inputs (Mem.ofProg (compile P inputs)) (Regs.ofInputs inputs) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha _
    exact img_get P inputs a (by omega)
  · rw [show (3 : Int) = ((3 : Nat) : Int) from rfl, img_get P inputs _ (by omega),
      wordAt_header P inputs 3 (by omega)]
    rfl
  · rw [show (4 : Int) = ((4 : Nat) : Int) from rfl, img_get P inputs _ (by omega),
      wordAt_header P inputs 4 (by omega)]
    rfl
  · rw [show (7 : Int) = ((7 : Nat) : Int) from rfl, img_get P inputs _ (by omega),
      wordAt_header P inputs 7 (by omega)]
    rfl
  · intro r
    rw [img_get P inputs _ (le_trans (by omega) (regAddr_ge P r)), wordAt_reg]
    rfl
  · rw [extent_ofProg, compile, List.size_toArray, compileList_length]
    omega

/-- The first instruction of the image jumps over the data cells. -/
theorem reaches_start (P : Program) (inputs : List Nat) (inp : Input) (out : ByteArray) (es : List Event) :
    ∃ m', Reaches exec ⟨Mem.ofProg (compile P inputs), 0, inp, out, es⟩
        ⟨m', ((entryAddr P 0 : Nat) : Int), inp, out, es⟩
      ∧ Ok P inputs m' (Regs.ofInputs inputs) := by
  have hok := ok_init P inputs
  have hext : (0 : Int) < (Mem.ofProg (compile P inputs)).extent := by
    have := hok.ext
    have := regBase_ge P
    omega
  have h0 : (Mem.ofProg (compile P inputs)).get 0 = 3 := by
    rw [show (0 : Int) = ((0 : Nat) : Int) from rfl, img_get P inputs _ (by omega),
      wordAt_header P inputs 0 (by omega)]
    rfl
  have h1 : (Mem.ofProg (compile P inputs)).get (0 + 1) = 3 := by
    rw [show (0 : Int) + 1 = ((1 : Nat) : Int) from rfl, img_get P inputs _ (by omega),
      wordAt_header P inputs 1 (by omega)]
    rfl
  have h2 : (Mem.ofProg (compile P inputs)).get (0 + 2) = ((entryAddr P 0 : Nat) : Int) := by
    rw [show (0 : Int) + 2 = ((2 : Nat) : Int) from rfl, img_get P inputs _ (by omega),
      wordAt_header P inputs 2 (by omega), entryAddr_zero]
    rfl
  have s0 := reaches_word (Mem.ofProg (compile P inputs)) 0 3 3 ((entryAddr P 0 : Nat) : Int)
    inp out es (le_refl 0) hext h0 h1 h2 (by omega) (by omega)
  rw [show (Mem.ofProg (compile P inputs)).get 3 - (Mem.ofProg (compile P inputs)).get 3 = 0
      from by omega, if_pos (le_refl 0)] at s0
  exact ⟨_, s0, scratch3 hok⟩

/-! ## The simulation -/

private theorem lt_len {P : Program} {k : Nat} {i : Cslib.URM.Instr} (h : P[k]? = some i) :
    k < P.length := by
  cases Nat.lt_or_ge k P.length with
  | inl hlt => exact hlt
  | inr hge => rw [List.getElem?_eq_none hge] at h; exact absurd h (by simp)

private theorem getElem_of_getElem? {P : Program} {k : Nat} {i : Cslib.URM.Instr}
    (h : P[k]? = some i) : P[k]'(lt_len h) = i := by
  rw [List.getElem?_eq_getElem (lt_len h)] at h
  exact Option.some.inj h

/-- One URM step becomes one block of subleq instructions. -/
theorem step_sim (P : Program) (inputs : List Nat) {s s' : Cslib.URM.State}
    (hstep : Step P s s') (m : Mem) (hok : Ok P inputs m s.regs)
    (inp : Input) (out : ByteArray) (es : List Event) :
    ∃ m', Reaches exec ⟨m, ((entryAddr P (min s.pc P.length) : Nat) : Int), inp, out, es⟩
        ⟨m', ((entryAddr P (min s'.pc P.length) : Nat) : Int), inp, out, es⟩
      ∧ Ok P inputs m' s'.regs := by
  cases hstep
  case zero n hi =>
    have hk : s.pc < P.length := lt_len hi
    rw [Nat.min_eq_left (Nat.le_of_lt hk), Nat.min_eq_left (show s.pc + 1 ≤ P.length by omega)]
    exact block_Z hok hk (getElem_of_getElem? hi) inp out es
  case succ n hi =>
    have hk : s.pc < P.length := lt_len hi
    rw [Nat.min_eq_left (Nat.le_of_lt hk), Nat.min_eq_left (show s.pc + 1 ≤ P.length by omega)]
    exact block_S hok hk (getElem_of_getElem? hi) inp out es
  case transfer x y hi =>
    have hk : s.pc < P.length := lt_len hi
    rw [Nat.min_eq_left (Nat.le_of_lt hk), Nat.min_eq_left (show s.pc + 1 ≤ P.length by omega)]
    exact block_T hok hk (getElem_of_getElem? hi) inp out es
  case jump_eq x y q hi heq =>
    have hk : s.pc < P.length := lt_len hi
    rw [Nat.min_eq_left (Nat.le_of_lt hk)]
    obtain ⟨m', hr, ok'⟩ := block_J_taken hok hk (getElem_of_getElem? hi) heq inp out es
    exact ⟨m', by rw [target] at hr; exact hr, ok'⟩
  case jump_ne x y q hi hne =>
    have hk : s.pc < P.length := lt_len hi
    rw [Nat.min_eq_left (Nat.le_of_lt hk), Nat.min_eq_left (show s.pc + 1 ≤ P.length by omega)]
    exact block_J_untaken hok hk (getElem_of_getElem? hi) hne inp out es

/-- A whole URM run becomes a whole run of the compiled program. -/
theorem steps_sim (P : Program) (inputs : List Nat) {s₀ s : Cslib.URM.State}
    (hsteps : Steps P s₀ s) (m : Mem) (hok : Ok P inputs m s₀.regs)
    (inp : Input) (out : ByteArray) (es : List Event) :
    ∃ m', Reaches exec ⟨m, ((entryAddr P (min s₀.pc P.length) : Nat) : Int), inp, out, es⟩
        ⟨m', ((entryAddr P (min s.pc P.length) : Nat) : Int), inp, out, es⟩
      ∧ Ok P inputs m' s.regs := by
  induction hsteps with
  | refl => exact ⟨m, Reaches.refl _ _, hok⟩
  | tail _ hlast ih =>
    obtain ⟨m₁, hr₁, ok₁⟩ := ih
    obtain ⟨m₂, hr₂, ok₂⟩ := step_sim P inputs hlast m₁ ok₁ inp out es
    exact ⟨m₂, Reaches.trans hr₁ hr₂, ok₂⟩

/-! ## Reading the answer back

The compiled program prints the byte 49 once per unit of register 0, so the
decoder is the length of the output. -/

/-- The decoder of the simulation theorem: the URM's answer is the number of
bytes the compiled program printed. -/
def decodeOutput (b : ByteArray) : Option Nat := some b.size

/-- **The simulation.** Whenever the URM `P` halts on `inputs` with `result`
in register 0, the compiled subleq program halts, for some fuel bound, having
printed `result` bytes. The input stream is irrelevant: the compiled program
never executes an input instruction. -/
theorem simulation (P : Program) (inputs : List Nat) (result : Nat)
    (h : HaltsWithResult P inputs result) (input : Input) :
    ∃ f, (evalProg (compile P inputs) input f).exit = Exit.halted ∧
         decodeOutput (evalProg (compile P inputs) input f).output = some result := by
  obtain ⟨s, hsteps, hhalt, hres⟩ := h
  obtain ⟨m₀, hstart, ok₀⟩ := reaches_start P inputs input ByteArray.empty []
  have hok₀ : Ok P inputs m₀ (Cslib.URM.State.init inputs).regs := ok₀
  obtain ⟨m₁, hsim, ok₁⟩ := steps_sim P inputs hsteps m₀ hok₀ input ByteArray.empty []
  simp only [Cslib.URM.State.init, Nat.zero_min,
    Nat.min_eq_right (show P.length ≤ s.pc from hhalt), entryAddr_length] at hsim
  obtain ⟨f₁, s₁, hexec, hsize⟩ := exec_epilogue ok₁ input ByteArray.empty []
  obtain ⟨c, hc⟩ := Reaches.trans hstart hsim
  refine ⟨c + f₁, ?_, ?_⟩
  · simp only [evalProg]
    rw [show ({ mem := Mem.ofProg (compile P inputs), input := input } : Langlib.Subleq.State)
        = ⟨Mem.ofProg (compile P inputs), 0, input, ByteArray.empty, []⟩ from rfl, hc f₁, hexec]
  · simp only [evalProg]
    rw [show ({ mem := Mem.ofProg (compile P inputs), input := input } : Langlib.Subleq.State)
        = ⟨Mem.ofProg (compile P inputs), 0, input, ByteArray.empty, []⟩ from rfl, hc f₁, hexec]
    simp only [decodeOutput, Option.some.injEq]
    rw [hsize]
    simpa [Cslib.URM.Regs.output] using hres

end Langlib.Computability.URMSubleq

namespace Langlib.Computability

open Langlib.Common

/-- The tag type naming subleq for the `ProgLang` class. -/
inductive SubleqLang : Type

instance : ProgLang SubleqLang where
  Prog := Langlib.Subleq.Prog
  parse := Langlib.Subleq.assemble
  run := Langlib.Subleq.evalProg

/-- **Subleq's trace semantics.** One instruction, two of whose forms do
I/O, so the record is short and the laws are proved from the same invariant
as whitespace's in `Langlib/Languages/Subleq/Trace.lean`.

With this and `TraceLang WhitespaceLang` in place, both backends the library
has proved answer-correct can now be *stated* behaviourally. Reading at end
of input consumes nothing and so records nothing, which is the honest
report: no byte crossed the boundary. -/
instance : TraceLang SubleqLang where
  trace := Langlib.Subleq.evalTrace
  trace_outputs := Langlib.Subleq.evalTrace_outputs
  trace_inputs := Langlib.Subleq.evalTrace_inputs

/-- **Subleq is Turing complete.**

The witness is the compiler `URMSubleq.compile`, which turns a URM program
and its input vector into a subleq memory image, and the simulation
`URMSubleq.simulation`. The compiled program ignores its input stream (the
input vector is compiled into the image), prints the URM's answer, the
contents of register 0, as that many copies of one byte, and halts by
jumping to a negative address.

The claim is exactly that every URM program which halts is simulated. It
says nothing about URM programs that diverge, since `simulates` constrains
halting runs only. The further step to "subleq computes every partial
computable function" is the classical equivalence of the unlimited register
machine with the other models (Shepherdson and Sturgis 1963; Cutland,
*Computability*, chapter 3), which is cited rather than proved here;
`computes_of_turingComplete` states in cslib's own vocabulary what does
follow. -/
def subleqComplete : TuringComplete SubleqLang where
  compile := URMSubleq.compile
  encodeInput := fun _ => Input.ofString ""
  decodeOutput := URMSubleq.decodeOutput
  simulates := fun P inputs result h =>
    URMSubleq.simulation P inputs result h (Input.ofString "")

end Langlib.Computability
