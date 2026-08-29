/-!
# Malbolge: the machine

Malbolge (Ben Olmstead, 1998) has no abstract syntax tree worth the name: a
program *is* its initial memory image. This module defines the machine-level
vocabulary shared by the loader and the evaluator: ten-trit words and their
two arithmetic operations (rotate right and the "crazy" operation), the
eight instructions and their position-dependent decoding, the post-execution
encryption table, and the loaded `Image`.

Everything here transcribes Olmstead's public-domain reference interpreter
(`malbolge.c`); see `docs/malbolge/spec.md` for the specification, the
tables, and the places where the printed spec and the interpreter disagree.
-/

namespace Langlib.Malbolge

/-- Memory size: `3^10 = 59049` words. Addresses and words share this range. -/
def memSize : Nat := 59049

/-- The largest word: `2222222222` in ternary. Also the value the input
instruction stores at end of input. -/
def maxWord : Nat := 59048

/-- The eight Malbolge instructions. A word `w` executed at address `p`
denotes the instruction with opcode `(w + p) % 94`; any opcode other than
these eight is a no-op at run time (but is rejected by the loader). The
letters in the doc comments are the instruction names used by Olmstead's
specification (via the `xlat1` table). -/
inductive Instr where
  /-- Opcode 4 (`i`): jump, `c := mem[d]`. -/
  | jmp
  /-- Opcode 5 (`<`): output `a mod 256` as one byte. (The printed spec
  swaps the meanings of `<` and `/`; the interpreter, followed here and by
  everyone else, makes `<` the output instruction.) -/
  | out
  /-- Opcode 23 (`/`): read one input byte into `a`; at end of input,
  `a := 59048`. -/
  | inp
  /-- Opcode 39 (`*`): ternary rotate right, `a := mem[d] := rotR mem[d]`. -/
  | rotr
  /-- Opcode 40 (`j`): load the data pointer, `d := mem[d]`. -/
  | movd
  /-- Opcode 62 (`p`): the crazy operation, `a := mem[d] := crz a mem[d]`. -/
  | crazy
  /-- Opcode 68 (`o`): no operation. -/
  | nop
  /-- Opcode 81 (`v`): halt. -/
  | halt
deriving Repr, BEq, DecidableEq, Inhabited

/-- Decode an opcode (already reduced mod 94) to an instruction, or `none`
if it is not one of the eight. The loader rejects `none`; the evaluator
treats it as `nop`. -/
def Instr.ofOpcode? : Nat → Option Instr
  | 4 => some .jmp
  | 5 => some .out
  | 23 => some .inp
  | 39 => some .rotr
  | 40 => some .movd
  | 62 => some .crazy
  | 68 => some .nop
  | 81 => some .halt
  | _ => none

/-- The instruction denoted by word `w` at address `p`: dispatch on
`(w + p) % 94`, defaulting to `nop`. Equivalent to the reference
interpreter's `xlat1[(w - 33 + p) % 94]` lookup (the table is that
dispatch, written out as a permutation of the 94 printable characters). -/
def decode (w p : Nat) : Instr :=
  (Instr.ofOpcode? ((w + p) % 94)).getD .nop

/-- Ternary rotate right by one trit: the least significant trit becomes
the most significant. `19683 = 3^9`. -/
def rotR (w : Nat) : Nat :=
  w / 3 + w % 3 * 19683

/-- One trit of the crazy operation, `crzTrit a d` with the row picked by
the trit of `mem[d]` and the column by the trit of `a` ("don't look for a
pattern, it's not there" -- Olmstead):

```
        | a: 0  1  2
  ------+-----------
  [d] 0 |    1  0  0
      1 |    1  0  2
      2 |    2  2  1
```
-/
def crzTrit (a d : Nat) : Nat :=
  match d, a with
  | 0, 0 => 1 | 0, 1 => 0 | 0, 2 => 0
  | 1, 0 => 1 | 1, 1 => 0 | 1, 2 => 2
  | 2, 0 => 2 | 2, 1 => 2 | 2, 2 => 1
  | _, _ => 0 -- unreachable: trits are 0..2

/-- The crazy operation: `crzTrit` applied tritwise across the ten trits of
`a` and `d`. This is the interpreter's `op()` (which tabulates the same
function two trits at a time); the loader also uses it to fill memory
beyond the program. -/
def crz (a d : Nat) : Nat :=
  go 10 a d
where
  go : Nat → Nat → Nat → Nat
    | 0, _, _ => 0
    | k + 1, a, d => crzTrit (a % 3) (d % 3) + 3 * go k (a / 3) (d / 3)

/-- The encryption table `xlat2`: after an instruction executes, the word
at `c` (a printable 33..126, or nothing happens) is replaced by
`xlat2[mem[c] - 33]`. As a string (Olmstead's `malbolge.c`):

```
5z]&gqtyfr$(we4{WP)H-Zn,[%\3dL+Q;>U!pJS72FhOA1C
B6v^=I_0/8|jsb9m<.TVac`uY*MK'X~xDl}REokN:#?G"i@
```

The definition spells out the character codes so that the sanity checks
below reduce in the kernel (strings do not). -/
def xlat2 : Array Nat := #[
  53, 122, 93, 38, 103, 113, 116, 121, 102, 114, 36, 40, 119, 101, 52, 123,
  87, 80, 41, 72, 45, 90, 110, 44, 91, 37, 92, 51, 100, 76, 43, 81,
  59, 62, 85, 33, 112, 74, 83, 55, 50, 70, 104, 79, 65, 49, 67, 66,
  54, 118, 94, 61, 73, 95, 48, 47, 56, 124, 106, 115, 98, 57, 109, 60,
  46, 84, 86, 97, 99, 96, 117, 89, 42, 77, 75, 39, 88, 126, 120, 68,
  108, 125, 82, 69, 111, 107, 78, 58, 35, 63, 71, 34, 105, 64]

/-- Post-execution encryption of the word at `c`: printable words are
translated through `xlat2`, anything else is left unchanged (the reference
interpreter indexes out of bounds there; see the spec page). -/
def encrypt (w : Nat) : Nat :=
  if 33 ≤ w && w ≤ 126 then xlat2[w - 33]! else w

/-- A loaded program: the initial 59049-word memory image produced by
`Langlib.Malbolge.load`. Every entry is a word `≤ maxWord`. -/
structure Image where
  mem : Array Nat
deriving Repr

-- Sanity checks, mirrored against Olmstead's interpreter.
example : xlat2.size = 94 := by decide
example : rotR 39 = 13 := by decide
example : crz 0 62 = 29555 := by decide
example : decode 39 0 = Instr.rotr := by decide
example : decode 81 0 = Instr.halt := by decide
example : encrypt 33 = 53 := by decide   -- '!' becomes '5'
example : encrypt 13 = 13 := by decide   -- out of range: unchanged

end Langlib.Malbolge
