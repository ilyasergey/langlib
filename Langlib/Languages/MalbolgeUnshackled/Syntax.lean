import Std.Data.HashMap

/-!
# Malbolge Unshackled: the machine vocabulary

Malbolge Unshackled (Ørjan Johansen, 2007) is Malbolge with the memory
bound taken out. Everything that Malbolge does in ten trits, Unshackled
does in unboundedly many, which forces one design decision that this
module is mostly about: what a *value* is.

Padding with zeros is not available, because the crazy operation has
`crz 0 0 = 1`, so a zero-padded value is a different value. Johansen's
answer is to make the first trit repeat forever to the left, so a value is
a 3-adic integer whose trit sequence is eventually constant: `...01` and
`...001` are the same thing, and `crz ...01 ...01 = ...110`. Values whose
repeating trit is `0` are exactly the naturals, which is what I/O and
instruction decoding use.

We represent such a value as a repeating `lead` trit plus the finite list
of trits below it, least significant first, with the invariant that the
list does not end in another copy of `lead`. The length of that list is
then literally the *width* of the value in Johansen's sense: the number of
trits other than the initial repeating ones.

This module defines trits, values and their normalisation, the two
arithmetic operations (the crazy operation and a rotation of variable
width), the successor function that plays the part of Malbolge's `+1 mod
59049` on both pointers, the mod-94 rule for values that are not naturals,
the eight instructions, and the encryption table.

Everything here follows Johansen's public-domain Haskell interpreter
(`Unshackled.hs`); see `docs/malbolge-unshackled/spec.md` for the
specification, the differences from Malbolge, and the points the language
leaves implementation-dependent.
-/

namespace Langlib.MalbolgeUnshackled

/-! ## Trits -/

/-- A ternary digit. -/
inductive Trit where
  | t0 | t1 | t2
deriving Repr, DecidableEq, Inhabited

instance : BEq Trit := ⟨fun a b => decide (a = b)⟩

def Trit.toNat : Trit → Nat
  | .t0 => 0 | .t1 => 1 | .t2 => 2

/-- `n % 3` as a trit. -/
def Trit.ofResidue (n : Nat) : Trit :=
  match n % 3 with
  | 0 => .t0
  | 1 => .t1
  | _ => .t2

def Trit.toChar : Trit → Char
  | .t0 => '0' | .t1 => '1' | .t2 => '2'

/-- One trit of the crazy operation, with the row picked by the trit of the
second operand (`mem[d]`) and the column by the trit of the first (`a`).
Identical to Malbolge's table; Olmstead's advice about it ("don't look for
a pattern, it's not there") is unchanged by the extra trits.

```
        | a: 0  1  2
  ------+-----------
  [d] 0 |    1  0  0
      1 |    1  0  2
      2 |    2  2  1
```
-/
def crzTrit : Trit → Trit → Trit
  | .t0, .t0 => .t1 | .t1, .t0 => .t0 | .t2, .t0 => .t0
  | .t0, .t1 => .t1 | .t1, .t1 => .t0 | .t2, .t1 => .t2
  | .t0, .t2 => .t2 | .t1, .t2 => .t2 | .t2, .t2 => .t1

/-! ## Values -/

/-- The last element of a list, if any. Used to state the normalisation
invariant on `Value`; defined here rather than reused from `List.getLast?`
so that the invariant proof below is self-contained. -/
def lastTrit? : List Trit → Option Trit
  | [] => none
  | [t] => some t
  | _ :: ts => lastTrit? ts

/-- Drop trailing copies of `t` from a list of trits (trailing = at the
most significant end, since lists are least-significant-first). -/
def stripLead (t : Trit) : List Trit → List Trit
  | [] => []
  | x :: xs =>
    match stripLead t xs with
    | [] => if x = t then [] else [x]
    | ys => x :: ys

/-- A Malbolge Unshackled value: a 3-adic integer whose trits are
eventually constant.

* `lead` is the trit that repeats indefinitely to the left;
* `low` is the finite list of trits below the repeating ones, least
  significant first.

The intended invariant is `Normalized`: `low` does not end in another copy
of `lead`, which makes the representation unique and makes `width` correct
by construction. Build values with `Value.mk'` (or the derived operations),
never with the raw constructor, unless you know the list is normalised. -/
structure Value where
  lead : Trit
  low : List Trit
deriving Repr, DecidableEq, Inhabited

instance : BEq Value := ⟨fun a b => decide (a = b)⟩

instance : Hashable Value where
  hash v := v.low.foldl (fun h t => mixHash h (hash t.toNat)) (hash v.lead.toNat)

namespace Value

/-- The normalisation invariant: the explicit trits do not end in another
copy of the repeating trit. Under it, structural equality of `Value`s is
equality of 3-adic integers. -/
def Normalized (v : Value) : Prop := lastTrit? v.low ≠ some v.lead

/-- Build a normalised value from a repeating trit and a raw trit list. -/
def mk' (lead : Trit) (low : List Trit) : Value := ⟨lead, stripLead lead low⟩

/-- `stripLead` really strips: the result never ends in `t`. -/
theorem lastTrit?_stripLead (t : Trit) (l : List Trit) :
    lastTrit? (stripLead t l) ≠ some t := by
  induction l with
  | nil => simp [stripLead, lastTrit?]
  | cons x xs ih =>
    show lastTrit? (match stripLead t xs with
      | [] => if x = t then [] else [x]
      | ys => x :: ys) ≠ some t
    cases h : stripLead t xs with
    | nil =>
      by_cases hx : x = t
      · simp [hx, lastTrit?]
      · simp [hx, lastTrit?]
    | cons y ys =>
      rw [h] at ih
      simpa [lastTrit?] using ih

/-- Hence `mk'` always produces a normalised value: the invariant the rest
of the interpreter relies on. -/
theorem normalized_mk' (lead : Trit) (low : List Trit) :
    (mk' lead low).Normalized :=
  lastTrit?_stripLead lead low

/-- The width of a value: the number of trits other than the initial
repeating ones (Johansen's definition, verbatim). -/
def width (v : Value) : Nat := v.low.length

/-- The trit at position `i` (position 0 is least significant). -/
def trit (v : Value) (i : Nat) : Trit := v.low.getD i v.lead

/-- Zero: `...000`. -/
def zero : Value := ⟨.t0, []⟩

/-- End of file, `...22`. Reserved by the language for exactly this. -/
def eof : Value := ⟨.t2, []⟩

/-- The end-of-line character, `...21`. -/
def eol : Value := ⟨.t2, [.t1]⟩

instance : Inhabited Value := ⟨zero⟩

/-- Base-3 digits of a natural, least significant first, no leading zeros.
The first argument is fuel; `natTrits` supplies enough of it. -/
def natTritsAux : Nat → Nat → List Trit
  | 0, _ => []
  | _ + 1, 0 => []
  | f + 1, n + 1 => Trit.ofResidue ((n + 1) % 3) :: natTritsAux f ((n + 1) / 3)

def natTrits (n : Nat) : List Trit := natTritsAux n n

/-- A natural number as a value: repeating trit `0`, ordinary base-3 digits
below it. -/
def ofNat (n : Nat) : Value := ⟨.t0, natTrits n⟩

/-- A character as a value: its Unicode code point. Unshackled reads and
writes Unicode, not bytes, so this is the I/O encoding as well as the
loader's. -/
def ofChar (c : Char) : Value := ofNat c.toNat

/-- The natural number a value denotes, or `none` if its repeating trit is
not `0` (in which case it denotes no natural: `...222` is the 3-adic `-1`).
Instruction decoding and I/O both go through this. -/
def toNat? (v : Value) : Option Nat :=
  if v.lead = .t0 then some (v.low.foldr (fun t acc => acc * 3 + t.toNat) 0)
  else none

/-- Naturals print as decimal; anything else prints as `...`, the repeating
trit, then the explicit trits most significant first, which is how the
language names its two reserved values (`...22` for end of file, `...21`
for end of line). A width-zero value gets a second copy of the repeating
trit so that the repetition is visible at all. Note that the wiki writes
the same values with more copies of the repeating trit where it likes
(`...1102` for what we print as `...102`); they denote the same 3-adic
integer. -/
def toString (v : Value) : String :=
  match v.toNat? with
  | some n => ToString.toString n
  | none =>
    let repeats := if v.low.isEmpty then [v.lead.toChar, v.lead.toChar]
                   else [v.lead.toChar]
    "..." ++ String.ofList (repeats ++ v.low.reverse.map Trit.toChar)

instance : ToString Value := ⟨toString⟩

/-! ### Arithmetic -/

/-- Pad a trit list up to length `n` with copies of the repeating trit. -/
def padTo (n : Nat) (t : Trit) (l : List Trit) : List Trit :=
  l ++ List.replicate (n - l.length) t

/-- The crazy operation, applied tritwise to two 3-adic values. The
repeating trits combine to give the result's repeating trit, and each
operand is padded with its own repeating trit up to the wider of the two
widths. -/
def crz (a b : Value) : Value :=
  let n := max a.low.length b.low.length
  mk' (crzTrit a.lead b.lead)
    ((padTo n a.lead a.low).zipWith crzTrit (padTo n b.lead b.low))

/-- Rotate right by one trit *within a window of `w` trits*: trits 0..w-1
rotate right (trit 0 moves up to position w-1), everything above position
w-1 stays put. With `w = 10` and a value below 59049 this is exactly
Malbolge's `rotR`. `w = 0` is not reachable (the rotation width starts at
10 and never shrinks) and is treated as the identity. -/
def rot (w : Nat) (v : Value) : Value :=
  match (List.range w).map v.trit with
  | [] => v
  | x :: xs => mk' v.lead (xs ++ [x] ++ v.low.drop w)

/-- Successor of a trit list under a repeating trit: returns the new
repeating trit and the new (not yet normalised) list. Carrying past the end
of the explicit trits is where the repeating trit can change: `...222 + 1`
is `...000`. -/
def succTrits (lead : Trit) : List Trit → Trit × List Trit
  | [] =>
    match lead with
    | .t0 => (.t0, [.t1])
    | .t1 => (.t1, [.t2])
    | .t2 => (.t0, [])
  | .t0 :: rest => (lead, .t1 :: rest)
  | .t1 :: rest => (lead, .t2 :: rest)
  | .t2 :: rest =>
    let (lead', rest') := succTrits lead rest
    (lead', .t0 :: rest')

/-- Add one. This is what Malbolge's `c := (c+1) mod 59049` becomes when
there is no modulus: plain 3-adic increment, which walks the whole of
memory (`...222` wraps to `...000`, and every other address has a distinct
successor). -/
def succ (v : Value) : Value :=
  let (lead, low) := succTrits v.lead v.low
  mk' lead low

/-! ### Remainders

Instruction decoding needs `(value + address) mod 94`, and memory
initialisation needs the address mod 6, but an address need not be a
natural number, and no *additive* remainder function on the 3-adics can
agree with the naturals (see the spec page for Johansen's proof, which is
two lines). Unshackled therefore fixes remainders by decree: `...111` and
`...222` are given the remainders of the 10-trit values `1111111111` and
`2222222222`, and every other value is an offset from whichever of `...0`,
`...1`, `...2` it starts with.

We track both remainders at once, modulo `lcm 6 94 = 282`. -/

/-- `lcm 6 94`: memory initialisation is 6-periodic, instruction decoding
is 94-periodic, and one residue modulo 282 determines both. -/
def fullMod : Nat := 282

/-- The residue decreed for the all-`t` value: `t * 1111111111₃`, reduced.
`(3^10 - 1) / 2 = 29524 = 1111111111₃`. -/
def leadModClass (t : Trit) : Nat := t.toNat * ((3 ^ 10 - 1) / 2) % fullMod

/-- The correction that makes "shift left, add a trit" have the all-`t`
residue as a fixed point, so that prepending another copy of the repeating
trit changes nothing. -/
def leadModAdjust (t : Trit) : Nat :=
  (fullMod + leadModClass t - (leadModClass t * 3 + t.toNat) % fullMod) % fullMod

/-- The residue of a value modulo 282, hence modulo 94 and modulo 6: start
from the decreed residue of the repeating trit and shift in the explicit
trits from the most significant end. -/
def modClass (v : Value) : Nat :=
  v.low.foldr
    (fun t mc => (mc * 3 + t.toNat + leadModAdjust v.lead) % fullMod)
    (leadModClass v.lead)

/-- The residue used for instruction decoding. -/
def mod94 (v : Value) : Nat := v.modClass % 94

/-- The residue used for memory initialisation. -/
def mod6 (v : Value) : Nat := v.modClass % 6

end Value

/-! ## Instructions -/

/-- The eight Malbolge instructions, plus the two ways a word can fail to
be one. A word `w` executed at address `p` denotes the instruction with
opcode `(w + p) mod 94`, where `w` must be a natural in 33..126 and `p`'s
residue comes from `Value.modClass`. -/
inductive Instr where
  /-- The word at `c` is not a printable natural: the reference
  interpreter hangs (Johansen's `hang`, an infinite loop), just as
  Malbolge's does. -/
  | outOfBounds
  /-- Opcode 4 (`i`): jump, `c := mem[d]`. -/
  | jmp
  /-- Opcode 5 (`<`): output the character `a` denotes. -/
  | out
  /-- Opcode 23 (`/`): read one character into `a`. -/
  | inp
  /-- Opcode 39 (`*`): rotate `mem[d]` right within the current rotation
  width, into both `mem[d]` and `a`. -/
  | rotr
  /-- Opcode 40 (`j`): load the data pointer, `d := mem[d]`. The only
  instruction that can change the rotation width. -/
  | movd
  /-- Opcode 62 (`p`): the crazy operation, `a := mem[d] := crz a mem[d]`. -/
  | crazy
  /-- Opcode 68 (`o`), and every opcode outside the eight: no operation. -/
  | nop
  /-- Opcode 81 (`v`): halt. -/
  | halt
deriving Repr, DecidableEq, Inhabited

instance : BEq Instr := ⟨fun a b => decide (a = b)⟩

/-- Decode an opcode (already reduced mod 94); `none` is a no-op at run
time and a load error at load time. -/
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

/-- A word's printable code, if it has one: values whose repeating trit is
not `0` have none, and neither do naturals outside 33..126. -/
def printableCode? (w : Value) : Option Nat :=
  match w.toNat? with
  | some n => if 33 ≤ n && n ≤ 126 then some n else none
  | none => none

/-- The instruction denoted by word `w` at an address with residue `m`. -/
def decode (w : Value) (m : Nat) : Instr :=
  match printableCode? w with
  | none => .outOfBounds
  | some n => (Instr.ofOpcode? ((n + m) % 94)).getD .nop

/-- The encryption table `xlat2`, unchanged from Malbolge: after an
instruction executes, the word at `c` is replaced by
`xlat2[mem[c] - 33]`.

```
5z]&gqtyfr$(we4{WP)H-Zn,[%\3dL+Q;>U!pJS72FhOA1C
B6v^=I_0/8|jsb9m<.TVac`uY*MK'X~xDl}REokN:#?G"i@
```
-/
def xlat2 : Array Nat := #[
  53, 122, 93, 38, 103, 113, 116, 121, 102, 114, 36, 40, 119, 101, 52, 123,
  87, 80, 41, 72, 45, 90, 110, 44, 91, 37, 92, 51, 100, 76, 43, 81,
  59, 62, 85, 33, 112, 74, 83, 55, 50, 70, 104, 79, 65, 49, 67, 66,
  54, 118, 94, 61, 73, 95, 48, 47, 56, 124, 106, 115, 98, 57, 109, 60,
  46, 84, 86, 97, 99, 96, 117, 89, 42, 77, 75, 39, 88, 126, 120, 68,
  108, 125, 82, 69, 111, 107, 78, 58, 35, 63, 71, 34, 105, 64]

/-- Post-execution encryption of a printable code. -/
def encrypt (n : Nat) : Nat := xlat2[n - 33]!

/-! ## Memory

Memory is the whole of the 3-adic integers, so it cannot be an array.
Johansen's interpreter builds a lazy infinite trie; we keep the finitely
many cells the program has touched, and compute the rest on demand. That
works because every untouched cell's contents depend only on its residue
mod 6: the memory-filling iteration of Malbolge is 6-periodic, and
Unshackled extends it to the addresses no iteration from 0 can reach by
saying that the value at an address is the one its residue mod 6 selects.
`rest` is that six-element table, computed by the loader from the last two
characters of the program. -/
structure Memory where
  /-- Cells written by the loader or by the program. -/
  cells : Std.HashMap Value Value
  /-- The initial contents of every other cell, indexed by residue mod 6. -/
  rest : Array Value
deriving Inhabited

namespace Memory

def get (m : Memory) (addr : Value) : Value :=
  m.cells.getD addr (m.rest.getD (addr.mod6) Value.zero)

def set (m : Memory) (addr v : Value) : Memory :=
  { m with cells := m.cells.insert addr v }

end Memory

/-- A loaded program: the initial memory image. -/
structure Image where
  mem : Memory
  /-- Number of non-whitespace characters in the source, for diagnostics. -/
  length : Nat
deriving Inhabited

/-! ## Sanity checks

Each of these is a fact the spec page states, checked in the kernel. -/

-- Values beginning with 0 are the naturals, and `width` counts the rest.
example : Value.ofNat 0 = ⟨.t0, []⟩ := by decide
example : Value.ofNat 5 = ⟨.t0, [.t2, .t1]⟩ := by decide
example : (Value.ofNat 5).width = 2 := by decide
example : (Value.ofNat 59048).width = 10 := by decide
example : Value.eof.width = 0 := by decide
example : Value.eol.width = 1 := by decide

-- Normalisation: `...0001` and `...01` are one value.
example : Value.mk' .t0 [.t1, .t0, .t0] = Value.ofNat 1 := by decide
example : (Value.ofNat 1).toString = "1" := by decide
example : Value.eof.toString = "...22" := by decide
example : Value.eol.toString = "...21" := by decide
-- the wiki's `...1102`, printed with one copy of the repeating trit
example : (Value.mk' .t1 [.t2, .t0]).toString = "...102" := by decide

-- The wiki's own example of the crazy operation on 3-adic values.
example : Value.crz (Value.ofNat 1) (Value.ofNat 1) = Value.mk' .t1 [.t0] := by decide
-- Malbolge computes `crz 0 62 = 29555 = 1111112122₃`. Unshackled agrees on
-- every trit, but does not stop at ten: the leading zeros of both operands
-- combine to a leading run of ones, so the result is `...1112122`, which is
-- not a natural number at all.
example : Value.crz (Value.ofNat 0) (Value.ofNat 62)
    = Value.mk' .t1 [.t2, .t2, .t1, .t2] := by decide
example : (List.range 10).map (Value.crz (Value.ofNat 0) (Value.ofNat 62)).trit
    = (List.range 10).map (Value.ofNat 29555).trit := by decide
example : (Value.crz (Value.ofNat 0) (Value.ofNat 62)).toNat? = none := by decide

-- Rotation of width 10 agrees with Malbolge's `rotR`.
example : Value.rot 10 (Value.ofNat 39) = Value.ofNat 13 := by decide
-- Rotation of an all-`t` value is that value again.
example : Value.rot 10 Value.eof = Value.eof := by decide

-- The successor function walks memory, wrapping `...222` to `...000`.
example : (Value.ofNat 2).succ = Value.ofNat 3 := by decide
example : Value.eof.succ = Value.zero := by decide
example : Value.eol.succ = Value.eof := by decide
example : (Value.mk' .t1 []).succ = Value.mk' .t1 [.t2] := by decide

-- The decreed residues, and the wiki's worked example.
example : Value.leadModClass .t1 = 196 := by decide
example : Value.leadModClass .t2 = 110 := by decide
example : Value.leadModAdjust .t1 = 171 := by decide
example : (Value.mk' .t1 []).mod94 = 29524 % 94 := by decide
example : (Value.mk' .t2 []).mod94 = 59048 % 94 := by decide
example : (Value.mk' .t1 [.t2, .t0]).mod94 = 6 := by decide
example : (Value.ofNat 1000).mod94 = 1000 % 94 := by decide

-- Instruction decoding and encryption, unchanged from Malbolge.
example : xlat2.size = 94 := by decide
example : decode (Value.ofNat 39) 0 = Instr.rotr := by decide
example : decode (Value.ofNat 81) 0 = Instr.halt := by decide
example : decode Value.eof 0 = Instr.outOfBounds := by decide
example : decode (Value.ofNat 13) 0 = Instr.outOfBounds := by decide
example : encrypt 33 = 53 := by decide

end Langlib.MalbolgeUnshackled
