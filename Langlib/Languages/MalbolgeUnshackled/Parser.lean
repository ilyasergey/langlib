import Langlib.Languages.MalbolgeUnshackled.Syntax

/-!
# Malbolge Unshackled: the loader

Like Malbolge, Unshackled is loaded rather than parsed: the source
characters become the first cells of memory and the rest of memory is
generated from them. Two things change.

**There is no length limit.** Malbolge's loader rejects programs longer
than 59049 characters because that is all the memory there is. Unshackled
has all the memory there is, so the only length requirement is Johansen's
`checkProgLength`: at least two characters, because the fill needs two
seeds.

**The fill covers the whole of the 3-adic integers.** Malbolge's
`mem[i] = crz mem[i-1] mem[i-2]` iteration starts at the end of the program
and walks up through address 59048; it can never reach an address whose
leading trit is 1 or 2, and in Unshackled there are infinitely many of
those. Johansen's answer uses a fact about the iteration that Malbolge
never needed: it is 6-periodic. Every trit position runs the state machine
`(x, y) ↦ (y, crz y x)` on three trits, whose cycles all have length 1, 2
or 3 and whose transients are one step long, so from the third term onward
the sequence repeats with period 6. The contents of an untouched cell are
therefore a function of its address modulo 6 alone, and `Value.mod6`
extends "modulo 6" to every address. We store that six-element table in
`Memory.rest` and compute untouched cells on demand, rather than building
Johansen's lazy infinite trie.

Loader errors report the character's line and column in the source and the
address it was landing on.
-/

namespace Langlib.MalbolgeUnshackled

private structure Pos where
  line : Nat := 1
  col : Nat := 1

private def Pos.show (p : Pos) : String := s!"{p.line}:{p.col}"

private def Pos.advance (p : Pos) (c : Char) : Pos :=
  if c == '\n' then { line := p.line + 1, col := 1 }
  else { p with col := p.col + 1 }

/-- Whitespace skipped by the loader: the six ASCII characters that C's
`isspace` and Haskell's `Data.Char.isSpace` agree on. See decision 11 in
`docs/malbolge-unshackled/spec.md` for why we stop at ASCII. -/
def isSpaceChar (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\x0b' || c == '\x0c' || c == '\r'

/-- The memory-filling iteration: `s 0 = p`, `s 1 = q`,
`s (n+2) = crz (s (n+1)) (s n)`; the first `k` terms. -/
def crzSeq : Nat → Value → Value → List Value
  | 0, _, _ => []
  | k + 1, p, q => p :: crzSeq k q (Value.crz q p)

/-- The six-element table of untouched-cell contents, indexed by the
address's residue mod 6.

`p` and `q` are the values of the last two program characters and `m` is
the residue of the address `p` landed on, so Malbolge's iteration puts
`crzSeq`'s term `k` at the address with residue `m + k`. The sequence is
6-periodic from index 2, so the cell whose residue is `j` holds term
`j + off`, where `off` is the least index that is at least 2 and congruent
to `j - m` modulo 6 (as `j` ranges over 0..5, `j + off` ranges over six
consecutive terms). -/
def restTable (p q : Value) (m : Nat) : Array Value :=
  let off := 2 + (10 - m % 6) % 6
  let seq := crzSeq (off + 6) p q
  ⟨(List.range 6).map fun j => seq.getD (off + j) Value.zero⟩

/-- Load Malbolge Unshackled source text into an initial memory image.

`strict` corresponds to Johansen's `-n` flag: with it, a character whose
code is outside 33..126 is a load error; without it (the default, matching
the reference interpreter's default) such a character is stored in memory
unchecked, exactly as Malbolge's loader does by accident. Executing one is
a different matter: see `docs/malbolge-unshackled/spec.md`, decision 5.

Unlike Malbolge's loader, this one accepts source characters above code
point 255: Unshackled values are unbounded and its I/O is Unicode, so a
character's code point is a perfectly good cell value. -/
def loadWith (strict : Bool) (src : String) : Except String Image := do
  let mut cells : Std.HashMap Value Value := {}
  let mut pos : Pos := {}
  -- `addr` is the next address to store at; `lastAddr`/`lastVal` and
  -- `prevAddr`/`prevVal` trail it by one and two characters, so that after
  -- the loop `prev*` describes the second-to-last character, which is what
  -- the fill is seeded and phased from.
  let mut addr : Value := Value.zero
  let mut lastAddr : Value := Value.zero
  let mut prevAddr : Value := Value.zero
  let mut lastVal : Value := Value.zero
  let mut prevVal : Value := Value.zero
  let mut n : Nat := 0
  for ch in src.toList do
    if isSpaceChar ch then
      pos := pos.advance ch
      continue
    let v := Value.ofChar ch
    let m := addr.modClass
    match printableCode? v with
    | some code =>
      if (Instr.ofOpcode? ((code + m) % 94)).isNone then
        throw s!"illegal instruction '{ch}' at {pos.show}: (code {code} + \
                 address {addr}) mod 94 = {(code + m) % 94} is not a \
                 Malbolge Unshackled instruction"
    | none =>
      if strict then
        throw s!"character '{ch}' (code {ch.toNat}) at {pos.show} is not a \
                 printable instruction, and --strict rejects those"
    cells := cells.insert addr v
    prevAddr := lastAddr; prevVal := lastVal
    lastAddr := addr; lastVal := v
    addr := addr.succ
    n := n + 1
    pos := pos.advance ch
  if n < 2 then
    throw s!"program too short: {n} instruction(s); the memory fill needs at \
             least two seeds (Johansen's interpreter rejects these too)"
  return ⟨⟨cells, restTable prevVal lastVal prevAddr.modClass⟩, n⟩

/-- Load with the reference interpreter's default settings. -/
def load (src : String) : Except String Image := loadWith false src

end Langlib.MalbolgeUnshackled
