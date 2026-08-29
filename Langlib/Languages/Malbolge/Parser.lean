import Langlib.Languages.Malbolge.Syntax

/-!
# Malbolge: the loader

Malbolge is not parsed so much as *loaded*: the source characters become the
first words of memory, and the rest of memory is generated from them. This
module reproduces the loader of Olmstead's reference interpreter exactly,
including its famous oversight (non-printable characters are stored without
the instruction-validity check); see `docs/malbolge/spec.md`.

The loader:

1. skips ASCII whitespace (space, tab, LF, VT, FF, CR -- C's `isspace`);
2. for each remaining character at load address `i`: if it is printable
   (33..126), requires `(code + i) mod 94` to be one of the eight
   instruction opcodes, else rejects the file; a non-printable character is
   stored *unchecked* (the reference behaviour that Lou Scheffer's cat
   program relies on);
3. rejects files with more than 59049 instructions (checked after the
   validity check, as in the reference) and, unlike the reference -- which
   reads before the start of its own memory -- files with fewer than two;
4. fills the rest of memory with `mem[i] = crz mem[i-1] mem[i-2]`.

Errors report the character's line and column in the source file and its
load address in memory.
-/

namespace Langlib.Malbolge

private structure Pos where
  line : Nat := 1
  col : Nat := 1

private def Pos.show (p : Pos) : String := s!"{p.line}:{p.col}"

private def Pos.advance (p : Pos) (c : Char) : Pos :=
  if c == '\n' then { line := p.line + 1, col := 1 }
  else { p with col := p.col + 1 }

/-- The characters C's `isspace` accepts (default locale); the loader skips
exactly these. -/
private def isSpaceByte (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\x0b' || c == '\x0c' || c == '\r'

/-- Load Malbolge source text into an initial memory `Image`.

The reference interpreter reads raw bytes; our runner reads the file as
UTF-8 text, so source characters above code point 255 are rejected (they
could never reach the reference interpreter as a single byte). -/
def load (src : String) : Except String Image := do
  let mut cells : Array Nat := Array.mkEmpty memSize
  let mut pos : Pos := {}
  for ch in src.toList do
    if isSpaceByte ch then
      pos := pos.advance ch
      continue
    let x := ch.toNat
    if x > 255 then
      throw s!"character '{ch}' at {pos.show} is outside the byte range 0..255"
    let i := cells.size
    if 33 ≤ x && x ≤ 126 then
      if (Instr.ofOpcode? ((x + i) % 94)).isNone then
        throw s!"invalid character '{ch}' at {pos.show}: (code {x} + address {i}) \
                 mod 94 = {(x + i) % 94} is not a Malbolge instruction"
    if i == memSize then
      throw s!"program too long: at {pos.show}, memory holds only {memSize} words"
    cells := cells.push x
    pos := pos.advance ch
  if cells.size < 2 then
    throw s!"program too short: {cells.size} instruction(s); the memory fill \
             needs at least two (the reference interpreter reads out of bounds here)"
  let n := cells.size
  for _ in [n : memSize] do
    cells := cells.push (crz cells[cells.size - 1]! cells[cells.size - 2]!)
  return ⟨cells⟩

end Langlib.Malbolge
