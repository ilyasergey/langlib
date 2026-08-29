/-!
# Befunge-93: the playfield

Befunge-93 (Chris Pressey, 1993) has no abstract syntax tree to speak of:
the program *is* an 80x25 grid of characters, walked by the program counter
in two dimensions and rewritten at runtime by the `p` command. What other
languages call an AST is here a mutable grid of integers.

Cells are `Int`, not bytes: the reference interpreter `bef.c` stores the
playfield in a C `char` array (so `p` truncates), but our stack is exact
integers and we keep `g`/`p` a lossless round trip. See
`docs/befunge93/spec.md`, decision 2.
-/

namespace Langlib.Befunge93

/-- Playfield width, in cells. Fixed by the language. -/
def width : Nat := 80

/-- Playfield height, in cells. Fixed by the language. -/
def height : Nat := 25

/-- The 80x25 playfield, stored row-major as a flat array of cell values.
Cell (x,y) holds the character code loaded from the source (space, 32, for
cells the source did not cover) or whatever `p` last stored there. -/
structure Playfield where
  cells : Array Int
deriving Repr, Inhabited

namespace Playfield

/-- The all-spaces playfield. -/
def empty : Playfield := ⟨Array.replicate (width * height) (32 : Int)⟩

/-- Read cell (x,y). Callers keep coordinates in bounds; out-of-bounds
handling for `g` lives in the semantics. -/
def get (p : Playfield) (x y : Nat) : Int :=
  p.cells[y * width + x]?.getD 32

/-- Write cell (x,y). -/
def set (p : Playfield) (x y : Nat) (v : Int) : Playfield :=
  ⟨p.cells.set! (y * width + x) v⟩

end Playfield

end Langlib.Befunge93
