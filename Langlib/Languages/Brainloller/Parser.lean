import Langlib.Common.Image
import Langlib.Languages.Brainloller.Syntax
import Langlib.Languages.Brainfuck.Syntax
import Langlib.Languages.Brainfuck.Parser

/-!
# Brainloller: decoder and encoder

**Decoding** walks the instruction pointer over the image: it starts at
the top-left pixel heading east, collects brainfuck command characters,
turns on cyan (clockwise) and dark cyan (counterclockwise), ignores every
other colour, and stops when it walks off the image. The collected string
is then parsed by the brainfuck parser (so bracket errors are that
parser's). A walk that never leaves the image (a rotation cycle) is
reported as a parse error: the pointer's state is (pixel, heading), so
any walk longer than `4 * width * height` steps has repeated a state and
will never terminate.

**Encoding** lays a brainfuck program out as an image: left to right on
the first row, then wrapped into a serpentine using the rotation colours
(two clockwise turns at the right edge going down, two counterclockwise
turns at the left edge), padding with black no-ops. Decoding an encoded
image gives back exactly the command characters, which the round-trip
tests pin down.
-/

namespace Langlib.Brainloller

open Langlib.Common

private def stepIp (img : Image) (p : Nat × Nat) : Dir → Option (Nat × Nat)
  | .east => if p.1 + 1 < img.width then some (p.1 + 1, p.2) else none
  | .south => if p.2 + 1 < img.height then some (p.1, p.2 + 1) else none
  | .west => if p.1 > 0 then some (p.1 - 1, p.2) else none
  | .north => if p.2 > 0 then some (p.1, p.2 - 1) else none

private def walk (img : Image) : Nat → (Nat × Nat) → Dir → List Char →
    Except String (List Char)
  | 0, _, _, _ =>
    throw "the instruction pointer never leaves the image \
      (the rotation pixels form a loop)"
  | fuel + 1, p, d, acc => do
    let px := (img.get? p.1 p.2).getD default
    let (d, acc) :=
      match instrOfRgb px with
      | .cmd c => (d, c :: acc)
      | .cw => (d.cw, acc)
      | .ccw => (d.ccw, acc)
      | .nop => (d, acc)
    match stepIp img p d with
    | some q => walk img fuel q d acc
    | none => return acc.reverse

/-- Decode an image to brainfuck source (the eight command characters). -/
def decode (img : Image) : Except String String := do
  let cmds ← walk img (4 * img.width * img.height + 1) (0, 0) .east []
  return String.ofList cmds

/-- Decode an image all the way to a parsed brainfuck program. -/
def decodeProg (img : Image) : Except String Langlib.Brainfuck.Prog :=
  decode img >>= Langlib.Brainfuck.parse

/-- Keep only the eight brainfuck command characters of `src`. -/
def bfCommands (src : String) : List Char :=
  src.toList.filter fun c => (rgbOfCmd c).isSome

/-- Build one row of the serpentine layout and recurse on what is left.
`y` is the row index (even rows run east, odd rows west). The fuel is the
number of commands left plus one: every non-final row places at least one
command (`width ≥ 3`), so it always suffices. -/
private def buildRows (width : Nat) : Nat → List Char → Nat →
    List (Array Rgb)
  | 0, _, _ => []
  | fuel + 1, cmds, y =>
    let east := y % 2 == 0
    -- capacity if this is the last row / if we must wrap and turn
    let fullCap := if y == 0 then width else width - 1
    let isLast := cmds.length ≤ fullCap
    let cap := if isLast then fullCap
               else if y == 0 then width - 1 else width - 2
    let chunk := (cmds.take cap).filterMap rgbOfCmd
    let row := Id.run do
      let mut row := Array.replicate width nopRgb
      -- incoming turn pixel (the second of the pair placed by row y-1)
      if y > 0 then
        if east then row := row.set! 0 ccwRgb
        else row := row.set! (width - 1) cwRgb
      -- the commands
      let start := if y == 0 then 0 else 1
      for i in [0:chunk.length] do
        let col := if east then start + i else width - 2 - i
        row := row.set! col chunk[i]!
      -- outgoing turn pixel
      if !isLast then
        if east then row := row.set! (width - 1) cwRgb
        else row := row.set! 0 ccwRgb
      return row
    if isLast then [row]
    else row :: buildRows width fuel (cmds.drop cap) (y + 1)

/-- Encode brainfuck source as a Brainloller image. `rowWidth = 0` (the
default) lays everything on a single row; otherwise rows are `rowWidth`
pixels wide (at least 3, to leave room for the turning pixels) and wrap
in a serpentine. -/
def encode (src : String) (rowWidth : Nat := 0) : Image :=
  let cmds := bfCommands src
  let width := if rowWidth == 0 then max cmds.length 1 else max rowWidth 3
  let rows := buildRows width (cmds.length + 1) cmds 0
  { width
    height := rows.length
    pixels := rows.foldl (fun acc r => acc ++ r) #[] }

end Langlib.Brainloller
