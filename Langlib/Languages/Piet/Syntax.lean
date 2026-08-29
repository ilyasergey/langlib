import Langlib.Common.Image

/-!
# Piet: colours, codels, and the codel grid

Piet (David Morgan-Mar, ~2002) programs are bitmaps. The "abstract syntax"
of a Piet program is a grid of *codels*, each one of 20 colours: 18
chromatic colours arranged on a 6-hue x 3-lightness wheel, plus white and
black. Commands are not written down anywhere; they arise at run time from
the colour *difference* between adjacent colour blocks (see
`Semantics.lean` and `docs/piet/spec.md`).

This module defines the colour types, the wheel arithmetic, the
(hue step, lightness step) -> command table, and the codel grid.
-/

namespace Langlib.Piet

open Langlib.Common (Rgb)

/-- The six hues, in wheel order. Hue steps are counted cyclically in this
order (red -> yellow -> ... -> magenta -> red). -/
inductive Hue where
  | red | yellow | green | cyan | blue | magenta
deriving Repr, BEq, Inhabited

def Hue.toNat : Hue → Nat
  | .red => 0 | .yellow => 1 | .green => 2
  | .cyan => 3 | .blue => 4 | .magenta => 5

/-- The three lightness levels; steps cycle light -> normal -> dark ->
light. -/
inductive Lightness where
  | light | normal | dark
deriving Repr, BEq, Inhabited

def Lightness.toNat : Lightness → Nat
  | .light => 0 | .normal => 1 | .dark => 2

/-- One codel's colour: chromatic (a point on the wheel), white, or
black. -/
inductive Codel where
  | chromatic (hue : Hue) (lightness : Lightness)
  | white
  | black
deriving Repr, BEq, Inhabited

/-- Cyclic hue distance from `a` to `b` (0-5). -/
def hueSteps (a b : Hue) : Nat := (6 + b.toNat - a.toNat) % 6

/-- Cyclic lightness distance from `a` to `b` (0-2). -/
def lightSteps (a b : Lightness) : Nat := (3 + b.toNat - a.toNat) % 3

/-- The 17 Piet commands. -/
inductive Op where
  | push | pop
  | add | subtract | multiply | divide | mod
  | not | greater
  | pointer | switch
  | dup | roll
  | inNum | inChar | outNum | outChar
deriving Repr, BEq, Inhabited

/-- The command encoded by a transition of `dh` hue steps and `dl`
lightness steps between two chromatic blocks. `(0, 0)` would mean "same
colour", which cannot occur between distinct blocks; it maps to `none`. -/
def opFor (dh dl : Nat) : Option Op :=
  match dl % 3, dh % 6 with
  | 0, 1 => some .add      | 0, 2 => some .divide  | 0, 3 => some .greater
  | 0, 4 => some .dup      | 0, 5 => some .inChar
  | 1, 0 => some .push     | 1, 1 => some .subtract | 1, 2 => some .mod
  | 1, 3 => some .pointer  | 1, 4 => some .roll     | 1, 5 => some .outNum
  | 2, 0 => some .pop      | 2, 1 => some .multiply | 2, 2 => some .not
  | 2, 3 => some .switch   | 2, 4 => some .inNum    | 2, 5 => some .outChar
  | _, _ => none

/-- The 20 standard colours, by exact RGB value; anything else is `none`
(rejected or treated as white, per `ParseConfig`). Values are from the
specification: `FF`/`C0`/`00` channel combinations. -/
def colorOfRgb (c : Rgb) : Option Codel :=
  let entry (h : Hue) (l : Lightness) := some (Codel.chromatic h l)
  match c.r.toNat, c.g.toNat, c.b.toNat with
  | 0xFF, 0xC0, 0xC0 => entry .red .light
  | 0xFF, 0x00, 0x00 => entry .red .normal
  | 0xC0, 0x00, 0x00 => entry .red .dark
  | 0xFF, 0xFF, 0xC0 => entry .yellow .light
  | 0xFF, 0xFF, 0x00 => entry .yellow .normal
  | 0xC0, 0xC0, 0x00 => entry .yellow .dark
  | 0xC0, 0xFF, 0xC0 => entry .green .light
  | 0x00, 0xFF, 0x00 => entry .green .normal
  | 0x00, 0xC0, 0x00 => entry .green .dark
  | 0xC0, 0xFF, 0xFF => entry .cyan .light
  | 0x00, 0xFF, 0xFF => entry .cyan .normal
  | 0x00, 0xC0, 0xC0 => entry .cyan .dark
  | 0xC0, 0xC0, 0xFF => entry .blue .light
  | 0x00, 0x00, 0xFF => entry .blue .normal
  | 0x00, 0x00, 0xC0 => entry .blue .dark
  | 0xFF, 0xC0, 0xFF => entry .magenta .light
  | 0xFF, 0x00, 0xFF => entry .magenta .normal
  | 0xC0, 0x00, 0xC0 => entry .magenta .dark
  | 0xFF, 0xFF, 0xFF => some .white
  | 0x00, 0x00, 0x00 => some .black
  | _, _, _ => none

/-- The codel grid: the parsed form of a Piet program. `codels` is
row-major, of size `width * height`. -/
structure Grid where
  width : Nat
  height : Nat
  codels : Array Codel
deriving Repr, Inhabited

namespace Grid

/-- Codel at `(x, y)`. Everywhere outside the image behaves exactly like
black (the edges of the program are walls), so out-of-bounds is `black`. -/
def get (g : Grid) (x y : Nat) : Codel :=
  if x < g.width && y < g.height then
    g.codels[y * g.width + x]?.getD .black
  else
    .black

end Grid

end Langlib.Piet
