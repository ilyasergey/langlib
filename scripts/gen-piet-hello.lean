/-
Generate `Langlib/Examples/Piet/hello.ppm`, the Hello, world! program on
the Piet spec page.

    lake env lean --run scripts/gen-piet-hello.lean

The program is built from `Langlib.Computability.URMPiet.linearGrid`, the
three-row corridor the straight-line compiler uses, so the layout comes
from tested code rather than from painting pixels by hand. Re-render the
figure afterwards with

    lake exe piet --svg docs/piet/img/hello.svg --scale 8 \
      Langlib/Examples/Piet/hello.ppm

This script imports `Langlib.Computability`, and so Mathlib. That is fine
for a generator run by hand; it is why the generated PPM is checked in
rather than built as part of `lake build`.
-/
import Langlib.Computability.Piet
import Langlib.Common.Image

open Langlib.Computability
open Langlib.Computability.URMPiet
open Langlib.Piet
open Langlib.Common

/-- Invert `colorOfRgb`: the RGB the spec assigns to each codel. -/
def rgbOfCodel : Codel → Rgb
  | .white => ⟨255, 255, 255⟩
  | .black => ⟨0, 0, 0⟩
  | .chromatic h l =>
    let chan : Nat → UInt8 := fun n => UInt8.ofNat n
    let (hi, mid) : Nat × Nat :=
      match l with
      | .light => (255, 192)
      | .normal => (255, 0)
      | .dark => (192, 0)
    match h with
    | .red     => ⟨chan hi,  chan mid, chan mid⟩
    | .yellow  => ⟨chan hi,  chan hi,  chan mid⟩
    | .green   => ⟨chan mid, chan hi,  chan mid⟩
    | .cyan    => ⟨chan mid, chan hi,  chan hi⟩
    | .blue    => ⟨chan mid, chan mid, chan hi⟩
    | .magenta => ⟨chan hi,  chan mid, chan hi⟩

def gridToImage (g : Grid) : Image :=
  { width := g.width, height := g.height, pixels := g.codels.map rgbOfCodel }

/-- Push `n` onto the stack. A literal costs a block of `n` codels, so for
anything big we build it as `a*a + d` with `a = sqrt n`, which is two small
blocks instead of one enormous one. -/
def pushValue (n : Nat) : List BlockCmd :=
  if n ≤ 12 then pushNat n
  else
    let a := Nat.sqrt n
    let d := n - a * a
    pushNat a ++ [op .dup, op .multiply] ++
      (if d = 0 then [] else pushNat d ++ [op .add])

/-- Emit `s`, keeping the character just printed on the stack and reaching
the next one by adding or subtracting the difference. `outChar` pops, so
each character is duplicated before it is printed. Cheaper than pushing
every code point from scratch, because the differences are small. -/
def codeFor (s : String) : List BlockCmd :=
  let step : (List BlockCmd × Option Nat) → Char → (List BlockCmd × Option Nat) :=
    fun (acc, prev) c =>
      let n := c.toNat
      let bring : List BlockCmd :=
        match prev with
        | none => pushValue n
        | some p =>
          if n == p then []
          else if p < n then pushValue (n - p) ++ [op .add]
          else pushValue (p - n) ++ [op .subtract]
      (acc ++ bring ++ [op .dup, op .outChar], some n)
  (s.toList.foldl step ([], none)).1 ++ [op .pop]

def main : IO Unit := do
  let msg := "Hello, world!"
  let code := codeFor msg
  let g := linearGrid code
  let img := gridToImage g
  IO.println s!"blocks: {code.length}, grid: {g.width}x{g.height}"
  IO.FS.writeFile "Langlib/Examples/Piet/hello.ppm" img.toPpm3
