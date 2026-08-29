import Langlib.Common.Image

/-!
# Brainloller: pixel instructions

Brainloller (Lode Vandevenne, 2005) is brainfuck for people who think
source code should hang in a gallery: the eight brainfuck commands are
colours, one pixel each, plus two colours that rotate the instruction
pointer so programs can wrap into rectangles. Every other colour is a
comment. See `docs/brainloller/spec.md`.

This module defines the pixel-level instruction set and the exact colour
table; the walk over the image is in `Parser.lean` and execution reuses
the brainfuck core.
-/

namespace Langlib.Brainloller

open Langlib.Common (Rgb)

/-- One pixel's meaning: a brainfuck command (kept as its character), an
instruction-pointer rotation, or a no-op. -/
inductive Instr where
  /-- One of the eight brainfuck command characters. -/
  | cmd (c : Char)
  /-- Rotate the instruction pointer 90 degrees clockwise (cyan). -/
  | cw
  /-- Rotate the instruction pointer 90 degrees counterclockwise
  (dark cyan). -/
  | ccw
  /-- Any other colour: does nothing. -/
  | nop
deriving Repr, BEq, Inhabited

/-- The colour table, from Vandevenne's specification (exact values). -/
def instrOfRgb (px : Rgb) : Instr :=
  match px.r.toNat, px.g.toNat, px.b.toNat with
  | 255, 0, 0 => .cmd '>' -- red
  | 128, 0, 0 => .cmd '<' -- dark red
  | 0, 255, 0 => .cmd '+' -- green
  | 0, 128, 0 => .cmd '-' -- dark green
  | 0, 0, 255 => .cmd '.' -- blue
  | 0, 0, 128 => .cmd ',' -- dark blue
  | 255, 255, 0 => .cmd '[' -- yellow
  | 128, 128, 0 => .cmd ']' -- dark yellow
  | 0, 255, 255 => .cw -- cyan
  | 0, 128, 128 => .ccw -- dark cyan
  | _, _, _ => .nop

/-- The colour for a brainfuck command character (encoder direction);
`none` if `c` is not one of the eight commands. -/
def rgbOfCmd (c : Char) : Option Rgb :=
  match c with
  | '>' => some ⟨255, 0, 0⟩
  | '<' => some ⟨128, 0, 0⟩
  | '+' => some ⟨0, 255, 0⟩
  | '-' => some ⟨0, 128, 0⟩
  | '.' => some ⟨0, 0, 255⟩
  | ',' => some ⟨0, 0, 128⟩
  | '[' => some ⟨255, 255, 0⟩
  | ']' => some ⟨128, 128, 0⟩
  | _ => none

def cwRgb : Rgb := ⟨0, 255, 255⟩
def ccwRgb : Rgb := ⟨0, 128, 128⟩
/-- The padding colour our encoder uses for no-ops (any non-command
colour would do; black reads as "background"). -/
def nopRgb : Rgb := ⟨0, 0, 0⟩

/-- The instruction pointer's heading. It starts east (rightward). -/
inductive Dir where
  | east | south | west | north
deriving Repr, BEq, Inhabited

def Dir.cw : Dir → Dir
  | .east => .south | .south => .west | .west => .north | .north => .east

def Dir.ccw : Dir → Dir
  | .east => .north | .north => .west | .west => .south | .south => .east

end Langlib.Brainloller
