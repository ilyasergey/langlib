import Langlib.Turpentine.Compile.Brainfuck
import Langlib.Languages.Brainloller

/-!
# Turpentine to Brainloller

Brainloller is brainfuck painted one command to a pixel, with two extra
colours that turn the instruction pointer so a program can wrap into a
rectangle. `Langlib/Languages/Brainloller/` already has both directions,
`encode` and `decodeProg`, so this backend is the brainfuck backend
composed with `encode`.

The supported fragment, the tape layout and every trap are the brainfuck
backend's; see `docs/brainfuck/compiler.md`.

## The one decision: row width

`Langlib.Brainloller.encode` takes a row width. Width `0` means "one
row", which for a compiled Turpentine program gives an image tens of
thousands of pixels wide and one pixel tall: unreadable, and awkward for
image tooling. `defaultWidth` is **64**, which keeps the aspect ratio in
the range a viewer can display and keeps the P3 text file's lines short
enough to diff. It is a presentation choice only: the serpentine layout
decodes to the same command sequence at every width ≥ 3, and
`Langlib.Computability.Brainloller.decodeProg_encode_render` proves it.

A width `w ≥ 3` carries `w - 1` commands on the first row and `w - 2` on
every row after it, the missing pixels being the clockwise and
counterclockwise turns at the ends. So an `n`-command program needs about
`n / (w - 2) + 1` rows, and at `w = 64` a 20,000-command program is 64 by
323.

## Output format

`compileSource` emits ASCII PPM (`P3`), which is what
`Langlib.Brainloller.run` and `lake exe brainloller` read, and what
`Langlib.Common.Image.toPpm3` writes: one image row per line, so the
files diff sensibly. Converting to PNG is a job for `magick`.
-/

namespace Langlib.Turpentine.Compile.Brainloller

open Langlib.Turpentine
open Langlib.Common (Image)

/-- The default serpentine row width. See the module docstring: this is a
presentation choice, not a semantic one. -/
def defaultWidth : Nat := 64

/-- Compile a Turpentine program to a Brainloller image.

Brainloller has no abstract syntax of its own: a program *is* an image,
and decoding walks the instruction pointer over it to recover brainfuck.
So the target type here is `Langlib.Common.Image` rather than a `Prog`,
and the compiler is the brainfuck backend followed by
`Langlib.Brainloller.encode`. Errors are the brainfuck backend's. -/
def compile (p : Program) (width : Nat := defaultWidth) :
    Except String Image := do
  let bf ← Langlib.Turpentine.Compile.Brainfuck.compile p
  return Langlib.Brainloller.encode (Langlib.Brainfuck.Prog.render bf) width

/-- The compiled program as brainfuck, before it is painted. Useful for
sizing the image and for the tests, which check that the walk over the
image recovers exactly this. -/
def compileProg (p : Program) : Except String Langlib.Brainfuck.Prog :=
  Langlib.Turpentine.Compile.Brainfuck.compile p

/-- Turpentine source text to Brainloller source text: an ASCII PPM
(`P3`) image, which is what `lake exe brainloller` reads. -/
def compileSource (src : String) (width : Nat := defaultWidth) :
    Except String String := do
  let prog ← parse src
  let img ← compile prog width
  return img.toPpm3

/-- Compile and run, for the differential tests. The compiled image goes
back through the Brainloller front end (PPM text in, pixel walk, then the
brainfuck core), so a test's expected output is a claim about the
generated *image*, not only about the generated syntax tree.

The EOF convention is the one the generated code is written for
(`lake exe brainloller --eof zero`). -/
def runCompiled (src : String) (input : Langlib.Common.Input) (fuel : Nat) :
    Except String Langlib.Common.RunResult := do
  let text ← compileSource src
  Langlib.Brainloller.run { eof := .zero } text input fuel

end Langlib.Turpentine.Compile.Brainloller
