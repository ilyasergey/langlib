import Langlib.Common.Io
import Langlib.Languages.Brainloller.Parser
import Langlib.Languages.Brainfuck.Semantics

/-!
# Brainloller: semantics = decode, then brainfuck

Brainloller adds nothing to brainfuck's semantics: once the pixel walk
(`Parser.lean`) has recovered the command string, execution is exactly
our brainfuck reference evaluator, with all its conventions (8-bit
wrapping cells, unbounded tape to the right, error left of cell 0, EOF
configurable and `unchanged` by default). Vandevenne's page does not pin
those corners down beyond "wrapping bytes", so inheriting our documented
brainfuck choices is the honest option; see `docs/brainloller/spec.md`.
-/

namespace Langlib.Brainloller

open Langlib.Common

/-- Run a decoded image on the brainfuck core. -/
def evalImage (cfg : Langlib.Brainfuck.Config) (img : Image) (input : Input)
    (fuel : Nat) : Except String RunResult := do
  let prog ← decodeProg img
  return Langlib.Brainfuck.evalProg cfg prog input fuel

/-- Parse (a P3 PPM, as text) and run: the entry point used by the runner
and the tests. Binary P6 images cannot travel through a `String`; convert
them (`magick prog.png -compress none prog.ppm`) or use
`Image.parsePpm` + `evalImage` directly. -/
def run (cfg : Langlib.Brainfuck.Config := {}) (src : String)
    (input : Input) (fuel : Nat) : Except String RunResult := do
  let img ← Image.parsePpm src.toUTF8
  evalImage cfg img input fuel

end Langlib.Brainloller
