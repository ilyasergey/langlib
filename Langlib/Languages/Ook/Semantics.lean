import Langlib.Languages.Brainfuck.Semantics
import Langlib.Languages.Ook.Parser

/-!
# Ook!: reference semantics

There is nothing here to define: an Ook! program *is* a brainfuck program in
different clothing, so evaluation is `Langlib.Brainfuck.evalProg`, and every
runtime semantic decision (8-bit wrapping cells, tape unbounded to the
right, moving left of cell 0 is an error, EOF conventions) is inherited from
`docs/brainfuck/spec.md`. Only the parser (and the banana) is Ook!'s own.
-/

namespace Langlib.Ook

open Langlib.Common

/-- Runtime configuration: the same EOF conventions as brainfuck. -/
abbrev Config := Langlib.Brainfuck.Config

/-- Parse and run: the entry point used by the runner and the tests.
Evaluation is exactly brainfuck's. -/
def run (cfg : Config := {}) (src : String) (input : Input) (fuel : Nat) :
    Except String RunResult := do
  let prog ← parse src
  return Langlib.Brainfuck.evalProg cfg prog input fuel

end Langlib.Ook
