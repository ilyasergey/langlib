import Langlib.Computability.Brainfuck.Divergence

/-! # Brainfuck: divergence-preserving Turing completeness

`Simulation` proves preservation of source answers and interpreter lawfulness;
`Divergence` proves exhaustion of every finite fuel on divergent source inputs.
This module assembles both into the public completeness witness.
-/

namespace Langlib.Computability

open Langlib.Common

/-- **Brainfuck is Turing complete.**

The witness uses paired unary tape columns and a structured counter-machine
dispatcher. The compiled program ignores its external input because the URM
input vector is embedded by the compiler. -/
def brainfuckComplete : TuringComplete BrainfuckLang where
  compile := URMBrainfuck.compile
  encodeInput := URMBrainfuck.encodeInput
  decodeOutput := URMBrainfuck.decodeOutput
  simulates := fun P inputs result h =>
    URMBrainfuck.simulation P inputs result h (URMBrainfuck.encodeInput inputs)
  preserves_divergence := fun P inputs hd fuel =>
    URMBrainfuck.preserves_divergence P inputs hd (Input.ofString "") fuel

end Langlib.Computability
