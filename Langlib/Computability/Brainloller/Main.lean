import Langlib.Computability.Brainloller.Divergence

/-! # Brainloller: divergence-preserving Turing completeness

`Simulation` proves preservation of source answers and interpreter lawfulness;
`Divergence` proves exhaustion of every finite fuel on divergent source inputs.
This module assembles both into the public completeness witness.
-/

namespace Langlib.Computability

open Langlib.Common

/-- **Brainloller is Turing complete.**

The witness is `brainfuckComplete`'s, unchanged: a decoded Brainloller
program is a `Langlib.Brainfuck.Prog` and it runs on the brainfuck
evaluator, so the compiler, the encodings and the simulation proof all
transfer definitionally. The Brainloller-specific content is the round
trip discussed in the module docstring.

The compiled program ignores its external input, because the URM input
vector is embedded by the compiler. -/
def brainlollerComplete : TuringComplete BrainlollerLang where
  compile := URMBrainfuck.compile
  decodeOutput := URMBrainfuck.decodeOutput
  simulates := fun P inputs result h =>
    URMBrainfuck.simulation P inputs result h Langlib.Common.Input.empty
  preserves_divergence := URMBrainloller.preserves_divergence

/-- The compiled URM program, painted and read back, is the program the
simulation theorem is about, provided the pixel walk recovers the painted
characters. That proviso is the one link carried by test rather than by
proof; see the module docstring. -/
theorem decode_compile (P : Cslib.URM.Program) (inputs : List Nat)
    {img : Langlib.Common.Image}
    (h : Langlib.Brainloller.decode img
      = .ok (BrainlollerSyntax.renderBf (brainlollerComplete.compile P inputs))) :
    Langlib.Brainloller.decodeProg img = .ok (brainlollerComplete.compile P inputs) :=
  BrainlollerSyntax.decodeProg_of_decode h

end Langlib.Computability
