import Langlib.Computability.Brainloller
import Langlib.Computability.Brainfuck.Divergence

/-! # Brainloller preserves URM divergence

The existing program representation and evaluator agree definitionally with
Brainfuck, so the established Brainfuck divergence proof applies directly.

This concerns the existing decoded-program interface; the separate pixel-walk
obligation is unchanged.
-/

namespace Langlib.Computability

open Langlib.Common

/-- The original Brainloller compiler, with divergence preservation. -/
def brainlollerDivergencePreserving : DivergencePreservingTC BrainlollerLang where
  toTuringComplete := brainlollerComplete
  preserves_divergence := brainfuckDivergencePreserving.preserves_divergence

end Langlib.Computability
