import Langlib.Computability.Ook
import Langlib.Computability.Brainfuck.Divergence

/-! # Ook preserves URM divergence

The existing program representation and evaluator agree definitionally with
Brainfuck, so the established Brainfuck divergence proof applies directly.
-/

namespace Langlib.Computability

open Langlib.Common

/-- The original Ook compiler, with divergence preservation. -/
def ookDivergencePreserving : DivergencePreservingTC OokLang where
  toTuringComplete := ookComplete
  preserves_divergence := brainfuckDivergencePreserving.preserves_divergence

end Langlib.Computability
