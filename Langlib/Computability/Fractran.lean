import Langlib.Computability.Fractran.Divergence

/-! # Fractran: divergence-preserving Turing completeness

`Simulation` proves preservation of source answers and interpreter lawfulness;
`Divergence` proves exhaustion of every finite fuel on divergent source inputs.
This module assembles both into the public completeness witness.
-/

namespace Langlib.Computability

open Langlib.Common

/-- FRACTRAN is Turing complete via the verified URM compiler. -/
def fractranComplete : TuringComplete FractranLang where
  compile := URMFractran.compileProgram
  encodeInput := fun _ => Input.ofString ""
  decodeOutput := URMFractran.decodeOutput
  simulates := fun P inputs result h => URMFractran.simulation P inputs result h
  preserves_divergence := URMFractran.preserves_divergence

end Langlib.Computability
