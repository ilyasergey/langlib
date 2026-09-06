import Langlib.Computability.Thue.Divergence

/-! # Thue: divergence-preserving Turing completeness

`Simulation` proves preservation of source answers and interpreter lawfulness;
`Divergence` proves exhaustion of every finite fuel on divergent source inputs.
This module assembles both into the public completeness witness.
-/

namespace Langlib.Computability

open Langlib.Common

/-- Thue is Turing complete, via the verified URM-to-Thue generator. -/
def thueComplete : TuringComplete ThueLang where
  compile := URMThue.compile
  decodeOutput := URMThue.decodeOutput
  simulates := fun P inputs result h => URMThue.simulation P inputs result h
  preserves_divergence := URMThue.preserves_divergence

end Langlib.Computability
