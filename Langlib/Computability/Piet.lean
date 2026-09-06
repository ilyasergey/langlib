import Langlib.Computability.Piet.Divergence

/-! # Piet: divergence-preserving Turing completeness

`Simulation` proves preservation of source answers and interpreter lawfulness;
`Divergence` proves exhaustion of every finite fuel on divergent source inputs.
This module assembles both into the public completeness witness.
-/

namespace Langlib.Computability

open Langlib.Common

set_option maxHeartbeats 1000000 in
/-- Piet is Turing complete, via the verified URM-to-image compiler. -/
def pietComplete : TuringComplete PietLang where
  compile := URMPiet.image
  encodeInput := fun _ => Langlib.Common.Input.ofString ""
  decodeOutput := URMPiet.decodeOutput
  simulates := fun P inputs result h => URMPiet.simulation P inputs result h
  preserves_divergence := URMPiet.preserves_divergence

end Langlib.Computability
