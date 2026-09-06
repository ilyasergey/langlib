import Langlib.Languages.JavaGen.Sweep
import Langlib.Languages.JavaGen

/-! Compatibility names for the shared, Mathlib-free executable sweeper.
The simulation proofs remain in this computability folder. -/

namespace Langlib.Computability.JavaGen.Sweep
export Langlib.JavaGen.Sweep
  (Machine Config advance stateName letterName turnName pad pad_append tape query
   readBase endBase stateDecl turnBases declarations programAt program compile)
end Langlib.Computability.JavaGen.Sweep
