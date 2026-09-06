import Langlib.Computability.Ski.Divergence

/-! # Ski: divergence-preserving Turing completeness

`Simulation` proves preservation of source answers and interpreter lawfulness;
`Divergence` proves exhaustion of every finite fuel on divergent source inputs.
This module assembles both into the public completeness witness.
-/

namespace Langlib.Computability

open Langlib.Common

/-- **SKI is Turing complete.**

The witness compiles a URM program into a single application: the structured
counter machine of `Langlib/Computability/Common/Counter.lean`, rendered in
combinators, applied to a register file of Scott numerals. The file carries
one cell more than the machine has registers, because SKI has no output
instruction and `counterProgram` reports its answer by emitting bytes; that
cell counts them.

The answer is a term rather than a stream. The compiled program ends by
printing `result` copies of `k` in front of an `i`, and `decodeOutput` counts
them.

Since the unlimited register machine computes every partial computable
function (Shepherdson and Sturgis 1963; Cutland, *Computability*, chapter 3),
so does the SKI calculus. -/
def skiComplete : TuringComplete SkiLang where
  compile := URMSki.compile
  decodeOutput := URMSki.decodeOutput
  simulates := fun P inputs result h =>
    URMSki.simulation P inputs result h Langlib.Common.Input.empty
  preserves_divergence := URMSki.preserves_divergence

end Langlib.Computability
