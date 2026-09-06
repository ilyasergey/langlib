import Langlib.Computability.Unlambda.Divergence

/-! # Unlambda: divergence-preserving Turing completeness

`Simulation` proves preservation of source answers and interpreter lawfulness;
`Divergence` proves exhaustion of every finite fuel on divergent source inputs.
This module assembles both into the public completeness witness.
-/

namespace Langlib.Computability

open Langlib.Common

/-- **Unlambda is Turing complete.**

The witness compiles a URM program into a single application: the structured
counter machine of `Langlib/Computability/Counter.lean`, rendered in
combinators, applied to a register file of Scott numerals. Registers are a
Scott list, the loop is a call-by-value fixed point, and the answer comes back
in unary, one `*` per unit of register 0.

The fragment used is `s`, `k`, `i`, `.x` and application. Unlambda's
distinctive builtins play no part: `d` never appears, so the delay rule never
fires; `c` never appears, so no continuation is reified; and nothing reads the
input stream.

Since the unlimited register machine computes every partial computable
function (Shepherdson and Sturgis 1963; Cutland, *Computability*, chapter 3),
so does Unlambda. -/
def unlambdaComplete : TuringComplete UnlambdaLang where
  compile := URMUnlambda.compile
  encodeInput := URMUnlambda.encodeInput
  decodeOutput := URMUnlambda.decodeOutput
  simulates := fun P inputs result h =>
    URMUnlambda.simulation P inputs result h (URMUnlambda.encodeInput inputs)
  preserves_divergence := fun P inputs hd fuel =>
    URMUnlambda.preserves_divergence P inputs hd (URMUnlambda.encodeInput inputs) fuel

end Langlib.Computability
