import Langlib.Computability.Whitespace.Divergence

/-! # Whitespace: divergence-preserving Turing completeness

`Simulation` proves preservation of source answers and interpreter lawfulness;
`Divergence` proves exhaustion of every finite fuel on divergent source inputs.
This module assembles both into the public completeness witness.
-/

namespace Langlib.Computability

open Langlib.Common

/-- **Whitespace is Turing complete.**

The witness is the compiler `URMWhitespace.compile`, which turns a URM
program and its input vector into a Whitespace program, and the simulation
`URMWhitespace.simulation`. The compiled program ignores its input stream
and prints the URM's answer, the contents of register 0, in decimal.

Since the unlimited register machine computes every partial computable
function (Shepherdson and Sturgis 1963; Cutland, *Computability*, chapter
3), so does Whitespace. -/
def whitespaceComplete : TuringComplete WhitespaceLang where
  compile := URMWhitespace.compile
  decodeOutput := URMWhitespace.decodeOutput
  simulates := fun P inputs result h =>
    URMWhitespace.simulation P inputs result h (Input.ofString "")
  preserves_divergence := fun P inputs hd fuel =>
    URMWhitespace.preserves_divergence P inputs hd (Input.ofString "") fuel

end Langlib.Computability
