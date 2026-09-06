import Langlib.Computability.Subleq.Divergence

/-! # Subleq: divergence-preserving Turing completeness

`Simulation` proves preservation of source answers and interpreter lawfulness;
`Divergence` proves exhaustion of every finite fuel on divergent source inputs.
This module assembles both into the public completeness witness.
-/

namespace Langlib.Computability

open Langlib.Common

/-- **Subleq is Turing complete.**

The witness is the compiler `URMSubleq.compile`, which turns a URM program
and its input vector into a subleq memory image, and the simulation
`URMSubleq.simulation`. The compiled program ignores its input stream (the
input vector is compiled into the image), prints the URM's answer, the
contents of register 0, as that many copies of one byte, and halts by
jumping to a negative address.

The witness preserves halting answers and, by
`URMSubleq.preserves_divergence`, exhausts every finite target fuel budget
on divergent URM inputs. The further step to "subleq computes every partial
computable function" is the classical equivalence of the unlimited register
machine with the other models (Shepherdson and Sturgis 1963; Cutland,
*Computability*, chapter 3), which is cited rather than proved here;
`computes_of_turingComplete` states in cslib's own vocabulary what does
follow. -/
def subleqComplete : TuringComplete SubleqLang where
  compile := URMSubleq.compile
  decodeOutput := URMSubleq.decodeOutput
  simulates := fun P inputs result h =>
    URMSubleq.simulation P inputs result h (Input.ofString "")
  preserves_divergence := fun P inputs hd fuel =>
    URMSubleq.preserves_divergence P inputs hd (Input.ofString "") fuel

end Langlib.Computability
