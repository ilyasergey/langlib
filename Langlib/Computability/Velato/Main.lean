import Langlib.Computability.Velato.Divergence

/-! # Velato: divergence-preserving Turing completeness

`Simulation` proves preservation of source answers and interpreter lawfulness;
`Divergence` proves exhaustion of every finite fuel on divergent source inputs.
This module assembles both into the public completeness witness.
-/

namespace Langlib.Computability

open Langlib.Common

/-- **Velato is Turing complete.**

The witness is `URMVelato.compile`, which turns a URM program and its input
vector into a Velato program, and the simulation `URMVelato.simulation`. The
compiled program ignores its input stream — the input vector is compiled
into the register-loading prologue — prints the URM's answer, the contents
of register 0, as that many copies of one byte, and halts.

What makes this backend different from every other one in the library is
where the state lives. Velato has at most 128 variables, one per MIDI note,
so the registers cannot be laid side by side; the compiled program uses a
*single* variable, middle C, holding the whole register file as
`2^w₀ · 3^w₁ · 5^w₂ · ⋯`. Increment multiplies by a prime, decrement
divides by it, and "is this register nonzero?" is "does this prime divide
the number?". `docs/velato/computability.md` gives the prose account.

The witness preserves halting answers and, by
`URMVelato.preserves_divergence`, exhausts every finite target fuel budget
on divergent URM inputs. The further step to "Velato computes every partial
computable function" is the classical equivalence of the unlimited register
machine with the other models (Shepherdson and Sturgis 1963), cited rather
than proved here; `computes_of_turingComplete` states in cslib's own
vocabulary what does follow.

It depends on Velato's integers being unbounded. Under the 2009 reference
compiler's 32-bit `int` the Gödel number overflows almost at once and the
language has a finite state space; `docs/velato/spec.md` argues why the
unbounded reading is the right one for a specification that names no
width. -/
def velatoComplete : TuringComplete VelatoLang where
  compile := URMVelato.compile
  decodeOutput := URMVelato.decodeOutput
  simulates := fun P inputs result h =>
    URMVelato.simulation P inputs result h (Input.ofString "")
  preserves_divergence := fun P inputs hd fuel =>
    URMVelato.preserves_divergence P inputs hd Langlib.Common.Input.empty fuel

end Langlib.Computability
