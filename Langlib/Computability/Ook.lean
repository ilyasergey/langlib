import Langlib.Computability.Ook.Divergence

/-! # Ook: divergence-preserving Turing completeness

`Simulation` proves preservation of source answers and interpreter lawfulness;
`Divergence` proves exhaustion of every finite fuel on divergent source inputs.
This module assembles both into the public completeness witness.
-/

namespace Langlib.Computability

open Langlib.Common

/-- **Ook! is Turing complete.**

The witness is `brainfuckComplete`'s, unchanged: `Langlib.Ook.Prog` is
`Langlib.Brainfuck.Prog` and `Langlib.Ook.run` is the brainfuck
evaluator, so the compiler, the encodings and the simulation proof all
transfer definitionally. The Ook!-specific content is
`OokSyntax.parse_render`, which says the compiled program can be
written down as Ook! text and read back unchanged.

The compiled program ignores its external input, because the URM input
vector is embedded by the compiler. -/
def ookComplete : TuringComplete OokLang where
  compile := URMBrainfuck.compile
  encodeInput := URMBrainfuck.encodeInput
  decodeOutput := URMBrainfuck.decodeOutput
  simulates := fun P inputs result h =>
    URMBrainfuck.simulation P inputs result h (URMBrainfuck.encodeInput inputs)
  preserves_divergence := URMOok.preserves_divergence

/-- The compiled URM program, written as Ook! source, parses back to the
program the simulation theorem is about. This is `parse_render`
instantiated at the compiler's output; it is what makes `ookComplete` a
claim about the *language* rather than about a shared syntax tree. -/
theorem parse_render_compile (P : Cslib.URM.Program) (inputs : List Nat) :
    Langlib.Ook.parse (Langlib.Ook.render (ookComplete.compile P inputs))
      = .ok (ookComplete.compile P inputs) :=
  OokSyntax.parse_render _

end Langlib.Computability
