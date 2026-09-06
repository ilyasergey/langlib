import Langlib.Computability.Brainloller.Simulation
import Langlib.Computability.Brainfuck.Divergence

/-! # Brainloller preserves URM divergence

The existing program representation and evaluator agree definitionally with
Brainfuck, so its divergence proof transfers to the same compiled programs.
This is the decoded-program interface; the pixel-walk obligation is separate.
-/

namespace Langlib.Computability.URMBrainloller

open Langlib.Common

/-- The shared Brainfuck execution exhausts every finite fuel on divergent input. -/
theorem preserves_divergence (P : Cslib.URM.Program) (inputs : List Nat)
    (hd : Cslib.URM.Diverges P inputs) (fuel : Nat) :
    (Langlib.Brainfuck.evalProg {} (URMBrainfuck.compile P inputs)
      Langlib.Common.Input.empty fuel).exit = .outOfFuel :=
  URMBrainfuck.preserves_divergence P inputs hd Langlib.Common.Input.empty fuel

end Langlib.Computability.URMBrainloller
