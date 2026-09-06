import Langlib.Computability.Ook.Simulation
import Langlib.Computability.Brainfuck.Divergence

/-! # Ook preserves URM divergence

The existing program representation and evaluator agree definitionally with
Brainfuck, so its divergence proof transfers to the same compiled programs.
-/

namespace Langlib.Computability.URMOok

open Langlib.Common

/-- The shared Brainfuck execution exhausts every finite fuel on divergent input. -/
theorem preserves_divergence (P : Cslib.URM.Program) (inputs : List Nat)
    (hd : Cslib.URM.Diverges P inputs) (fuel : Nat) :
    (Langlib.Brainfuck.evalProg {} (URMBrainfuck.compile P inputs)
      Langlib.Common.Input.empty fuel).exit = .outOfFuel :=
  URMBrainfuck.preserves_divergence P inputs hd Langlib.Common.Input.empty fuel

end Langlib.Computability.URMOok
