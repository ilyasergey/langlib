/-
A one-line demonstration of the certified URM to Unlambda compiler.

    lake env lean --run scripts/unlambda-urm-demo.lean

It compiles the empty URM program with input vector `[3]`, which halts at
once with 3 in register 0, then runs the compiled Unlambda term and decodes
its output. See docs/computability-unlambda.md.
-/
import Langlib.Computability.Unlambda

open Langlib.Common
open Langlib.Computability.URMUnlambda

def main : IO Unit := do
  let P : Cslib.URM.Program := []
  let inputs : List Nat := [3]
  let prog := compile P inputs
  let r := Langlib.Unlambda.evalProg prog (encodeInput inputs) 1000000
  IO.println s!"size={prog.size} exit={repr r.exit} decoded={decodeOutput r.output}"
