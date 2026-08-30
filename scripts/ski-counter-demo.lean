/-
A demonstration of the certified compiler into the SKI calculus.

    lake env lean --run scripts/ski-counter-demo.lean

It compiles the counter-machine program `+0 +0 +0 [0 -0 . ]`, which emits one
byte per unit of register 0, and normalises the result. SKI has no output
instruction, so the answer is the normal form itself: three `K`s in front of
an `I`. See docs/computability-ski.md.
-/
import Langlib.Computability.Ski

open Langlib.Common
open Langlib.Computability.Counter
open Langlib.Computability.URMSki

def main : IO Unit := do
  let c : Code :=
    [Cmd.inc 0, Cmd.inc 0, Cmd.inc 0, Cmd.loop 0 [Cmd.dec 0, Cmd.emit]]
  let prog : Langlib.Ski.Term :=
    .app unaryT (.app (getT 1) (.app (codeT 1 c) (listT [0, 0])))
  match Langlib.Ski.normalise 1000000 prog with
  | none => IO.println "out of fuel"
  | some nf =>
    let decoded := decodeOutput ((nf.render ++ "\n").toUTF8)
    IO.println s!"size={prog.size} normal form={nf.render} decoded={decoded}"
