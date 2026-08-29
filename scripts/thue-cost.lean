import Langlib.Computability.Thue

/-!
Size and cost of the generated Thue rulebase, for `docs/computability-thue.md`.

Run from the repository root:

    lake env lean --run scripts/thue-cost.lean

It compiles one small URM program, reports the number of generated rules,
the length of the initial string, the exact number of rewrites the program
takes to halt, and the answer the final-state decoder reads back.
-/

open Langlib.Common
open Langlib.Computability
open Cslib.URM (Program Instr)

/-- `in 0 1` / `J 0 1 3` / `S 0` / `J 0 0 0`: add one to register 0 by
looping until it equals register 1. -/
def addition : Program := [.J 0 1 3, .S 0, .J 0 0 0]

/-- Count the rewrites a program takes to halt, or `none` within the budget. -/
def rewrites (rules : List Langlib.Thue.Rule) (st : Langlib.Thue.MState) :
    Nat → Option Nat
  | 0 => none
  | fuel + 1 =>
    match Langlib.Thue.step {} rules st with
    | none => some 0
    | some st' => (rewrites rules st' fuel).map (· + 1)

/-- `S 0` twice: build the constant two in the answer register. -/
def twoIncrements : Program := [.S 0, .S 0]

/-- `in 0 2` / `T 1 0`: copy the second input into the answer register. -/
def oneTransfer : Program := [.T 1 0]

def report (name : String) (P : Program) (inputs : List Nat) : IO Unit := do
  let prog := URMThue.compile P inputs
  let start : Langlib.Thue.MState :=
    { str := prog.initial.toList, input := Input.ofString "" }
  let run := Langlib.Thue.evalProg { finalState := true } prog
    (Input.ofString "") 100000
  IO.println s!"{name}: {prog.rules.length} rules, {prog.initial.length}-character initial state, {rewrites prog.rules start 100000} rewrites, answer {URMThue.decodeOutput run.output}"

def main : IO Unit := do
  report "two increments" twoIncrements []
  report "one transfer" oneTransfer [0, 2]
  report "addition loop" addition [0, 1]
