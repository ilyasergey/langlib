import Langlib.Common.TestHarness
import Langlib.Computability.Piet

/-!
Differential tests for the verified stack macros and straight-corridor
lowerer in `Langlib.Computability.URMPiet`.

The current compiler intentionally accepts only `Z`, `S`, and `T`.  A `J`
is rejected because the image-level routing proof needed for a back edge has
not landed.  Every accepted case runs the generated codel grid with Piet's
reference evaluator and compares the decoded answer with the executable URM
interpreter.
-/

namespace Langlib.Tests.URMPiet

open Langlib.Common
open Cslib.URM (Program Instr)

private def toks (line : String) : List String :=
  let body := match line.splitOn "#" with
    | [] => ""
    | h :: _ => h
  (body.splitOn " ").flatMap (fun t => t.splitOn "\t") |>.filter (fun t => t ≠ "")

private def parseNat (t : String) : Except String Nat :=
  match t.toNat? with
  | some n => .ok n
  | none => .error s!"not a register or label: '{t}'"

private def parseLine (line : String) : Except String (Option (Sum (List Nat) Instr)) := do
  match toks line with
  | [] => return none
  | "in" :: rest => return some (.inl (← rest.mapM parseNat))
  | ["Z", a] => return some (.inr (.Z (← parseNat a)))
  | ["S", a] => return some (.inr (.S (← parseNat a)))
  | ["T", a, b] => return some (.inr (.T (← parseNat a) (← parseNat b)))
  | ["J", a, b, q] =>
    return some (.inr (.J (← parseNat a) (← parseNat b) (← parseNat q)))
  | ts => .error s!"bad URM line: {String.intercalate " " ts}"

private def parseURM (src : String) : Except String (Program × List Nat) := do
  let mut prog : List Instr := []
  let mut inputs : List Nat := []
  for line in src.splitOn "\n" do
    match ← parseLine line with
    | none => pure ()
    | some (.inl vs) => inputs := vs
    | some (.inr i) => prog := prog ++ [i]
  return (prog, inputs)

private def urmSteps : Nat := 100000

def run (src : String) (_input : Input) (fuel : Nat) : Except String RunResult := do
  let (P, inputs) ← parseURM src
  if ¬ Langlib.Computability.URM.haltsIn P (Cslib.URM.State.init inputs) urmSteps then
    .error s!"the URM program did not halt within {urmSteps} steps"
  else
    let want := Langlib.Computability.URM.result P inputs urmSteps
    let grid ← Langlib.Computability.URMPiet.compileStraight P inputs
    let r := Langlib.Piet.evalGrid grid (Input.ofString "") fuel
    match r.exit with
    | .halted =>
      match Langlib.Computability.URMPiet.decodeOutput r.output with
      | some got =>
        if got == want then
          return { output := s!"ok {want}".toUTF8, exit := .halted }
        else
          return { exit := .error s!"URM says {want}, compiled Piet says {got}" }
      | none => return { exit := .error "the Piet output did not decode" }
    | .outOfFuel => return { exit := .error s!"compiled Piet ran out of fuel ({fuel})" }
    | .error msg => return { exit := .error s!"compiled Piet failed: {msg}" }

def sizeOf (src : String) (_input : Input) (_fuel : Nat) : Except String RunResult := do
  let (P, inputs) ← parseURM src
  let grid ← Langlib.Computability.URMPiet.compileStraight P inputs
  let message := s!"{grid.width}x{grid.height}={grid.codels.size}"
  return { output := message.toUTF8, exit := .halted }

def suite : Suite where
  name := "urm -> piet (verified stack macros, straight corridor)"
  run := run
  cases :=
    [ { name := "empty program preserves register zero",
        source := .inline "in 9", expect := .outputs "ok 9", fuel := 1000000 }
    , { name := "a constant built by increments",
        source := .inline "S 0\nS 0\nS 0", expect := .outputs "ok 3", fuel := 1000000 }
    , { name := "zero clears the answer register",
        source := .inline "in 7\nZ 0", expect := .outputs "ok 0", fuel := 1000000 }
    , { name := "transfer copies into the answer register",
        source := .inline "in 0 6\nT 1 0", expect := .outputs "ok 6", fuel := 1000000 }
    , { name := "successor at depth then transfer",
        source := .inline "in 0 6\nS 1\nT 1 0", expect := .outputs "ok 7", fuel := 1000000 }
    , { name := "a backward J is rejected until routing is proved",
        source := .inline "in 0 1\nJ 0 1 0", expect := .parseError "routing gadget" }
    ]

def sizeSuite : Suite where
  name := "urm -> piet (partial corridor size)"
  run := sizeOf
  cases :=
    [ { name := "three increments",
        source := .inline "S 0\nS 0\nS 0", expect := .outputs "112x3=336" }
    , { name := "one transfer with two inputs",
        source := .inline "in 0 6\nT 1 0", expect := .outputs "67x3=201" }
    ]

def suites : List Suite := [suite, sizeSuite]

end Langlib.Tests.URMPiet
