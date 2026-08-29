import Langlib.Common.TestHarness
import Langlib.Computability.Piet

/-!
Differential tests for both Piet lowerers in
`Langlib.Computability.URMPiet`.  The proved straight-corridor fragment
rejects `J`.  The full runnable compiler uses a branchless dispatcher and one
geometric loop, so its tests include taken and untaken jumps and a backward
loop.  Every accepted case runs the generated grid with Piet's reference
evaluator and compares its decimal output with the executable URM interpreter.
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

def runStraight (src : String) (_input : Input) (fuel : Nat) : Except String RunResult := do
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

def runFull (src : String) (_input : Input) (fuel : Nat) : Except String RunResult := do
  let (P, inputs) ← parseURM src
  if ¬ Langlib.Computability.URM.haltsIn P (Cslib.URM.State.init inputs) urmSteps then
    .error s!"the URM program did not halt within {urmSteps} steps"
  else
    let want := Langlib.Computability.URM.result P inputs urmSteps
    let grid := Langlib.Computability.URMPiet.compile P inputs
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

def sizeOfStraight (src : String) (_input : Input) (_fuel : Nat) : Except String RunResult := do
  let (P, inputs) ← parseURM src
  let grid ← Langlib.Computability.URMPiet.compileStraight P inputs
  let message := s!"{grid.width}x{grid.height}={grid.codels.size}"
  return { output := message.toUTF8, exit := .halted }

def sizeOfFull (src : String) (_input : Input) (_fuel : Nat) : Except String RunResult := do
  let (P, inputs) ← parseURM src
  let grid := Langlib.Computability.URMPiet.compile P inputs
  let message := s!"{grid.width}x{grid.height}={grid.codels.size}"
  return { output := message.toUTF8, exit := .halted }

def suite : Suite where
  name := "urm -> piet (verified stack macros, straight corridor)"
  run := runStraight
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
    , { name := "the straight compiler rejects J explicitly",
        source := .inline "in 0 1\nJ 0 1 0", expect := .parseError "routing gadget" }
    ]

def sizeSuite : Suite where
  name := "urm -> piet (partial corridor size)"
  run := sizeOfStraight
  cases :=
    [ { name := "three increments",
        source := .inline "S 0\nS 0\nS 0", expect := .outputs "112x3=336" }
    , { name := "one transfer with two inputs",
        source := .inline "in 0 6\nT 1 0", expect := .outputs "67x3=201" }
    ]

def fullSuite : Suite where
  name := "urm -> piet (branchless dispatcher, real evaluator)"
  run := runFull
  cases :=
    [ { name := "empty program preserves register zero",
        source := .inline "in 9", expect := .outputs "ok 9", fuel := 5000 }
    , { name := "a taken forward jump halts immediately",
        source := .inline "in 2 2\nJ 0 1 4\nS 0\nS 0\nS 0",
        expect := .outputs "ok 2", fuel := 20000 }
    , { name := "an untaken forward jump falls through",
        source := .inline "in 1 2\nJ 0 1 4\nS 0\nS 0\nS 0",
        expect := .outputs "ok 4", fuel := 20000 }
    , { name := "transfer inside a backward copy loop",
        source := .inline "in 0 3 0\nJ 2 1 4\nS 2\nT 2 0\nJ 0 0 0",
        expect := .outputs "ok 3", fuel := 100000 }
    , { name := "backward jumps implement addition",
        source := .inline "in 3 4\nJ 2 1 5\nS 0\nS 2\nJ 0 0 0",
        expect := .outputs "ok 7", fuel := 100000 }
    ]

def fullSizeSuite : Suite where
  name := "urm -> piet (singleton dispatcher size)"
  run := sizeOfFull
  cases :=
    [ { name := "three increments",
        source := .inline "S 0\nS 0\nS 0", expect := .outputs "915x3=2745" }
    , { name := "backward-loop addition",
        source := .inline "in 3 4\nJ 2 1 5\nS 0\nS 2\nJ 0 0 0",
        expect := .outputs "2416x3=7248" }
    ]

def suites : List Suite := [suite, sizeSuite, fullSuite, fullSizeSuite]

end Langlib.Tests.URMPiet
