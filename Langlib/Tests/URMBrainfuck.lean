import Langlib.Common.TestHarness
import Langlib.Computability.Brainfuck

/-!
Differential tests for the certified URM to Brainfuck compiler.

Each case runs the executable URM interpreter, compiles the same program,
runs the generated Brainfuck, and compares the decoded byte count. The
generated programs and their execution traces are large by design: natural
numbers are unary tape columns and every URM step scans a linear dispatcher.
-/

namespace Langlib.Tests.URMBrainfuck

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

private def urmSteps : Nat := 10000

/-- Compile, run, and compare with the executable URM reference. -/
def run (src : String) (_input : Input) (fuel : Nat) : Except String RunResult := do
  let (P, inputs) ← parseURM src
  if ¬ Langlib.Computability.URM.haltsIn P (Cslib.URM.State.init inputs) urmSteps then
    .error s!"the URM program did not halt within {urmSteps} steps"
  else
    let want := Langlib.Computability.URM.result P inputs urmSteps
    let prog := Langlib.Computability.URMBrainfuck.compile P inputs
    let r := Langlib.Brainfuck.evalProg {} prog
      (Langlib.Computability.URMBrainfuck.encodeInput inputs) fuel
    match r.exit with
    | .halted =>
      match Langlib.Computability.URMBrainfuck.decodeOutput r.output with
      | some got =>
        if got == want then
          return { output := s!"ok {want}".toUTF8, exit := .halted }
        else
          return { exit := .error s!"URM says {want}, compiled Brainfuck says {got}" }
      | none => return { exit := .error "the output did not decode" }
    | .outOfFuel => return { exit := .error s!"compiled program ran out of fuel ({fuel})" }
    | .error msg => return { exit := .error s!"compiled program failed: {msg}" }

/-- Report rendered source size for a stable cost regression. -/
def sizeOf (src : String) (_input : Input) (_fuel : Nat) : Except String RunResult := do
  let (P, inputs) ← parseURM src
  let prog := Langlib.Computability.URMBrainfuck.compile P inputs
  return { output := s!"{prog.render.length}".toUTF8, exit := .halted }

private def bfFuel : Nat := 200000000

def suite : Suite where
  name := "urm -> brainfuck (certified compiler)"
  run := run
  cases :=
    [ { name := "a constant built by increments", fuel := bfFuel,
        source := .inline "S 0\nS 0", expect := .outputs "ok 2" }
    , { name := "transfer copies an input into the answer register", fuel := bfFuel,
        source := .inline "in 0 2\nT 1 0", expect := .outputs "ok 2" }
    , { name := "zero clears the answer register", fuel := bfFuel,
        source := .inline "in 2\nZ 0", expect := .outputs "ok 0" }
    , { name := "addition uses a backward unconditional J", fuel := bfFuel,
        source := .inline "in 1 1\nJ 2 1 5\nS 0\nS 2\nJ 0 0 0",
        expect := .outputs "ok 2" }
    , { name := "copy loop followed by a backward J", fuel := bfFuel,
        source := .inline "in 0 2\nJ 0 1 4\nT 1 2\nS 0\nJ 0 0 0",
        expect := .outputs "ok 2" }
    ]

def sizeSuite : Suite where
  name := "urm -> brainfuck (rendered source size)"
  run := sizeOf
  cases :=
    [ { name := "two increments", source := .inline "S 0\nS 0",
        expect := .outputs "10197" }
    ]

def suites : List Suite := [suite, sizeSuite]

end Langlib.Tests.URMBrainfuck
