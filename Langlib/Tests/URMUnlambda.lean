import Langlib.Common.TestHarness
import Langlib.Computability.Unlambda

/-!
Differential tests for the certified URM to Unlambda compiler.

Each case runs the executable URM interpreter, compiles the same program,
runs the generated Unlambda, and compares the decoded byte count. The
generated terms and their runs are large by design: a register is a Scott
numeral, the file holding them is a Scott list, and every URM step goes
through the counter machine's linear dispatcher.
-/

namespace Langlib.Tests.URMUnlambda

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
    let prog := Langlib.Computability.URMUnlambda.compile P inputs
    let r := Langlib.Unlambda.evalProg prog
      (Langlib.Computability.URMUnlambda.encodeInput inputs) fuel
    match r.exit with
    | .halted =>
      match Langlib.Computability.URMUnlambda.decodeOutput r.output with
      | some got =>
        if got == want then
          return { output := s!"ok {want}".toUTF8, exit := .halted }
        else
          return { exit := .error s!"URM says {want}, compiled Unlambda says {got}" }
      | none => return { exit := .error "the output did not decode" }
    | .outOfFuel => return { exit := .error s!"compiled program ran out of fuel ({fuel})" }
    | .error msg => return { exit := .error s!"compiled program failed: {msg}" }

/-- Report the number of combinators for a stable cost regression. -/
def sizeOf (src : String) (_input : Input) (_fuel : Nat) : Except String RunResult := do
  let (P, inputs) ← parseURM src
  let prog := Langlib.Computability.URMUnlambda.compile P inputs
  return { output := s!"{prog.size}".toUTF8, exit := .halted }

private def ulFuel : Nat := 200000000

def suite : Suite where
  name := "urm -> unlambda (certified compiler)"
  run := run
  cases :=
    [ { name := "a constant built by increments", fuel := ulFuel,
        source := .inline "S 0\nS 0", expect := .outputs "ok 2" }
    , { name := "transfer copies an input into the answer register", fuel := ulFuel,
        source := .inline "in 0 2\nT 1 0", expect := .outputs "ok 2" }
    , { name := "zero clears the answer register", fuel := ulFuel,
        source := .inline "in 2\nZ 0", expect := .outputs "ok 0" }
    , { name := "addition uses a backward unconditional J", fuel := ulFuel,
        source := .inline "in 1 1\nJ 2 1 5\nS 0\nS 2\nJ 0 0 0",
        expect := .outputs "ok 2" }
    ]

def sizeSuite : Suite where
  name := "urm -> unlambda (compiled term size)"
  run := sizeOf
  cases :=
    [ { name := "two increments", source := .inline "S 0\nS 0",
        expect := .outputs "270099" }
    ]

def suites : List Suite := [suite, sizeSuite]

end Langlib.Tests.URMUnlambda
