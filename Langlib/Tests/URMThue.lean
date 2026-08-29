import Langlib.Common.TestHarness
import Langlib.Computability.Thue

/-!
Differential tests for the executable URM to Thue generator.

The generated rulebase is large by design.  Registers are unary, and the
general equality macro used by `J` expands to more than one thousand rewrite
rules even for a three-instruction source program.  Cases therefore use tiny
values and generous fuel.

These are executable generator tests.  `Langlib.Computability.Thue` proves
the per-instruction counter-macro arithmetic and the encoding invariants; the
composition with Thue substring rewriting is still open, so this suite is not
described as testing a certified compiler.
-/

namespace Langlib.Tests.URMThue

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

private def urmSteps : Nat := 10_000

/-- Compile, run, and compare with the executable URM reference. -/
def run (src : String) (_input : Input) (fuel : Nat) : Except String RunResult := do
  let (P, inputs) ← parseURM src
  if ¬ Langlib.Computability.URM.haltsIn P (Cslib.URM.State.init inputs) urmSteps then
    .error s!"the URM program did not halt within {urmSteps} steps"
  else
    let want := Langlib.Computability.URM.result P inputs urmSteps
    let prog := Langlib.Computability.URMThue.compile P inputs
    let r := Langlib.Thue.evalProg { finalState := true } prog (Input.ofString "") fuel
    match r.exit with
    | .halted =>
      match Langlib.Computability.URMThue.decodeOutput r.output with
      | some got =>
        if got == want then
          return { output := s!"ok {want}".toUTF8, exit := .halted }
        else
          return { exit := .error s!"URM says {want}, generated Thue says {got}" }
      | none => return { exit := .error "the final Thue state did not decode" }
    | .outOfFuel => return { exit := .error s!"generated program ran out of fuel ({fuel})" }
    | .error msg => return { exit := .error s!"generated program failed: {msg}" }

/-- Report generated rule count and initial-state length. -/
def sizeOf (src : String) (_input : Input) (_fuel : Nat) : Except String RunResult := do
  let (P, inputs) ← parseURM src
  let prog := Langlib.Computability.URMThue.compile P inputs
  return { output := s!"{prog.rules.length}/{prog.initial.length}".toUTF8, exit := .halted }

private def thueFuel : Nat := 1_000_000

def suite : Suite where
  name := "urm -> thue (executable generator)"
  run := run
  cases :=
    [ { name := "a constant built by increments", fuel := thueFuel,
        source := .inline "S 0\nS 0", expect := .outputs "ok 2" }
    , { name := "zero clears the answer register", fuel := thueFuel,
        source := .inline "in 2\nZ 0", expect := .outputs "ok 0" }
    , { name := "transfer copies into the answer register", fuel := thueFuel,
        source := .inline "in 0 2\nT 1 0", expect := .outputs "ok 2" }
    , { name := "an unconditional jump skips an increment", fuel := thueFuel,
        source := .inline "in 3\nJ 0 0 2\nS 0", expect := .outputs "ok 3" }
      -- One iteration of the standard addition loop.  Instruction 2 is the
      -- backward jump; instruction 0 exits once r0 reaches r1.
    , { name := "addition by a backward jump (0 + 1)", fuel := thueFuel,
        source := .inline "in 0 1\nJ 0 1 3\nS 0\nJ 0 0 0",
        expect := .outputs "ok 1" }
    , { name := "copy inside a backward loop", fuel := thueFuel,
        source := .inline "in 0 1\nJ 0 1 4\nT 1 2\nS 0\nJ 0 0 0",
        expect := .outputs "ok 1" }
    ]

def sizeSuite : Suite where
  name := "urm -> thue (generated size)"
  run := sizeOf
  cases :=
    [ { name := "two increments", source := .inline "S 0\nS 0",
        expect := .outputs "77/15" }
    , { name := "one transfer", source := .inline "in 0 2\nT 1 0",
        expect := .outputs "174/18" }
    ]

def suites : List Suite := [suite, sizeSuite]

end Langlib.Tests.URMThue
