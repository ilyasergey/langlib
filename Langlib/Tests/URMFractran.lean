import Langlib.Common.TestHarness
import Langlib.Computability.Fractran
import Langlib.Computability.URM

/-!
Differential tests for the verified URM-to-FRACTRAN compiler.

Each case executes the URM reference interpreter, compiles the same program,
runs the generated fraction list with the actual FRACTRAN interpreter in
`final` mode, and compares the decoded terminal power of two.  The same
execution path is used by `fractranComplete`.

Prime-exponent states grow quickly, so the examples are deliberately small
and receive generous fuel.
-/

namespace Langlib.Tests.URMFractran

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

/-- Compile, run, and compare with the executable URM reference. -/
def run (src : String) (_input : Input) (fuel : Nat) : Except String RunResult := do
  let (P, inputs) ← parseURM src
  if ¬ Langlib.Computability.URM.haltsIn P (Cslib.URM.State.init inputs) urmSteps then
    .error s!"the URM program did not halt within {urmSteps} steps"
  else
    let want := Langlib.Computability.URM.result P inputs urmSteps
    let artifact := Langlib.Computability.URMFractran.compileProgram P inputs
    let r := Langlib.Fractran.evalProg { out := .final }
      artifact.code artifact.start fuel
    match r.exit with
    | .halted =>
      match Langlib.Computability.URMFractran.decodeOutput r.output with
      | some got =>
        if got == want then
          return { output := s!"ok {want}".toUTF8, exit := .halted }
        else
          return { exit := .error s!"URM says {want}, compiled FRACTRAN says {got}" }
      | none => return { exit := .error "the final power-of-two output did not decode" }
    | .outOfFuel => return { exit := .error s!"compiled program ran out of fuel ({fuel})" }
    | .error msg => return { exit := .error s!"compiled program failed: {msg}" }

private def stepsToHalt (p : Langlib.Fractran.Prog) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, n =>
    match Langlib.Fractran.step p n with
    | none => some 0
    | some n' => (stepsToHalt p fuel n').map (fun k => k + 1)

/-- Stable code-size and fraction-application count for one small image. -/
def stats (src : String) (_input : Input) (_fuel : Nat) : Except String RunResult := do
  let (P, inputs) ← parseURM src
  let artifact := Langlib.Computability.URMFractran.compileProgram P inputs
  let some steps := stepsToHalt artifact.code 100000 artifact.start
    | throw "compiled program did not halt while measuring"
  return {
    output := s!"{artifact.code.length} fractions, {artifact.code.render.length} chars, {steps} steps".toUTF8
    exit := .halted
  }

private def ftFuel : Nat := 5_000_000

def suite : Suite where
  name := "urm -> fractran (verified compiler)"
  run := run
  cases :=
    [ { name := "empty program preserves register 0", fuel := ftFuel,
        source := .inline "in 7", expect := .outputs "ok 7" }
    , { name := "constant built by increments", fuel := ftFuel,
        source := .inline "S 0\nS 0\nS 0", expect := .outputs "ok 3" }
    , { name := "zero clears the answer register", fuel := ftFuel,
        source := .inline "in 8\nZ 0", expect := .outputs "ok 0" }
    , { name := "transfer copies into the answer register", fuel := ftFuel,
        source := .inline "in 0 4\nT 1 0", expect := .outputs "ok 4" }
    , { name := "self-transfer is a no-op", fuel := ftFuel,
        source := .inline "in 5\nT 0 0", expect := .outputs "ok 5" }
    , { name := "taken jump skips increments", fuel := ftFuel,
        source := .inline "in 2 2\nJ 0 1 3\nS 0\nS 0", expect := .outputs "ok 2" }
    , { name := "untaken jump, left register larger", fuel := ftFuel,
        source := .inline "in 3 2\nJ 0 1 3\nS 0\nS 0", expect := .outputs "ok 5" }
    , { name := "untaken jump, right register larger", fuel := ftFuel,
        source := .inline "in 1 2\nJ 0 1 3\nS 0\nS 0", expect := .outputs "ok 3" }
    , { name := "jump past the end halts", fuel := ftFuel,
        source := .inline "in 6\nJ 0 0 99\nS 0", expect := .outputs "ok 6" }
    , { name := "addition loop uses a backward unconditional jump", fuel := ftFuel,
        source := .inline "in 3 4\nJ 2 1 5\nS 0\nS 2\nJ 0 0 0",
        expect := .outputs "ok 7" }
    ]

def statsSuite : Suite where
  name := "urm -> fractran (measured cost)"
  run := stats
  cases :=
    [ { name := "two increments", source := .inline "S 0\nS 0",
        expect := .outputs "3 fractions, 18 chars, 3 steps" }
    ]

def suites : List Suite := [suite, statsSuite]

end Langlib.Tests.URMFractran
