import Langlib.Common.TestHarness
import Langlib.Computability.Subleq

/-!
Differential tests for the certified URM to subleq compiler.

Every case is a *pair* of runs. The source of a case is a small URM program
in the ad-hoc notation parsed below; `run` executes it on langlib's
executable URM interpreter (`Langlib.Computability.URM.run`, which agrees
with cslib's `Step` relation by `step_eq_some_iff_Step`), compiles the same
program with `Langlib.Computability.URMSubleq.compile`, runs the image on the
subleq interpreter, and decodes the answer. A case passes only when the two
agree, and the expected output pins the agreed value as well.

The compiled output is huge by design: the answer leaves the machine in
unary, one byte per unit, and `J` costs nine subleq instructions. The
programs are kept tiny and the fuel generous for that reason. See
`docs/computability-subleq.md`.

The notation, one item per line, `#` to end of line is a comment:

```
in 3 4        the input vector (at most one such line)
Z 0           zero register 0
S 0           increment register 0
T 0 1         copy register 0 to register 1
J 2 1 5       jump to instruction 5 if registers 2 and 1 are equal
```
-/

namespace Langlib.Tests.URMSubleq

open Langlib.Common
open Cslib.URM (Program Instr)

/-- Whitespace-separated non-empty tokens, comments stripped. -/
private def toks (line : String) : List String :=
  let body := match line.splitOn "#" with
    | [] => ""
    | h :: _ => h
  (body.splitOn " ").flatMap (fun t => (t.splitOn "\t")) |>.filter (fun t => t ≠ "")

private def parseNat (t : String) : Except String Nat :=
  match t.toNat? with
  | some n => .ok n
  | none => .error s!"not a register or label: '{t}'"

/-- One line: nothing, an input vector, or an instruction. -/
private def parseLine (line : String) : Except String (Option (Sum (List Nat) Instr)) := do
  match toks line with
  | [] => return none
  | "in" :: rest => return some (.inl (← rest.mapM parseNat))
  | ["Z", a] => return some (.inr (.Z (← parseNat a)))
  | ["S", a] => return some (.inr (.S (← parseNat a)))
  | ["T", a, b] => return some (.inr (.T (← parseNat a) (← parseNat b)))
  | ["J", a, b, c] => return some (.inr (.J (← parseNat a) (← parseNat b) (← parseNat c)))
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

/-- How many URM steps the reference interpreter is allowed. -/
private def urmSteps : Nat := 100000

/-- Compile the URM program to subleq, run both, and report agreement. -/
def run (src : String) (_input : Input) (fuel : Nat) : Except String RunResult := do
  let (P, inputs) ← parseURM src
  if ¬ Langlib.Computability.URM.haltsIn P (Cslib.URM.State.init inputs) urmSteps then
    .error s!"the URM program did not halt within {urmSteps} steps"
  else
    let want := Langlib.Computability.URM.result P inputs urmSteps
    let prog := Langlib.Computability.URMSubleq.compile P inputs
    let r := Langlib.Subleq.evalProg prog (Input.ofString "") fuel
    match r.exit with
    | .halted =>
      match Langlib.Computability.URMSubleq.decodeOutput r.output with
      | some got =>
        if got == want then
          return { output := s!"ok {want}".toUTF8, exit := .halted }
        else
          return { exit := .error s!"URM says {want}, compiled subleq says {got}" }
      | none => return { exit := .error "the output did not decode" }
    | .outOfFuel => return { exit := .error s!"compiled program ran out of fuel ({fuel})" }
    | .error m => return { exit := .error s!"compiled program failed: {m}" }

/-- Report the size of the compiled image, so the cost is pinned down rather
than described. -/
def sizeOf (src : String) (_input : Input) (_fuel : Nat) : Except String RunResult := do
  let (P, inputs) ← parseURM src
  let prog := Langlib.Computability.URMSubleq.compile P inputs
  return { output := s!"{prog.size}".toUTF8, exit := .halted }

def suite : Suite where
  name := "urm -> subleq (certified compiler)"
  run := run
  cases :=
    [ { name := "the empty program is the identity on register 0",
        source := .inline "in 9", expect := .outputs "ok 9" }
    , { name := "no program, no input",
        source := .inline "", expect := .outputs "ok 0" }
    , { name := "a constant, built by increments",
        source := .inline "S 0\nS 0\nS 0", expect := .outputs "ok 3" }
    , { name := "Z clears a register that held an input",
        source := .inline "in 7\nZ 0", expect := .outputs "ok 0" }
    , { name := "T copies into the answer register",
        source := .inline "in 0 6\nT 1 0", expect := .outputs "ok 6" }
    , { name := "T from a register to itself is a no-op",
        source := .inline "in 5\nT 0 0", expect := .outputs "ok 5" }
    , { name := "T out of a register the input never reached",
        source := .inline "in 4\nT 3 0", expect := .outputs "ok 0" }
    , { name := "J taken jumps forward over the increments",
        source := .inline "in 2 2\nJ 0 1 4\nS 0\nS 0\nS 0",
        expect := .outputs "ok 2" }
    , { name := "J untaken falls through, second operand larger",
        source := .inline "in 1 2\nJ 0 1 4\nS 0\nS 0\nS 0",
        expect := .outputs "ok 4" }
    , { name := "J untaken falls through, first operand larger",
        source := .inline "in 3 2\nJ 0 1 4\nS 0\nS 0\nS 0",
        expect := .outputs "ok 6" }
    , { name := "a jump past the end of the program halts",
        source := .inline "in 5\nJ 0 0 99\nS 0", expect := .outputs "ok 5" }
      -- Addition, the standard URM loop, with a backward jump
    , { name := "addition by a copy loop (3 + 4)",
        source := .inline "in 3 4\nJ 2 1 5\nS 0\nS 2\nJ 0 0 0",
        expect := .outputs "ok 7" }
    , { name := "addition where the counter starts equal (5 + 0)",
        source := .inline "in 5 0\nJ 2 1 5\nS 0\nS 2\nJ 0 0 0",
        expect := .outputs "ok 5" }
      -- Multiplication: r0 := r1 * r2, by repeated addition
      -- Multiplication, r0 := r1 * r2, by repeated addition. Registers 3 and
      -- 4 are the outer and inner counters; the exit is a jump to 8, which is
      -- past the end of this eight-instruction program.
    , { name := "multiplication by nested loops (3 * 4)",
        source := .inline
          ("in 0 3 4\n" ++
           "J 3 2 8\n" ++    -- 0: outer loop, r3 counts up to r2
           "J 4 1 5\n" ++    -- 1: inner loop, r4 counts up to r1
           "S 0\n" ++        -- 2
           "S 4\n" ++        -- 3
           "J 0 0 1\n" ++    -- 4: back to the inner test
           "Z 4\n" ++        -- 5: reset the inner counter
           "S 3\n" ++        -- 6: bump the outer counter
           "J 0 0 0"),       -- 7: back to the outer test
        expect := .outputs "ok 12" }
    , { name := "multiplication by zero",
        source := .inline
          ("in 0 7 0\n" ++
           "J 3 2 8\nJ 4 1 5\nS 0\nS 4\nJ 0 0 1\nZ 4\nS 3\nJ 0 0 0"),
        expect := .outputs "ok 0" }
    ]

def sizeSuite : Suite where
  name := "urm -> subleq (compiled image size)"
  run := sizeOf
  cases :=
    [ { name := "three increments", source := .inline "S 0\nS 0\nS 0",
        expect := .outputs "38" }
    , { name := "one copy, one input", source := .inline "in 5\nT 0 1",
        expect := .outputs "42" }
    , { name := "the addition loop, two inputs",
        source := .inline "in 3 4\nJ 2 1 5\nS 0\nS 2\nJ 0 0 0",
        expect := .outputs "91" }
    ]

def suites : List Suite := [suite, sizeSuite]

end Langlib.Tests.URMSubleq
