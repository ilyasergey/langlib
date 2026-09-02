import Langlib.Common.TestHarness
import Langlib.Computability.Velato

/-!
Differential tests for the certified URM to Velato compiler.

Every case is a *pair* of runs. The source is a small URM program in the
notation below; `run` executes it on langlib's executable URM interpreter,
compiles the same program with `Langlib.Computability.URMVelato.compile`,
runs the resulting Velato program on the Velato interpreter, and decodes the
answer as the number of bytes printed. A case passes only when the two
agree.

These tests are what make the completeness proof's *meta*-theoretic half
checkable: `TuringComplete.compile` is required to be a real function that
runs, and a noncomputable witness would fail here rather than in the kernel.
It is why `pr`, the sequence of primes the encoding uses, is built by search
rather than taken from `Nat.nth Nat.Prime`, which is noncomputable.

The compiled programs are *short* — a dozen statements for a small machine —
because the entire register file is one Velato variable holding
`2^w0 * 3^w1 * ...`. What is not short is the arithmetic: the number grows
exponentially in the register values, so the fuel is generous and the
programs are kept small. `sizeOf` reports the statement count, so the cost is
pinned down rather than described. See `docs/computability-velato.md`.

The notation, one item per line, `#` to end of line is a comment:

```
in 3 4        the input vector (at most one such line)
Z 0           zero register 0
S 0           increment register 0
T 0 1         copy register 0 to register 1
J 2 1 5       jump to instruction 5 if registers 2 and 1 are equal
```
-/

namespace Langlib.Tests.URMVelato

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

/-- Compile the URM program to Velato, run both, and report agreement. -/
def run (src : String) (_input : Input) (fuel : Nat) : Except String RunResult := do
  let (P, inputs) ← parseURM src
  if ¬ Langlib.Computability.URM.haltsIn P (Cslib.URM.State.init inputs) urmSteps then
    .error s!"the URM program did not halt within {urmSteps} steps"
  else
    let want := Langlib.Computability.URM.result P inputs urmSteps
    let prog := Langlib.Computability.URMVelato.compile P inputs
    let r := Langlib.Velato.evalProg prog (Input.ofString "") fuel
    match r.exit with
    | .halted =>
      match Langlib.Computability.URMVelato.decodeOutput r.output with
      | some got =>
        if got == want then
          return { output := s!"ok {want}".toUTF8, exit := .halted }
        else
          return { exit := .error s!"URM says {want}, compiled Velato says {got}" }
      | none => return { exit := .error "the output did not decode" }
    | .outOfFuel => return { exit := .error s!"compiled program ran out of fuel ({fuel})" }
    | .error m => return { exit := .error s!"compiled program failed: {m}" }

/-- The statement count of the compiled program, so the cost of the
one-variable encoding is pinned down rather than described. -/
def sizeOf (src : String) (_input : Input) (_fuel : Nat) : Except String RunResult := do
  let (P, inputs) ← parseURM src
  let prog := Langlib.Computability.URMVelato.compile P inputs
  return { output := s!"{prog.length}".toUTF8, exit := .halted }

def suite : Suite where
  name := "urm -> velato (certified compiler)"
  run := run
  cases :=
    [ { name := "the empty program is the identity on register 0",
        source := .inline "in 5", expect := .outputs "ok 5" }
    , { name := "no program, no input",
        source := .inline "", expect := .outputs "ok 0" }
    , { name := "a constant, built by increments",
        source := .inline "S 0\nS 0\nS 0", expect := .outputs "ok 3" }
    , { name := "Z clears a register that held an input",
        source := .inline "in 7\nZ 0", expect := .outputs "ok 0" }
    , { name := "T copies into the answer register",
        source := .inline "in 0 6\nT 1 0", expect := .outputs "ok 6" }
    , { name := "T from a register to itself is a no-op",
        source := .inline "in 4\nT 0 0", expect := .outputs "ok 4" }
    , { name := "T out of a register the input never reached",
        source := .inline "in 4\nT 3 0", expect := .outputs "ok 0" }
    , { name := "J taken jumps forward over the increments",
        source := .inline "in 2 2\nJ 0 1 4\nS 0\nS 0\nS 0", expect := .outputs "ok 2" }
    , { name := "J not taken falls through",
        source := .inline "in 2 3\nJ 0 1 4\nS 0\nS 0\nS 0", expect := .outputs "ok 5" }
    , { name := "a jump past the end halts",
        source := .inline "in 1\nJ 0 0 9", expect := .outputs "ok 1" }
    , { name := "a loop that adds register 1 to register 0",
        source := .inline "in 2 3\nJ 1 2 6\nS 0\nS 2\nJ 0 0 0\nZ 3\nZ 3",
        expect := .outputs "ok 5" }
    , { name := "a register above the answer register is carried too",
        source := .inline "in 0 0 4\nT 2 0", expect := .outputs "ok 4" }
    , { name := "a high register index still gets its own prime",
        source := .inline "in 0 0 0 0 0 0 0 0 2\nT 8 0", expect := .outputs "ok 2" }
    ]

/-- The compiled programs are short, because the register file is one
variable. These pin that down. -/
def sizeSuite : Suite where
  name := "urm -> velato (program size)"
  run := sizeOf
  cases :=
    [ { name := "the empty program", source := .inline "", expect := .outputs "5" }
      -- the same five, because the URM program lives inside the dispatch
      -- loop rather than being spread across the top level
    , { name := "one increment", source := .inline "S 0", expect := .outputs "5" }
    ]

def suites : List Suite := [suite, sizeSuite]

end Langlib.Tests.URMVelato
