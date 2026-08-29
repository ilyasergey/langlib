import Langlib.Common.TestHarness
import Langlib.Turpentine.Semantics
import Langlib.Turpentine.Compile.Ook
import Langlib.Computability.Ook

/-!
# Compiler tests: Turpentine to Ook!

Three things are checked here, and they are different things.

* **Differential**, `compiled` against `reference`: every case in `shared`
  is run twice, once by `Langlib.Turpentine.run` and once by
  `Langlib.Turpentine.Compile.Ook.runCompiled`, which compiles to
  brainfuck, renders the result as Ook! *text*, parses that text back with
  `Langlib.Ook.parse` and runs it on the brainfuck core with the EOF
  convention the generated code targets. So each expected string is both a
  golden test of the reference interpreter and a claim that the compiler
  preserved its behaviour through a full round trip of the concrete
  syntax. Every expected string was taken from a run of the reference
  interpreter first.

* **Emitted size**, `renderers`: pins the byte count of the Ook! the
  backend emits, so a change in the layout shows up as a failing test
  rather than as a silently larger file. There is no renderer-agreement
  suite: `Langlib.Ook.render` is the renderer `OokSyntax.parse_render` is
  proved about, so the theorem is already a statement about the shipped
  compiler's literal output.

* **Completeness**, `urm`: small URM programs compiled with
  `ookComplete.compile`, rendered as Ook!, parsed back, run, and decoded.
  The programs are tiny and the fuel is generous because the compiled
  output is huge by design: naturals are unary tape columns and every URM
  step scans a linear dispatcher.

Inputs are small on purpose; an Ook! file is ten times the size of the
brainfuck it came from, and the brainfuck backend is correct rather than
quick (`docs/ook/compiler.md` has the numbers).
-/

namespace Langlib.Tests.CompileOok

open Langlib.Common
open Cslib.URM (Program Instr)

private def ex (f : String) : Source :=
  .file s!"Langlib/Examples/Turpentine/{f}"

/-- The fuel the compiled programs get, matching the brainfuck backend's
own suite. -/
private def ookFuel : Nat := 200_000_000

/-- Cases that both the reference interpreter and the compiled Ook! must
satisfy. -/
def shared : List TestCase :=
  [ { name := "hello example", source := ex "hello.turp", fuel := ookFuel,
      expect := .outputs "Hello, Turpentine!\n" }
  , { name := "cat example", source := ex "cat.turp", input := "meow\n",
      fuel := ookFuel, expect := .outputs "meow\n" }
  , { name := "isqrt example (16)", source := ex "isqrt.turp", input := "16\n",
      fuel := ookFuel, expect := .outputs "4\n" }
  , { name := "sumdigits example (405)", source := ex "sumdigits.turp",
      input := "405\n", fuel := ookFuel, expect := .outputs "9\n" }
  , { name := "gcd example", source := ex "gcd.turp", input := "252\n105\n",
      fuel := ookFuel, expect := .outputs "21\n" }
  , { name := "collatz example (6)", source := ex "collatz.turp", input := "6\n",
      fuel := ookFuel, expect := .outputs "8\n" }
  , { name := "arithmetic", fuel := ookFuel, source := .inline
        "println(6 * 7); println(100 / 7); println(100 % 7);",
      expect := .outputs "42\n14\n2\n" }
  , { name := "nested while", fuel := ookFuel, source := .inline
        ("var i : int := 1; var j : int; while i <= 3 { j := 1; "
          ++ "while j <= i { printByte(48 + j); j := j + 1; } "
          ++ "printByte(10); i := i + 1; }"),
      expect := .outputs "1\n12\n123\n" }
  , { name := "array element write and read", fuel := ookFuel, source := .inline
        ("var a : int[3]; a[0] := 7; a[2] := -5; "
          ++ "println(a[0]); println(a[1]); println(a[2]);"),
      expect := .outputs "7\n0\n-5\n" }
  ]

/-- The compiled programs, as Ook! source text, run through
`Langlib.Ook.parse`. -/
def compiled : Suite where
  name := "turpentine -> ook"
  run := Langlib.Turpentine.Compile.Ook.runCompiled
  cases := shared

/-- The same cases on the reference interpreter: one expected string, two
independent machines. -/
def reference : Suite where
  name := "turpentine -> ook (reference cross-check)"
  run := Langlib.Turpentine.run
  cases := shared

/-- Compile and report the size of the emitted Ook!. -/
def renderAgrees (src : String) (_input : Input) (_fuel : Nat) :
    Except String RunResult := do
  let prog ← Langlib.Turpentine.parse src
  let bf ← Langlib.Turpentine.Compile.Ook.compile prog
  return { output := s!"ok {(Langlib.Ook.render bf).length}".toUTF8, exit := .halted }

/-- Size regression on the emitted Ook!. The renderer these numbers come
from is the one `OokSyntax.parse_render` is proved about, so nothing here
has to bridge a proved renderer to a shipped one. -/
def renderers : Suite where
  name := "turpentine -> ook (emitted size)"
  run := renderAgrees
  cases :=
    [ { name := "hello example", source := ex "hello.turp",
        expect := .outputs "ok 4600" }
    , { name := "cat example", source := ex "cat.turp",
        expect := .outputs "ok 273760" }
    , { name := "the empty program", source := .inline "",
        expect := .outputs "ok 0" }
    , { name := "one statement", source := .inline "printByte(65);",
        expect := .outputs "ok 770" }
    ]

/-! ## The completeness witness, end to end

The notation is `Langlib/Tests/URMSubleq.lean`'s: one item per line, `in`
for the input vector, then `Z`, `S`, `T`, `J`. -/

private def toks (line : String) : List String :=
  let body := match line.splitOn "#" with
    | [] => ""
    | h :: _ => h
  (body.splitOn " ").flatMap (fun t => t.splitOn "\t") |>.filter (fun t => t ≠ "")

private def parseNat (t : String) : Except String Nat :=
  match t.toNat? with
  | some n => .ok n
  | none => .error s!"not a register or label: '{t}'"

private def parseLine (line : String) :
    Except String (Option (Sum (List Nat) Instr)) := do
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

/-- Run the URM, compile the same program with the completeness witness,
render it as Ook! text, parse that text back, run it, and check that the
decoded answer is the one the machine computed. The parse step is the
round trip `OokSyntax.parse_render` proves; here it also has to
survive being run. -/
def runURM (src : String) (_input : Input) (fuel : Nat) :
    Except String RunResult := do
  let (P, inputs) ← parseURM src
  if ¬ Langlib.Computability.URM.haltsIn P (Cslib.URM.State.init inputs) urmSteps then
    .error s!"the URM program did not halt within {urmSteps} steps"
  else
    let want := Langlib.Computability.URM.result P inputs urmSteps
    let tc := Langlib.Computability.ookComplete
    let text := Langlib.Ook.render (tc.compile P inputs)
    let prog ← Langlib.Ook.parse text
    let r := Langlib.Brainfuck.evalProg {} prog (tc.encodeInput inputs) fuel
    match r.exit with
    | .halted =>
      match tc.decodeOutput r.output with
      | some got =>
        if got == want then
          return { output := s!"ok {want}".toUTF8, exit := .halted }
        else
          return { exit := .error s!"URM says {want}, compiled Ook! says {got}" }
      | none => return { exit := .error "the output did not decode" }
    | .outOfFuel =>
      return { exit := .error s!"compiled program ran out of fuel ({fuel})" }
    | .error m => return { exit := .error s!"compiled program failed: {m}" }

/-- The size of the Ook! text the completeness witness emits, so the cost
is pinned down rather than described. -/
def urmSize (src : String) (_input : Input) (_fuel : Nat) :
    Except String RunResult := do
  let (P, inputs) ← parseURM src
  let prog := Langlib.Computability.ookComplete.compile P inputs
  let text := Langlib.Ook.render prog
  return { output := s!"{text.length}".toUTF8, exit := .halted }

def urm : Suite where
  name := "urm -> ook (certified compiler)"
  run := runURM
  cases :=
    [ { name := "a constant built by increments", fuel := ookFuel,
        source := .inline "S 0\nS 0", expect := .outputs "ok 2" }
    , { name := "transfer copies an input into the answer register",
        fuel := ookFuel, source := .inline "in 0 2\nT 1 0",
        expect := .outputs "ok 2" }
    , { name := "zero clears the answer register", fuel := ookFuel,
        source := .inline "in 2\nZ 0", expect := .outputs "ok 0" }
    , { name := "addition uses a backward unconditional J", fuel := ookFuel,
        source := .inline "in 1 1\nJ 2 1 5\nS 0\nS 2\nJ 0 0 0",
        expect := .outputs "ok 2" }
    ]

def urmSizes : Suite where
  name := "urm -> ook (rendered source size)"
  run := urmSize
  cases :=
    [ { name := "two increments", source := .inline "S 0\nS 0",
        expect := .outputs "101970" }
    ]

def suites : List Suite := [compiled, reference, renderers, urm, urmSizes]

end Langlib.Tests.CompileOok
