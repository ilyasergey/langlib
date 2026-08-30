import Langlib.Common.TestHarness
import Langlib.Languages.Turpentine.Semantics
import Langlib.Languages.Turpentine.Compile.Brainloller
import Langlib.Computability.Brainloller

/-!
# Compiler tests: Turpentine to Brainloller

Four things are checked here.

* **Differential**, `compiled` against `reference`: every case in `shared`
  is run twice, once by `Langlib.Turpentine.run` and once by
  `Langlib.Turpentine.Compile.Brainloller.runCompiled`, which compiles to
  brainfuck, paints the result as an image, writes that image as ASCII PPM
  *text*, reads the text back with `Langlib.Common.Image.parsePpm`, walks
  the pixels, and runs the recovered program on the brainfuck core with
  the EOF convention the generated code targets. So each expected string
  is both a golden test of the reference interpreter and a claim that the
  compiler preserved its behaviour through a full round trip of the
  concrete syntax, image file included. Every expected string was taken
  from a run of the reference interpreter first.

* **The pixel walk**, `walks`: this is the one link of the round trip
  `Langlib/Computability/Brainloller.lean` does *not* prove, so it is the
  one the tests have to carry. Each case compiles a program, paints it at
  a given row width, decodes the image back to characters, and checks the
  characters are exactly the rendered brainfuck. Widths 3 (the narrowest
  legal serpentine), 8, 64 (the compiler's default) and 0 (a single row)
  are covered.

* **Renderer agreement**, `renderers`: `Langlib.Brainfuck.Prog.render`
  routes through a `partial def`, which Lean compiles to an opaque
  constant, so no theorem can mention it.
  `Langlib.Computability.BrainlollerSyntax.renderBf` is a total
  re-implementation and is the renderer `parse_renderBf` is proved about.
  This suite checks the two agree byte-for-byte on the programs the
  backend actually emits.

* **Completeness**, `urm`: small URM programs compiled with
  `brainlollerComplete.compile`, painted, decoded, run, and the answer
  decoded. The programs are tiny and the fuel is generous because the
  compiled output is huge by design.

Inputs are small on purpose. A compiled image is one pixel per brainfuck
command, and its ASCII PPM file is about nine bytes per pixel
(`docs/brainloller/compiler.md` has the numbers), so the examples here are
the cheap ones.
-/

namespace Langlib.Tests.CompileBrainloller

open Langlib.Common
open Cslib.URM (Program Instr)

private def ex (f : String) : Source :=
  .file s!"Langlib/Examples/Turpentine/{f}"

/-- The fuel the compiled programs get, matching the brainfuck backend's
own suite. -/
private def blFuel : Nat := 200_000_000

/-- Cases that both the reference interpreter and the compiled image must
satisfy. -/
def shared : List TestCase :=
  [ { name := "hello example", source := ex "hello.turp", fuel := blFuel,
      expect := .outputs "Hello, Turpentine!\n" }
  , { name := "cat example", source := ex "cat.turp", input := "meow\n",
      fuel := blFuel, expect := .outputs "meow\n" }
  , { name := "isqrt example (16)", source := ex "isqrt.turp", input := "16\n",
      fuel := blFuel, expect := .outputs "4\n" }
  , { name := "sumdigits example (405)", source := ex "sumdigits.turp",
      input := "405\n", fuel := blFuel, expect := .outputs "9\n" }
  , { name := "gcd example", source := ex "gcd.turp", input := "252\n105\n",
      fuel := blFuel, expect := .outputs "21\n" }
  , { name := "collatz example (6)", source := ex "collatz.turp", input := "6\n",
      fuel := blFuel, expect := .outputs "8\n" }
  , { name := "arithmetic", fuel := blFuel, source := .inline
        "println(6 * 7); println(100 / 7); println(100 % 7);",
      expect := .outputs "42\n14\n2\n" }
  , { name := "nested while", fuel := blFuel, source := .inline
        ("var i : int := 1; var j : int; while i <= 3 { j := 1; "
          ++ "while j <= i { printByte(48 + j); j := j + 1; } "
          ++ "printByte(10); i := i + 1; }"),
      expect := .outputs "1\n12\n123\n" }
  , { name := "array element write and read", fuel := blFuel, source := .inline
        ("var a : int[3]; a[0] := 7; a[2] := -5; "
          ++ "println(a[0]); println(a[1]); println(a[2]);"),
      expect := .outputs "7\n0\n-5\n" }
  ]

/-- The compiled programs, as ASCII PPM text, run through the Brainloller
front end. -/
def compiled : Suite where
  name := "turpentine -> brainloller"
  run := Langlib.Turpentine.Compile.Brainloller.runCompiled
  cases := shared

/-- The same cases on the reference interpreter: one expected string, two
independent machines. -/
def reference : Suite where
  name := "turpentine -> brainloller (reference cross-check)"
  run := Langlib.Turpentine.run
  cases := shared

/-! ## The pixel walk

`decode (encode s w)` recovering `s`'s command characters is the link the
Lean development leaves open; these cases are what stands in for it. The
expected string reports the image dimensions, so a change in the layout
shows up as a diff rather than as a silent pass. -/

private def walkAt (width : Nat) (src : String) : Except String RunResult := do
  let prog ← Langlib.Turpentine.parse src
  let bf ← Langlib.Turpentine.Compile.Brainloller.compileProg prog
  let text := Langlib.Computability.BrainlollerSyntax.renderBf bf
  let img := Langlib.Brainloller.encode text width
  let got ← Langlib.Brainloller.decode img
  if got == text then
    return { output := s!"ok {img.width}x{img.height}".toUTF8, exit := .halted }
  else
    let msg := s!"walk lost commands ({got.length} of {text.length} recovered)"
    return { exit := .error msg }

def walks : Suite where
  name := "turpentine -> brainloller (the pixel walk recovers the commands)"
  run := fun src _ _ => walkAt 64 src
  cases :=
    [ { name := "hello at the default width 64", source := ex "hello.turp",
        expect := .outputs "ok 64x8" }
    , { name := "cat at the default width 64", source := ex "cat.turp",
        expect := .outputs "ok 64x442" }
    ]

def walksNarrow : Suite where
  name := "turpentine -> brainloller (width 3, the narrowest serpentine)"
  run := fun src _ _ => walkAt 3 src
  cases :=
    [ { name := "hello at width 3", source := ex "hello.turp",
        expect := .outputs "ok 3x458" }
    , { name := "one statement at width 3", source := .inline "printByte(65);",
        expect := .outputs "ok 3x75" }
    ]

def walksWide : Suite where
  name := "turpentine -> brainloller (width 8 and a single row)"
  run := fun src _ _ => walkAt 8 src
  cases :=
    [ { name := "hello at width 8", source := ex "hello.turp",
        expect := .outputs "ok 8x77" }
    ]

def walksSingleRow : Suite where
  name := "turpentine -> brainloller (a single row)"
  run := fun src _ _ => walkAt 0 src
  cases :=
    [ { name := "hello on one row", source := ex "hello.turp",
        expect := .outputs "ok 460x1" }
    , { name := "one statement on one row", source := .inline "printByte(65);",
        expect := .outputs "ok 77x1" }
    ]

/-- Compile, then compare the shipped brainfuck renderer with the proved
one. -/
def renderAgrees (src : String) (_input : Input) (_fuel : Nat) :
    Except String RunResult := do
  let prog ← Langlib.Turpentine.parse src
  let bf ← Langlib.Turpentine.Compile.Brainloller.compileProg prog
  let shipped := Langlib.Brainfuck.Prog.render bf
  let proved := Langlib.Computability.BrainlollerSyntax.renderBf bf
  if shipped == proved then
    return { output := s!"ok {shipped.length}".toUTF8, exit := .halted }
  else
    let msg := s!"renderers disagree ({shipped.length} vs {proved.length} bytes)"
    return { exit := .error msg }

def renderers : Suite where
  name := "turpentine -> brainloller (shipped renderer = proved renderer)"
  run := renderAgrees
  cases :=
    [ { name := "hello example", source := ex "hello.turp",
        expect := .outputs "ok 460" }
    , { name := "cat example", source := ex "cat.turp",
        expect := .outputs "ok 27376" }
    , { name := "the empty program", source := .inline "",
        expect := .outputs "ok 0" }
    , { name := "one statement", source := .inline "printByte(65);",
        expect := .outputs "ok 77" }
    ]

/-! ## The completeness witness, end to end -/

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
paint it at the compiler's default width, walk the image back to a
program, run it, and check that the decoded answer is the one the machine
computed. -/
def runURM (src : String) (_input : Input) (fuel : Nat) :
    Except String RunResult := do
  let (P, inputs) ← parseURM src
  if ¬ Langlib.Computability.URM.haltsIn P (Cslib.URM.State.init inputs) urmSteps then
    .error s!"the URM program did not halt within {urmSteps} steps"
  else
    let want := Langlib.Computability.URM.result P inputs urmSteps
    let tc := Langlib.Computability.brainlollerComplete
    let text := Langlib.Computability.BrainlollerSyntax.renderBf (tc.compile P inputs)
    let img := Langlib.Brainloller.encode text
      Langlib.Turpentine.Compile.Brainloller.defaultWidth
    let prog ← Langlib.Brainloller.decodeProg img
    let r := Langlib.Brainfuck.evalProg {} prog (tc.encodeInput inputs) fuel
    match r.exit with
    | .halted =>
      match tc.decodeOutput r.output with
      | some got =>
        if got == want then
          return { output := s!"ok {want}".toUTF8, exit := .halted }
        else
          let msg := s!"URM says {want}, compiled Brainloller says {got}"
          return { exit := .error msg }
      | none => return { exit := .error "the output did not decode" }
    | .outOfFuel =>
      return { exit := .error s!"compiled program ran out of fuel ({fuel})" }
    | .error m => return { exit := .error s!"compiled program failed: {m}" }

/-- The size of the image the completeness witness emits, so the cost is
pinned down rather than described. -/
def urmSize (src : String) (_input : Input) (_fuel : Nat) :
    Except String RunResult := do
  let (P, inputs) ← parseURM src
  let prog := Langlib.Computability.brainlollerComplete.compile P inputs
  let text := Langlib.Computability.BrainlollerSyntax.renderBf prog
  let img := Langlib.Brainloller.encode text
    Langlib.Turpentine.Compile.Brainloller.defaultWidth
  return { output := s!"{img.width}x{img.height}".toUTF8, exit := .halted }

def urm : Suite where
  name := "urm -> brainloller (certified compiler)"
  run := runURM
  cases :=
    [ { name := "a constant built by increments", fuel := blFuel,
        source := .inline "S 0\nS 0", expect := .outputs "ok 2" }
    , { name := "transfer copies an input into the answer register",
        fuel := blFuel, source := .inline "in 0 2\nT 1 0",
        expect := .outputs "ok 2" }
    , { name := "zero clears the answer register", fuel := blFuel,
        source := .inline "in 2\nZ 0", expect := .outputs "ok 0" }
    , { name := "addition uses a backward unconditional J", fuel := blFuel,
        source := .inline "in 1 1\nJ 2 1 5\nS 0\nS 2\nJ 0 0 0",
        expect := .outputs "ok 2" }
    ]

def urmSizes : Suite where
  name := "urm -> brainloller (image size)"
  run := urmSize
  cases :=
    [ { name := "two increments", source := .inline "S 0\nS 0",
        expect := .outputs "64x165" }
    ]

def suites : List Suite :=
  [compiled, reference, walks, walksNarrow, walksWide, walksSingleRow,
   renderers, urm, urmSizes]

end Langlib.Tests.CompileBrainloller
