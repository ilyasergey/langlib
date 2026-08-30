import Langlib.Common.TestHarness
import Langlib.Languages.Turpentine.Compile.MalbolgeUnshackled
import Langlib.Languages.MalbolgeUnshackled.Semantics

/-!
Differential and structural tests for the Turpentine → Malbolge Unshackled
compiler.

Four suites, because there are four different things that can go wrong with
a backend whose target checks its own program at load time.

1. **Differential.** Compile the Turpentine source, load the emitted text
   with Unshackled's own loader, run it on Unshackled's own interpreter, and
   compare with what the Turpentine reference interpreter produces. The
   expected strings are Turpentine's, not the compiler's.
2. **Rotation width.** The language leaves the starting rotation width to
   the implementation, and Johansen's interpreter randomises it precisely so
   that a program which depends on it fails on some runs. This backend emits
   no `*`, so its programs should be *insensitive* to the width; the suite
   runs each one at seven settings from 10 to 300 and passes only if all
   seven agree.
3. **Structure.** Two properties of the emitted file rather than of the run:
   every character is legal at its own address (checked here against
   Unshackled's `Instr.ofOpcode?`, not against the compiler's own
   bookkeeping), and the program halts within `3 + n` steps for an `n`-cell
   image, which is what "straight-line" means — no cell runs twice and
   nothing spins.
4. **Refusals.** The fragment boundary, one case per reason, each checked by
   the message it produces.
-/

namespace Langlib.Tests.CompileMalbolgeUnshackled

open Langlib.Common
open Langlib.Turpentine.Compile.MalbolgeUnshackled
  (compileSource compileSourceWith legalCell)

/-- Compile, then load and run on Unshackled's reference interpreter. -/
def run (src : String) (input : Input) (fuel : Nat) : Except String RunResult := do
  Langlib.MalbolgeUnshackled.run (← compileSource src) input fuel

/-- The starting rotation widths the second suite sweeps. 10 is the least
the language allows; Johansen's interpreter draws from 10..15; the large
ones are legal and absurd, which is the point. -/
def widths : List Nat := [10, 11, 12, 13, 15, 64, 300]

/-- Compile once, run at every width in `widths`, and report the common
output — so a case in this suite checks both that the runs agree and that
they agree on the right thing. -/
def runWidths (src : String) (input : Input) (fuel : Nat) :
    Except String RunResult := do
  let text ← compileSource src
  let first := Langlib.MalbolgeUnshackled.evalImage
    { rotWidth := 10 } (← Langlib.MalbolgeUnshackled.load text) input fuel
  for w in widths do
    let img ← Langlib.MalbolgeUnshackled.load text
    let r := Langlib.MalbolgeUnshackled.evalImage { rotWidth := w } img input fuel
    if r.exit != first.exit then
      throw s!"rotation width {w} changes the exit: {repr r.exit} vs {repr first.exit}"
    if r.output != first.output then
      throw s!"rotation width {w} changes the output"
  return first

/-- Every character of the emitted file, checked at its own address against
the loader's rule. Independent of the compiler's own `Asm.render` check: it
reads the text back the way the loader does. -/
def auditCells (src : String) (_input : Input) (_fuel : Nat) :
    Except String RunResult := do
  let text ← compileSource src
  let mut addr := 0
  for ch in text.toList do
    if Langlib.MalbolgeUnshackled.isSpaceChar ch then
      throw s!"the emitted file has a whitespace character at address {addr}, \
               which the loader would skip"
    if !legalCell addr ch.toNat then
      throw s!"the character at address {addr} (code {ch.toNat}) is not \
               loadable there"
    addr := addr + 1
  return { output := "all cells loadable".toUTF8, exit := .halted }

/-- How many cells the emitted image has: one character per address, so the
length of the file in characters. Pinned for a few programs, because it is
the clearest single number describing the layout. -/
def cellCount (src : String) (_input : Input) (_fuel : Nat) :
    Except String RunResult := do
  let text ← compileSource src
  return { output := s!"{text.length} cells".toUTF8, exit := .halted }

/-- The emitted program is straight-line: it halts within `3 + n` steps of
an `n`-cell image (three for the prologue, one per code cell, and the code
row is shorter than the image). Run at exactly that bound, so a program that
looped or spun would report out-of-fuel instead. -/
def runTight (src : String) (input : Input) (_fuel : Nat) :
    Except String RunResult := do
  let text ← compileSource src
  Langlib.MalbolgeUnshackled.run text input (text.length + 4)

/-- The data cells are characters outside `33..126`, which the loader stores
unchecked by default and rejects with `--strict` (Johansen's `-n`). Both
halves are a property of the emitted file worth pinning down. -/
def strictRejects (src : String) (_input : Input) (_fuel : Nat) :
    Except String RunResult := do
  let text ← compileSource src
  match Langlib.MalbolgeUnshackled.runWith { strict := true } text Input.empty 1000 with
  | .error _ => return { output := "strict rejects the data cells".toUTF8, exit := .halted }
  | .ok _ => throw "the strict loader accepted the emitted program"

/-- Compile with a small bound on the compile-time run, so that the
divergence case does not have to exhaust the real one. -/
def runSmallFuel (src : String) (input : Input) (fuel : Nat) :
    Except String RunResult := do
  Langlib.MalbolgeUnshackled.run (← compileSourceWith 20_000 src) input fuel

private def ex (f : String) : Source :=
  .file s!"Langlib/Examples/Turpentine/{f}.turp"

/-- Sources used by more than one suite: each is a `(name, program,
expected output)` triple, so the structural suites can reuse the
differential suite's programs without repeating them. -/
def shared : List (String × String × String) :=
  [ ("string literal", "println(\"Hello, Turpentine!\");", "Hello, Turpentine!\n")
  , ("decimal printing", "println(0); println(1000); println(-31337);",
     "0\n1000\n-31337\n")
  , ("repeated bytes", "println(\"aaabbbccc\");", "aaabbbccc\n")
  , ("no output at all", "var x : int := 6 * 7;", "")
  , ("a bool array and a loop",
     "var b : bool[4]; var i : int; b[2] := true;\n\
      while i < len(b) { if b[i] { print(\"T\"); } else { print(\".\"); } i := i + 1; }\n\
      println();",
     "..T.\n") ]

def suite : Suite where
  name := "turpentine -> malbolge-unshackled"
  run := run
  cases :=
    ( shared.map fun (n, src, want) =>
        { name := n, source := .inline src, expect := .outputs want : TestCase } ) ++
    [ -- Strings and escapes
      { name := "string escapes",
        source := .inline "print(\"a\\tb\\n\"); println(\"\\\"q\\\\\\\"\");",
        expect := .outputs "a\tb\n\"q\\\"\n" }
    , { name := "bare newline and print without one",
        source := .inline "print(1); print(2); println(); println(3);",
        expect := .outputs "12\n3\n" }
      -- Decimal rendering, the accumulator's main workout
    , { name := "printint across digit boundaries",
        source := .inline
          "println(9); println(10); println(99); println(100); println(1000);",
        expect := .outputs "9\n10\n99\n100\n1000\n" }
    , { name := "printint on negatives",
        source := .inline "println(-1); println(-1000000);",
        expect := .outputs "-1\n-1000000\n" }
    , { name := "booleans",
        source := .inline "println(true); println(1 < 2); println(2 <= 1);",
        expect := .outputs "true\ntrue\nfalse\n" }
      -- Bytes: the accumulator has to reach every code point below 128
    , { name := "every byte from 1 to 127",
        source := .inline
          "var i : int := 1; while i < 128 { printByte(i); i := i + 1; }",
        expect := .outputsBytes ⟨((List.range 127).map fun i => UInt8.ofNat (i + 1)).toArray⟩ }
    , { name := "byte zero and byte 127",
        source := .inline "printByte(0); printByte(127); println(\"|\");",
        expect := .outputsBytes ⟨#[0, 127, 124, 10]⟩ }
    , { name := "printByte reduces mod 256 the way Turpentine does",
        source := .inline "printByte(65 + 256); printByte(-191); println();",
        expect := .outputs "AA\n" }
      -- Arithmetic, all of it resolved at compile time
    , { name := "euclidean division and remainder",
        source := .inline
          "println(7 / 2); println(-7 / 2); println(7 % 3); println(-7 % 3);",
        expect := .outputs "3\n-4\n1\n2\n" }
    , { name := "short-circuit and nested if",
        source := .inline
          "var x : int := 0;\n\
           if x == 0 || 1 / x == 1 { println(\"safe\"); } else { println(\"no\"); }",
        expect := .outputs "safe\n" }
    , { name := "assert that holds",
        source := .inline "var x : int := 4; assert x * x == 16; println(\"ok\");",
        expect := .outputs "ok\n" }
      -- Arrays, including a computed index
    , { name := "an int array with computed indices",
        source := .inline
          "var a : int[5]; var i : int;\n\
           while i < len(a) { a[i] := i * i; i := i + 1; }\n\
           println(a[len(a) - 1]); println(a[2 + 1]);",
        expect := .outputs "16\n9\n" }
      -- Whole examples
    , { name := "hello example", source := ex "hello",
        expect := .outputs "Hello, Turpentine!\n" }
    , { name := "sieve example", source := ex "sieve",
        expect := .outputs "2\n3\n5\n7\n11\n13\n17\n19\n23\n29\n31\n37\n41\n43\n47\n" }
    , { name := "sum example (no output, answer only)", source := ex "sum",
        expect := .outputs "" }
    ]

def widthSuite : Suite where
  name := "turpentine -> malbolge-unshackled (rotation width)"
  run := runWidths
  cases :=
    ( shared.map fun (n, src, want) =>
        { name := n, source := .inline src, expect := .outputs want : TestCase } ) ++
    [ { name := "sieve example", source := ex "sieve",
        expect := .outputs "2\n3\n5\n7\n11\n13\n17\n19\n23\n29\n31\n37\n41\n43\n47\n" } ]

def structureSuite : Suite where
  name := "turpentine -> malbolge-unshackled (every cell loadable)"
  run := auditCells
  cases :=
    ( shared.map fun (n, src, _) =>
        { name := n, source := .inline src,
          expect := .outputs "all cells loadable" : TestCase } ) ++
    [ { name := "every byte from 1 to 127",
        source := .inline
          "var i : int := 1; while i < 128 { printByte(i); i := i + 1; }",
        expect := .outputs "all cells loadable" }
    , { name := "sieve example", source := ex "sieve",
        expect := .outputs "all cells loadable" } ]

/-- The cell counts, pinned. A change to the layout or to the accumulator
accounting shows up here as a diff, which is the point. The image is
`194 + 2n` cells for a code row of `n` (the data row is the same length, and
194 is the prologue, its two tables and the gap between the rows), and the
code row is three cells per new output byte, one per repeated byte, plus the
closing `halt`. -/
def cellCountSuite : Suite where
  name := "turpentine -> malbolge-unshackled (cell counts)"
  run := cellCount
  cases :=
    [ { name := "hello", source := .inline "println(\"Hello, Turpentine!\");",
        expect := .outputs "306 cells" }
    , { name := "no output at all", source := .inline "var x : int := 6 * 7;",
        expect := .outputs "196 cells" }
    , { name := "one repeated byte costs one cell, not three",
        source := .inline "print(\"aaaa\");",
        expect := .outputs "208 cells" }
    ]

def tightSuite : Suite where
  name := "turpentine -> malbolge-unshackled (straight-line, tight fuel)"
  run := runTight
  cases :=
    ( shared.map fun (n, src, want) =>
        { name := n, source := .inline src, expect := .outputs want : TestCase } ) ++
    [ { name := "sieve example", source := ex "sieve",
        expect := .outputs "2\n3\n5\n7\n11\n13\n17\n19\n23\n29\n31\n37\n41\n43\n47\n" } ]

def strictSuite : Suite where
  name := "turpentine -> malbolge-unshackled (the loader's strict mode)"
  run := strictRejects
  cases :=
    [ { name := "hello", source := .inline "println(\"Hello, Turpentine!\");",
        expect := .outputs "strict rejects the data cells" }
    , { name := "no output at all", source := .inline "var x : int := 6 * 7;",
        expect := .outputs "strict rejects the data cells" } ]

def refusalSuite : Suite where
  name := "turpentine -> malbolge-unshackled (the fragment boundary)"
  run := runSmallFuel
  cases :=
    [ { name := "refuses readInt",
        source := .inline "var x : int; x := readInt(); println(x);",
        expect := .parseError "do not read input" }
    , { name := "refuses readByte",
        source := .inline "var b : int; b := readByte(); printByte(b);",
        expect := .parseError "do not read input" }
    , { name := "refuses readInt into an array element",
        source := .inline "var a : int[2]; a[0] := readInt();",
        expect := .parseError "do not read input" }
    , { name := "refuses a read buried in a loop",
        source := .inline
          "var i : int; var b : int;\n\
           while i < 3 { if i == 1 { b := readByte(); } i := i + 1; }",
        expect := .parseError "do not read input" }
    , { name := "refuses a program that does not halt",
        source := .inline "var i : int := 0; while true { i := i + 1; }",
        expect := .parseError "did not halt within 20000 steps" }
    , { name := "refuses a byte above 127",
        source := .inline "printByte(200);",
        expect := .parseError "byte above 127" }
    , { name := "refuses a program that traps",
        source := .inline "var a : int[2]; println(a[5]);",
        expect := .parseError "out of bounds" }
    , { name := "refuses a failing assertion",
        source := .inline "assert 1 == 2;",
        expect := .parseError "assertion failed" }
    , { name := "refuses a program that does not type-check",
        source := .inline "var x : bool; x := 1;",
        expect := .parseError "type error" }
    , { name := "refuses a program that does not parse",
        source := .inline "println(1)",
        expect := .parseError "expected ';'" }
    ]

def suites : List Suite :=
  [suite, widthSuite, structureSuite, cellCountSuite, tightSuite, strictSuite,
   refusalSuite]

end Langlib.Tests.CompileMalbolgeUnshackled
