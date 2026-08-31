import Langlib.Common.TestHarness
import Langlib.Languages.Turpentine.Compile.Malbolge
import Langlib.Languages.Malbolge.Semantics

/-!
Differential and structural tests for the Turpentine → Malbolge compiler.

Five suites, because there are five different things that can go wrong with
a backend whose target checks its own program at load time *and* has a
ceiling.

1. **Differential.** Compile the Turpentine source, load the emitted text
   with Malbolge's own loader, run it on Malbolge's own interpreter, and
   compare with what the Turpentine reference interpreter produces. The
   expected strings are Turpentine's, not the compiler's.
2. **Structure.** Two properties of the emitted file rather than of the
   run: every character is legal at its own address — checked here against
   Malbolge's `Instr.ofOpcode?` rather than against the compiler's own
   bookkeeping — and no character is one the loader would skip as
   whitespace, which would shift every address after it.
3. **Cell counts.** Pinned, because the layout is the whole design and a
   change to it should show up as a diff.
4. **Straight-line.** The image halts within a tight bound: no cell runs
   twice and nothing spins.
5. **Refusals.** The fragment boundary, one case per reason. Two of them
   are Malbolge's alone: a program whose output does not fit, and — the
   happy one — a byte above 127, which the Unshackled backend must refuse
   and this one need not, because Malbolge's `out` writes `a mod 256`.

A sixth suite runs the artifacts checked in under
`Langlib/Examples/Malbolge/compiled/`, with nothing from the compiler
involved, so that a wrong compiler and a stale artifact are separate
failures.
-/

namespace Langlib.Tests.CompileMalbolge

open Langlib.Common
open Langlib.Turpentine.Compile.Malbolge
  (compileSource compileSourceWith legalCell isSpaceCode maxCodeRow)

/-- Compile, then load and run on Malbolge's reference interpreter. -/
def run (src : String) (input : Input) (fuel : Nat) : Except String RunResult := do
  Langlib.Malbolge.run (← compileSource src) input fuel

/-- Every character of the emitted file, checked at its own address against
the loader's rule. Independent of the compiler's own `Asm.render` check: it
reads the text back the way the loader does. -/
def auditCells (src : String) (_input : Input) (_fuel : Nat) :
    Except String RunResult := do
  let text ← compileSource src
  let mut addr := 0
  for ch in text.toList do
    if isSpaceCode ch.toNat then
      throw s!"the emitted file has a whitespace character at address {addr}, \
               which the loader would skip"
    if !legalCell addr ch.toNat then
      throw s!"the character at address {addr} (code {ch.toNat}) is not \
               loadable there"
    addr := addr + 1
  return { output := "all cells loadable".toUTF8, exit := .halted }

/-- How many cells the emitted image has: one character per address, so the
length of the file in characters. -/
def cellCount (src : String) (_input : Input) (_fuel : Nat) :
    Except String RunResult := do
  let text ← compileSource src
  return { output := s!"{text.length} cells".toUTF8, exit := .halted }

/-- The emitted program is straight-line, so it halts in at most one step
per cell of the image plus the prologue's two dozen. Run at exactly that
bound, so a program that looped or spun would report out-of-fuel instead. -/
def runTight (src : String) (input : Input) (_fuel : Nat) :
    Except String RunResult := do
  let text ← compileSource src
  Langlib.Malbolge.run text input (text.length + 30)

/-- Compile with a small bound on the compile-time run, so that the
divergence case does not have to exhaust the real one. -/
def runSmallFuel (src : String) (input : Input) (fuel : Nat) :
    Except String RunResult := do
  Langlib.Malbolge.run (← compileSourceWith 20_000 src) input fuel

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
  name := "turpentine -> malbolge"
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
      -- Bytes. Malbolge's `out` writes `a mod 256`, so unlike the
      -- Unshackled backend this one reaches every byte there is.
    , { name := "every byte from 1 to 255",
        source := .inline
          "var i : int := 1; while i < 256 { printByte(i); i := i + 1; }",
        expect := .outputsBytes ⟨((List.range 255).map fun i => UInt8.ofNat (i + 1)).toArray⟩ }
    , { name := "byte zero, byte 127 and byte 255",
        source := .inline "printByte(0); printByte(127); printByte(255); println(\"|\");",
        expect := .outputsBytes ⟨#[0, 127, 255, 124, 10]⟩ }
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
      -- Whole examples. All four of the artifacts under compiled/ except
      -- the song, which is compiled afresh by scripts/gen-mal-examples.sh
      -- instead: at 28351 code cells it costs a few seconds, and the
      -- artifact suite below runs the checked-in copy for a hundredth of
      -- that. The same reasoning keeps the hand-written 99bottles.mal out
      -- of Langlib/Tests/Malbolge.lean.
    , { name := "hello example", source := ex "hello",
        expect := .outputs "Hello, Turpentine!\n" }
    , { name := "sieve example", source := ex "sieve",
        expect := .outputs "2\n3\n5\n7\n11\n13\n17\n19\n23\n29\n31\n37\n41\n43\n47\n" }
    , { name := "sum example (no output, answer only)", source := ex "sum",
        expect := .outputs "" }
    , { name := "primes-mu example", source := ex "primes-mu",
        expect := .outputs "2\n3\n5\n7\n11\n13\n17\n19\n23\n29\n" }
    , { name := "sort-mu example", source := ex "sort-mu",
        expect := .outputs "1\n2\n5\n5\n6\n9\n" }
    ]

def structureSuite : Suite where
  name := "turpentine -> malbolge (every cell loadable)"
  run := auditCells
  cases :=
    ( shared.map fun (n, src, _) =>
        { name := n, source := .inline src,
          expect := .outputs "all cells loadable" : TestCase } ) ++
    [ { name := "every byte from 1 to 255",
        source := .inline
          "var i : int := 1; while i < 256 { printByte(i); i := i + 1; }",
        expect := .outputs "all cells loadable" }
    , { name := "sieve example", source := ex "sieve",
        expect := .outputs "all cells loadable" } ]

/-- The cell counts, pinned. The image is `dataBase + n` cells for a code
row of `n`, and the compiler chooses the smallest `dataBase` its rotation
seeds offer, so both halves of the layout show up in this number. A byte
costs about one and a half crazy operations plus its `out`; a *repeated*
byte costs only the `out`, which is what the third case pins. -/
def cellCountSuite : Suite where
  name := "turpentine -> malbolge (cell counts)"
  run := cellCount
  cases :=
    [ { name := "hello", source := .inline "println(\"Hello, Turpentine!\");",
        expect := .outputs "247 cells" }
    , { name := "no output at all", source := .inline "var x : int := 6 * 7;",
        expect := .outputs "146 cells" }
    , { name := "one repeated byte costs one cell, not two",
        source := .inline "print(\"aaaa\");",
        expect := .outputs "161 cells" }
    ]

def tightSuite : Suite where
  name := "turpentine -> malbolge (straight-line, tight fuel)"
  run := runTight
  cases :=
    ( shared.map fun (n, src, want) =>
        { name := n, source := .inline src, expect := .outputs want : TestCase } ) ++
    [ { name := "sieve example", source := ex "sieve",
        expect := .outputs "2\n3\n5\n7\n11\n13\n17\n19\n23\n29\n31\n37\n41\n43\n47\n" } ]

def refusalSuite : Suite where
  name := "turpentine -> malbolge (the fragment boundary)"
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
      -- Malbolge's own refusal, and the only one in the library that a
      -- better compiler could not lift: 25592 bytes of output against a
      -- machine with room for a code row of 29157 cells.
    , { name := "refuses output that does not fit in 59049 words",
        source := .inline
          "var i : int; while i < 3000 { println(i * 7919); i := i + 1; }",
        expect := .parseError "does not have room for them" }
    , { name := "the refusal says how much of the output did fit",
        source := .inline
          "var i : int; while i < 3000 { println(i * 7919); i := i + 1; }",
        expect := .parseError "the first 15191 bytes" }
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

/-- The compiled examples under `Langlib/Examples/Malbolge/compiled/` are
derived files: `scripts/gen-mal-examples.sh` is the only thing that may
write them, and `--check` is what catches a stale one. These cases check the
other half — that the file in the tree really is a Malbolge program that
runs and prints what its Turpentine source prints — by loading it with
Malbolge's own loader and running it on Malbolge's own interpreter, with
nothing from the compiler involved.

The differential suite above compiles four of the same sources afresh, so
between the two a wrong compiler and a wrong artifact are separate
failures. `compiled/99bottles.mal` is the fifth artifact and the only one
this suite runs without a fresh-compile counterpart; at 57514 cells it is
97% of the machine, and it is here because it is the demonstration. -/
def compiledSuite : Suite where
  name := "malbolge compiled examples"
  run := Langlib.Malbolge.run
  cases :=
    [ { name := "compiled/hello.mal",
        source := .file "Langlib/Examples/Malbolge/compiled/hello.mal",
        expect := .outputs "Hello, Turpentine!\n" }
    , { name := "compiled/sieve.mal",
        source := .file "Langlib/Examples/Malbolge/compiled/sieve.mal",
        expect := .outputs "2\n3\n5\n7\n11\n13\n17\n19\n23\n29\n31\n37\n41\n43\n47\n" }
    , { name := "compiled/primes.mal",
        source := .file "Langlib/Examples/Malbolge/compiled/primes.mal",
        expect := .outputs "2\n3\n5\n7\n11\n13\n17\n19\n23\n29\n" }
    , { name := "compiled/sort.mal",
        source := .file "Langlib/Examples/Malbolge/compiled/sort.mal",
        expect := .outputs "1\n2\n5\n5\n6\n9\n" }
    , { name := "compiled/hello.mal ignores the input stream",
        source := .file "Langlib/Examples/Malbolge/compiled/hello.mal",
        input := "99\n", expect := .outputs "Hello, Turpentine!\n" }
    ]

/-- Run, and report the output's length and a checksum rather than its text.
The song is 11459 bytes and has no business being quoted in a Lean source
file; a length and a rolling checksum pin it just as tightly.

`scripts/gen-mal-examples.sh` makes the stronger check that this cannot:
that the artifact's output is *identical* to what `turpentine run` prints
for the source. -/
def digest (src : String) (input : Input) (fuel : Nat) :
    Except String RunResult := do
  let r ← Langlib.Malbolge.run src input fuel
  let bs := r.output.toList
  let sum := bs.foldl (fun n b => (n * 31 + b.toNat) % 1000003) 7
  return { r with output := s!"{bs.length} bytes, checksum {sum}".toUTF8 }

/-- The song, which is why this backend exists: 11459 bytes out of a machine
that provably cannot loop for ever, from an image of 57514 cells — 97% of
Malbolge's memory. Straight-line, so it costs one step per code cell and
runs in a hundredth of a second, which is why it is affordable here where
compiling it afresh would not be.

The second case is the one worth looking at. It is not a compiled artifact
at all: it is `99bottles.mal`, the 2005 hand-written song by Iizawa,
Sakabe, Sakai, Kusakari and Nishida — the first Malbolge program with real
loops and conditionals, twenty million machine cycles of them. It is here
because it produces **the same digest**, and two identical digests in the
same report is how a pure test harness says that a compiler which unrolls
every loop at compile time and an author who wrote the loops out by hand
arrived at the same 11459 bytes. -/
def songSuite : Suite where
  name := "malbolge: the whole song, compiled and hand-written"
  run := digest
  cases :=
    [ { name := "compiled/99bottles.mal (57514 cells, straight-line)",
        source := .file "Langlib/Examples/Malbolge/compiled/99bottles.mal",
        expect := .outputs "11459 bytes, checksum 788446" }
    , { name := "99bottles.mal (hand-written, with real loops) agrees byte for byte",
        source := .file "Langlib/Examples/Malbolge/99bottles.mal",
        expect := .outputs "11459 bytes, checksum 788446" }
    ]

/-- The ceiling itself, as a number rather than as prose: the longest code
row Malbolge has room for. Every refusal in the backend is measured against
it, and `docs/malbolge/compiler.md` quotes it. -/
example : maxCodeRow = 29157 := by native_decide

def suites : List Suite :=
  [suite, structureSuite, cellCountSuite, tightSuite, refusalSuite, compiledSuite,
   songSuite]

end Langlib.Tests.CompileMalbolge
