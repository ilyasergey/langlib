import Langlib.Common.TestHarness
import Langlib.Languages.Turpentine.Semantics
import Langlib.Languages.Turpentine.Compile.Brainfuck
import Langlib.Languages.Turpentine.Compile.Whitespace
import Langlib.Languages.Turpentine.Compile.Subleq
import Langlib.Languages.Turpentine.Compile.Ook
import Langlib.Languages.Turpentine.Compile.Brainloller
import Langlib.Languages.Turpentine.Compile.Piet
import Langlib.Languages.Whitespace.Semantics
import Langlib.Languages.Subleq.Semantics

/-!
# The conformance suite

Twenty Turpentine programs in `Langlib/Examples/Turpentine/suite/`, each
with one expected output, run against every way LangLib has of executing
them. The point is that the expected output is written down *once* and
every language in the library has to agree with it.

A program qualifies for this suite if it **reads no input**. That is what
makes the suite runnable without a harness that feeds stdin, and it is why
`cat`-shaped programs live in the per-language example folders instead.
Every program does print, because a run nobody can observe proves nothing.

Two kinds of runner are registered here.

* **Compiled**: the Turpentine source through each bespoke backend, run on
  that target's own reference interpreter. Five of those today
  (`docs/conformance.md` has the table), so a program that behaves
  differently on one backend fails exactly one suite and names it.
* **Hand-written**: the same program written directly in the target
  language by a person, run on the same interpreter against the same
  expected output. These live in `Langlib/Examples/<Langname>/suite/` and
  are registered in `Langlib/Tests/ConformanceHand.lean`.

The difference between the two matters. A compiled program tests the
compiler; a hand-written one tests the *interpreter*, because it was
written against the language as documented rather than against whatever
the backend happens to emit. Where both exist, they are two independent
implementations of one specification.

Expected outputs were captured by running the reference interpreter, never
guessed, and every one of them was checked against all five backends
before being written down.
-/

namespace Langlib.Tests.Conformance

open Langlib.Common

/-- One conformance program: its file name, a one-line note on what it is
for, and the output every implementation must produce. -/
structure Prog where
  name : String
  about : String
  output : String

/-- The suite. Keep this list and `docs/conformance.md` in step. -/
def programs : List Prog :=
  [ ⟨"hello", "the smallest observable program",
      "Hello, World!\n"⟩
  , ⟨"count", "a counted loop and multi-digit decimals",
      "1\n2\n3\n4\n5\n6\n7\n8\n9\n10\n"⟩
  , ⟨"fizzbuzz", "modulo and an else-if chain",
      "1\n2\nFizz\n4\nBuzz\nFizz\n7\n8\nFizz\nBuzz\n11\nFizz\n13\n14\nFizzBuzz\n16\n17\nFizz\n19\nBuzz\n"⟩
  , ⟨"fib", "two accumulators updated in step",
      "0\n1\n1\n2\n3\n5\n8\n13\n21\n34\n55\n89\n"⟩
  , ⟨"fact", "repeated multiplication, up to 5040",
      "1\n1\n2\n6\n24\n120\n720\n5040\n"⟩
  , ⟨"gcd", "Euclid, four pairs, data-dependent inner loop",
      "21\n21\n1\n30\n"⟩
  , ⟨"primes", "trial division, doubly nested",
      "2\n3\n5\n7\n11\n13\n17\n19\n23\n29\n"⟩
  , ⟨"sieve", "a 50-cell array written at a computed index",
      "2\n3\n5\n7\n11\n13\n17\n19\n23\n29\n31\n37\n41\n43\n47\n"⟩
  , ⟨"collatz", "alternating branches, data-dependent length",
      "0\n1\n7\n2\n5\n8\n16\n3\n19\n6\n"⟩
  , ⟨"isqrt", "counting up until the square passes",
      "0\n1\n3\n4\n4\n14\n"⟩
  , ⟨"sumdigits", "division and modulo by ten",
      "0\n7\n18\n25\n"⟩
  , ⟨"power", "doubling to 16384, the widest value here",
      "1\n2\n4\n8\n16\n32\n64\n128\n256\n512\n1024\n2048\n4096\n8192\n16384\n"⟩
  , ⟨"triangle", "byte output and a variable-length inner loop",
      "*\n**\n***\n****\n*****\n"⟩
  , ⟨"sort", "insertion sort: computed index on both sides",
      "0\n1\n2\n5\n5\n6\n7\n9\n"⟩
  , ⟨"maxelem", "one pass, three accumulators",
      "1\n9\n31\n"⟩
  , ⟨"binary", "an array used as a stack",
      "0\n1\n101\n1000000\n1111101000\n"⟩
  , ⟨"multtable", "nested loops printing in both",
      "1\t2\t3\t4\t5\n2\t4\t6\t8\t10\n3\t6\t9\t12\t15\n4\t8\t12\t16\t20\n5\t10\t15\t20\t25\n"⟩
  , ⟨"bottles", "the most text, and a singular/plural branch",
      "3 bottles of beer on the wall,\n3 bottles of beer.\nTake one down, pass it around,\n2 bottles of beer on the wall.\n\n2 bottles of beer on the wall,\n2 bottles of beer.\nTake one down, pass it around,\n1 bottle of beer on the wall.\n\n1 bottle of beer on the wall,\n1 bottle of beer.\nTake one down, pass it around,\n0 bottles of beer on the wall.\n\n"⟩
  , ⟨"divmod", "Euclidean division at all four sign pairs",
      "3\n2\n-4\n3\n-3\n2\n4\n3\n"⟩
  , ⟨"logic", "every boolean and comparison operator",
      "true\nfalse\nfalse\ntrue\nfalse\ntrue\nfalse\ntrue\nfalse\ntrue\ntrue\n"⟩  ]

/-- Fuel for the compiled runs. A compiled program takes many target steps
per Turpentine statement, and the reference interpreter is happy to be
handed the same number. -/
def fuel : Nat := 2_000_000_000

/-- Turn the program list into cases for one runner. -/
def cases (dir : String) (ext : String) : List TestCase :=
  programs.map fun p =>
    { name := p.name
      source := .file s!"Langlib/Examples/{dir}/suite/{p.name}.{ext}"
      expect := .outputs p.output
      fuel := fuel }

/-- The programs on the Turpentine reference interpreter. Every other suite
in the library is measured against this one. -/
def reference : Suite where
  name := "conformance: turpentine (reference)"
  run := Langlib.Turpentine.run
  cases := cases "Turpentine" "turp"

private def viaBrainfuck (src : String) (i : Input) (n : Nat) :
    Except String RunResult :=
  Langlib.Turpentine.Compile.Brainfuck.runCompiled src i n

private def viaWhitespace (src : String) (i : Input) (n : Nat) :
    Except String RunResult := do
  let text ← Langlib.Turpentine.Compile.Whitespace.compileSource src
  Langlib.Whitespace.run text i n

private def viaSubleq (src : String) (i : Input) (n : Nat) :
    Except String RunResult := do
  let text ← Langlib.Turpentine.Compile.Subleq.compileSource src
  Langlib.Subleq.run text i n

private def viaOok (src : String) (i : Input) (n : Nat) :
    Except String RunResult :=
  Langlib.Turpentine.Compile.Ook.runCompiled src i n

private def viaBrainloller (src : String) (i : Input) (n : Nat) :
    Except String RunResult :=
  Langlib.Turpentine.Compile.Brainloller.runCompiled src i n

/-- Piet compiles to a picture, so this one goes out through
`Grid.toImage` and comes back through Piet's own PPM parser rather than
running the grid the code generator built. -/
private def viaPiet (src : String) (i : Input) (n : Nat) :
    Except String RunResult :=
  Langlib.Turpentine.Compile.Piet.runCompiled src i n

def compiledBrainfuck : Suite where
  name := "conformance: compiled to brainfuck"
  run := viaBrainfuck
  cases := cases "Turpentine" "turp"

def compiledWhitespace : Suite where
  name := "conformance: compiled to whitespace"
  run := viaWhitespace
  cases := cases "Turpentine" "turp"

def compiledSubleq : Suite where
  name := "conformance: compiled to subleq"
  run := viaSubleq
  cases := cases "Turpentine" "turp"

def compiledOok : Suite where
  name := "conformance: compiled to ook"
  run := viaOok
  cases := cases "Turpentine" "turp"

def compiledBrainloller : Suite where
  name := "conformance: compiled to brainloller"
  run := viaBrainloller
  cases := cases "Turpentine" "turp"

/-- Piet is the slowest of these by a wide margin, and the reason is the
interpreter rather than the backend: finding the colour block under the
pointer is a flood fill and it happens at every step, so one instruction
costs the area of the picture. The twenty run in about 45 seconds, most of
it the four programs with arrays, which pay `O(depth)` per element access
because Piet has no heap. -/
def compiledPiet : Suite where
  name := "conformance: compiled to piet"
  run := viaPiet
  cases := cases "Turpentine" "turp"

def suites : List Suite :=
  [ reference
  , compiledBrainfuck
  , compiledWhitespace
  , compiledSubleq
  , compiledOok
  , compiledBrainloller
  , compiledPiet ]

end Langlib.Tests.Conformance
