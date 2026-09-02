import Langlib.Common.TestHarness
import Langlib.Tests.BeerSong
import Langlib.Languages.Turpentine.Compile.Unlambda
import Langlib.Languages.Unlambda.Semantics

/-!
Differential tests for the Turpentine → Unlambda compiler.

Every case is a *pair* of runs. The `run` field takes Turpentine source,
compiles it to an Unlambda program, parses that program back with Unlambda's
own parser and runs it on Unlambda's interpreter; the expected output is what
the Turpentine reference interpreter produces on the same input. A case
passes only when the two agree. Going out through the emitted bytes rather
than the syntax tree means the renderer and the parser are exercised too.

The bytes matter here more than anywhere else in the library. `.x` carries
the byte it prints, so a program that prints byte 200 *contains* byte 200,
and a `String` cannot hold it: writing one out UTF-8-encodes it into two
bytes that parse back as a dot carrying 195 and an unrecognised command. So
the compiler emits a `ByteArray` and the tests run it with
`Langlib.Unlambda.runBytes`. The `printByte` and `cat` cases below are the
ones that would fail if that ever went back to text.

What is worth testing, given that the backend takes the whole language:

* **Both halves of the conformance suite's arithmetic**, since integers are
  sign-and-magnitude Scott numerals and every operation on them is a fixed
  point. `Langlib/Tests/Conformance.lean` runs the twenty programs; the cases
  here are the ones that need input, which the conformance suite excludes.
* **Call by value**, which is where this backend can go wrong in ways no
  other one can. A thunk that runs early prints early, and a loop whose
  branches are not both guarded runs its body once on a false condition.
  `&& short-circuits over a division by zero` and the loop cases are those.
* **`c`**, which is reached by every test on the input: `?x` answers `i` or
  `v`, and only a captured continuation gets a value back out of the `v`.
* **Failure**, which Unlambda does not have. Turpentine's runtime errors
  become `e`, so the compiled program *halts* where the reference interpreter
  reports an error, with the output written so far. Those cases expect the
  partial output.

See `docs/unlambda/compiler.md`.
-/

namespace Langlib.Tests.CompileUnlambda

open Langlib.Common
open Langlib.Turpentine.Compile.Unlambda (compileBytes)

/-- Compile Turpentine source to an Unlambda program, then parse and run
those bytes. -/
def run (src : String) (input : Input) (fuel : Nat) : Except String RunResult := do
  let bytes ← compileBytes src
  Langlib.Unlambda.runBytes bytes input fuel

/-- Unary arithmetic is not free: a compiled program takes a few hundred
machine steps per Turpentine statement, plus O(n) for every operation on a
number of size n. -/
def fuel : Nat := 200_000_000

private def ex (f : String) : Source :=
  .file s!"Langlib/Examples/Turpentine/{f}"

def suite : Suite where
  name := "turpentine -> unlambda"
  run := run
  cases :=
    [ -- The examples, run as a reader would run them.
      { name := "hello", source := ex "hello.turp", fuel,
        expect := .outputs "Hello, Turpentine!\n" }
    , { name := "primes-mu", source := ex "primes-mu.turp", fuel,
        expect := .outputs "2\n3\n5\n7\n11\n13\n17\n19\n23\n29\n" }
    , { name := "99bottles", source := ex "99bottles.turp", fuel,
        expect := .outputs BeerSong.song }
    , { name := "cat", source := ex "cat.turp", input := "unlambda says meow", fuel,
        expect := .outputs "unlambda says meow" }
    , { name := "cat on empty input", source := ex "cat.turp", fuel,
        expect := .outputs "" }
      -- Every byte, not every character: `.x` carries the byte it prints, so
      -- the emitted program holds byte 200 itself.
    , { name := "cat is byte-exact above 127",
        -- The input is one non-ASCII character, so the bytes that go in are
        -- 0xc3 0xa9; the program echoes bytes, and gets them back exactly.
        source := ex "cat.turp", input := "é", fuel,
        expect := .outputsBytes ⟨#[0xc3, 0xa9]⟩ }
    , { name := "printByte reduces mod 256, including negatives",
        source := .inline "printByte(65);\nprintByte(321);\nprintByte(-191);\nprintByte(10);\n",
        fuel, expect := .outputs "AAA\n" }
    , { name := "printByte writes bytes above 127",
        source := .inline "printByte(200);\nprintByte(255);\nprintByte(128);\n",
        fuel, expect := .outputsBytes ⟨#[200, 255, 128]⟩ }
      -- readInt, which is a decimal parser written in combinators: the line
      -- is read one byte at a time and classified by a chain of `?x` tests.
    , { name := "readInt takes a line, spaces and a sign included",
        source := .inline "var a : int;\nvar b : int;\na := readInt();\nb := readInt();\n\
          println(a + b);\nprintln(a * b);\n",
        input := "  -42  \n8\n", fuel, expect := .outputs "-34\n-336\n" }
    , { name := "isqrt of a read number", source := ex "isqrt.turp",
        input := "17\n", fuel, expect := .outputs "4\n" }
    , { name := "sumdigits of a read number", source := ex "sumdigits.turp",
        input := "1234\n", fuel, expect := .outputs "10\n" }
      -- readByte reports -1 at end of input, and a NUL is not the end.
    , { name := "readByte reports end of input as -1",
        source := .inline "var c : int;\nc := readByte();\n\
          while c != -1 {\n  printByte(c + 1);\n  c := readByte();\n}\n",
        input := "abc", fuel, expect := .outputs "bcd" }
      -- Euclidean division, on all four sign combinations.
    , { name := "division is Euclidean, not truncating",
        source := .inline "var a : int := -7;\nvar b : int := 2;\n\
          println(a / b);\nprintln(a % b);\nprintln(7 / -2);\nprintln(7 % -2);\n\
          println(-7 / -2);\nprintln(-7 % -2);\n",
        fuel, expect := .outputs "-4\n1\n-3\n1\n4\n1\n" }
      -- Call by value: the right operand of `&&` must not run.
    , { name := "&& short-circuits over a division by zero",
        source := .inline "var x : int := 0;\nvar y : int := 5;\n\
          if x != 0 && 10 / x > 1 { println(1); } else { println(0); }\n\
          if y != 0 && 10 / y > 1 { println(1); } else { println(0); }\n\
          if x == 0 || 10 / x > 1 { println(2); } else { println(3); }\n",
        fuel, expect := .outputs "0\n1\n2\n" }
      -- ... and a loop whose condition is false must not run its body once.
    , { name := "a loop with a false condition runs no iterations",
        source := .inline "var i : int := 10;\nwhile i < 5 { println(99); i := i + 1; }\n\
          println(i);\n",
        fuel, expect := .outputs "10\n" }
    , { name := "nested loops and byte output",
        source := .inline "var i : int := 1;\nvar j : int;\n\
          while i <= 4 {\n  j := 0;\n  while j < i {\n    printByte(42);\n    j := j + 1;\n  }\n  \
          printByte(10);\n  i := i + 1;\n}\n",
        fuel, expect := .outputs "*\n**\n***\n****\n" }
    , { name := "booleans print as words",
        source := .inline "var t : bool := true;\nvar f : bool := false;\n\
          println(t);\nprintln(f);\nprintln(3 < 5);\nprintln(3 >= 5);\nprintln(t == f);\n",
        fuel, expect := .outputs "true\nfalse\ntrue\nfalse\nfalse\n" }
    , { name := "arrays, read and written at a computed index",
        source := .inline "var a : int[5];\nvar i : int;\n\
          while i < len(a) { a[i] := (i * i) % 7; i := i + 1; }\n\
          i := len(a) - 1;\nwhile i >= 0 { print(a[i]); print(\" \"); i := i - 1; }\n\
          println(\"\");\n",
        fuel, expect := .outputs "2 2 4 1 0 \n" }
    , { name := "a bool array, as the sieve uses one",
        source := .inline "var b : bool[3];\nvar i : int;\nb[1] := true;\n\
          while i < 3 { println(b[i]); i := i + 1; }\n",
        fuel, expect := .outputs "false\ntrue\nfalse\n" }
    , { name := "unary minus and an if without an else",
        source := .inline "var a : int := 5;\nprintln(-a);\nprintln(-(-a));\n\
          if a > 2 { println(1); }\nif a > 9 { println(2); }\n",
        fuel, expect := .outputs "-5\n5\n1\n" }
    , { name := "an initialiser can read the variable declared before it",
        source := .inline "var a : int := 6;\nvar b : int := a * 7;\nprintln(b);\n",
        fuel, expect := .outputs "42\n" }
    ]

/-- The failures Unlambda cannot report.

Turpentine has runtime errors and Unlambda has none: every value can be
applied to every value, so a run either halts or runs forever. The compiled
program therefore stops with `e` where the reference interpreter would report
an error, and what it has printed so far is what it printed. Each case here
runs a program that fails partway and expects the prefix. -/
def failureSuite : Suite where
  name := "turpentine -> unlambda (failure stops the run)"
  run := run
  cases :=
    [ { name := "division by zero stops after what was printed",
        source := .inline "println(1);\nprintln(10 / 0);\nprintln(2);\n",
        fuel, expect := .outputs "1\n" }
    , { name := "modulo by zero, likewise",
        source := .inline "print(\"a\");\nprintln(10 % 0);\n",
        fuel, expect := .outputs "a" }
    , { name := "a failed assert stops the run",
        source := .inline "var n : int := 1;\nprintln(n);\nassert n > 1;\nprintln(2);\n",
        fuel, expect := .outputs "1\n" }
    , { name := "an index past the end stops the run",
        source := .inline "var a : int[2];\nprintln(0);\nprintln(a[2]);\n",
        fuel, expect := .outputs "0\n" }
    , { name := "a negative index, likewise",
        source := .inline "var a : int[2];\nvar i : int := -1;\nprintln(0);\na[i] := 3;\n",
        fuel, expect := .outputs "0\n" }
    , { name := "readInt on a malformed line stops the run",
        source := .inline "var n : int;\nprintln(0);\nn := readInt();\nprintln(n);\n",
        input := "4x2\n", fuel, expect := .outputs "0\n" }
    , { name := "readInt at end of input stops the run",
        source := .inline "var n : int;\nprintln(0);\nn := readInt();\nprintln(n);\n",
        fuel, expect := .outputs "0\n" }
    ]

def suites : List Suite := [suite, failureSuite]

end Langlib.Tests.CompileUnlambda
