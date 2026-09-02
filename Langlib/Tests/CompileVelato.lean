import Langlib.Common.TestHarness
import Langlib.Tests.BeerSong
import Langlib.Languages.Turpentine.Compile.Velato
import Langlib.Languages.Velato.Semantics

/-!
Differential tests for the Turpentine → Velato compiler.

Every case is a *pair* of runs. The `run` field takes Turpentine source,
compiles it to Velato note names, parses those back with the Velato parser,
and runs the result on the Velato interpreter; the expected output is what
the Turpentine reference interpreter produces on the same input. A case
passes only when the two agree. Going through the note text rather than the
syntax tree also exercises the encoder and Velato's own parser, so a
disagreement between the two tables would show up here.

The interesting cases are the four places the languages differ, because
everywhere else the backend is a direct translation and there is nothing to
get wrong:

* **Euclidean versus truncating division.** Turpentine's `/` and `%` never
  give a negative remainder and Velato's do, so the backend emits a
  correction. The six-line `divmod` case is that correction being exercised
  on all four sign combinations.
* **Short circuits that survive the correction.** The correction needs
  statements, and hoisting them out of a `&&` would run them
  unconditionally. `x != 0 && 10 / x > 1` with `x` zero is the case that
  catches it: it must print, not divide by zero.
* **Booleans.** Velato has no `bool` and no strings, so printing one is an
  `if` that prints the word a character at a time.
* **`readByte` at end of input.** Velato stores `0` there and Turpentine
  wants `-1`. The backend converts, at the documented cost of not being
  able to tell a NUL byte from the end of the stream — the same caveat the
  brainfuck backend carries.

The second suite checks that the constructs outside the fragment are refused
by name rather than mis-compiled. See `docs/velato/compiler.md`.
-/

namespace Langlib.Tests.CompileVelato

open Langlib.Common
open Langlib.Turpentine.Compile.Velato (compileSource)

/-- Compile Turpentine source to Velato note names, then parse and run
them. -/
def run (src : String) (input : Input) (fuel : Nat) : Except String RunResult := do
  let text ← compileSource src
  Langlib.Velato.run text input fuel

/-- Report what the compiler refused, as output, so a refusal can be a
golden expectation rather than a comment. -/
def refusal (src : String) (_input : Input) (_fuel : Nat) : Except String RunResult :=
  match compileSource src with
  | .ok _ => return { exit := .error "expected a refusal, but it compiled" }
  | .error m => return { output := m.toUTF8, exit := .halted }

private def ex (f : String) : Source :=
  .file s!"Langlib/Examples/Turpentine/{f}"

def suite : Suite where
  name := "turpentine -> velato"
  run := run
  cases :=
    [ -- The examples, run as a reader would run them.
      { name := "hello", source := ex "hello.turp",
        expect := .outputs "Hello, Turpentine!\n" }
    , { name := "primes-mu", source := ex "primes-mu.turp",
        expect := .outputs "2\n3\n5\n7\n11\n13\n17\n19\n23\n29\n" }
    , { name := "cat", source := ex "cat.turp", input := "velato says meow",
        expect := .outputs "velato says meow" }
    , { name := "cat on empty input", source := ex "cat.turp", expect := .outputs "" }
    , { name := "99bottles", source := ex "99bottles.turp",
        expect := .outputs BeerSong.song }
      -- Euclidean division, on all four sign combinations. Velato's own
      -- operators truncate, so every line here is the correction working.
    , { name := "division is Euclidean, not truncating",
        source := .inline "var a : int := -7;\nvar b : int := 2;\n\
          println(a / b);\nprintln(a % b);\nprintln(7 / -2);\nprintln(7 % -2);\n\
          println(-7 / -2);\nprintln(-7 % -2);\n",
        expect := .outputs "-4\n1\n-3\n1\n4\n1\n" }
      -- The prelude the correction needs must not escape a short circuit.
    , { name := "&& short-circuits over a division by zero",
        source := .inline "var x : int := 0;\nvar y : int := 5;\n\
          if x != 0 && 10 / x > 1 { println(1); } else { println(0); }\n\
          if y != 0 && 10 / y > 1 { println(1); } else { println(0); }\n\
          if x == 0 || 10 / x > 1 { println(2); } else { println(3); }\n",
        expect := .outputs "0\n1\n2\n" }
      -- Velato has no bool and no strings.
    , { name := "booleans print as words",
        source := .inline "var t : bool := true;\nvar f : bool := false;\n\
          println(t);\nprintln(f);\nprintln(3 < 5);\nprintln(3 >= 5);\n",
        expect := .outputs "true\nfalse\ntrue\nfalse\n" }
      -- printByte reduces mod 256 the Euclidean way, so a negative
      -- argument still names a byte.
    , { name := "printByte reduces mod 256, including negatives",
        source := .inline "printByte(65);\nprintByte(321);\nprintByte(-191);\nprintByte(10);\n",
        expect := .outputs "AAA\n" }
      -- readByte reports -1 at end of input, which Velato does not.
    , { name := "readByte reports end of input as -1",
        source := .inline "var c : int;\nc := readByte();\n\
          while c != -1 {\n  printByte(c + 1);\n  c := readByte();\n}\n",
        input := "abc", expect := .outputs "bcd" }
      -- The rest of the language, which is a direct translation.
    , { name := "nested loops and arithmetic",
        source := .inline "var i : int := 1;\nvar j : int;\n\
          while i <= 4 {\n  j := 0;\n  while j < i {\n    printByte(42);\n    j := j + 1;\n  }\n  \
          printByte(10);\n  i := i + 1;\n}\n",
        expect := .outputs "*\n**\n***\n****\n" }
    , { name := "unary minus, which Velato spells as a subtraction",
        source := .inline "var a : int := 5;\nprintln(-a);\nprintln(-(-a));\n",
        expect := .outputs "-5\n5\n" }
    , { name := "if without an else",
        source := .inline "var a : int := 3;\nif a > 2 { println(1); }\nif a > 9 { println(2); }\n",
        expect := .outputs "1\n" }
    ]

def refusalSuite : Suite where
  name := "turpentine -> velato (outside the fragment)"
  run := refusal
  cases :=
    [ { name := "arrays are refused by name", source := ex "sort-tc.turp",
        expect := .outputs "velato: Velato has no arrays, so 'a' cannot be declared" }
    , { name := "so is an array in a sieve", source := ex "sieve-tc.turp",
        expect := .outputs "velato: Velato has no arrays, so 'composite' cannot be declared" }
    , { name := "readInt is refused, and says why",
        source := .inline "var n : int;\nn := readInt();\nprintln(n);\n",
        expect := .outputs "velato: readInt (for 'n') is outside this backend's fragment; \
          Velato reads one character at a time and has no way to fail on a malformed line" }
    , { name := "assert is refused, and says why",
        source := .inline "var n : int := 1;\nassert n > 0;\n",
        expect := .outputs "velato: assert is outside this backend's fragment; \
          Velato has no way to abort" }
    ]

def suites : List Suite := [suite, refusalSuite]

end Langlib.Tests.CompileVelato
