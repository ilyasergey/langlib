import Langlib.Common.TestHarness
import Langlib.Languages.Turpentine.Compile.Fractran

/-!
# Compiler tests: Turpentine to FRACTRAN, the hand-written backend

Every case is a *pair* of runs, as in the other compiler suites: the `run`
field compiles the source to a fraction list and a starting value and runs
it on the FRACTRAN interpreter, and the expected output is what the
Turpentine reference interpreter produces. So each expected string is at
once a golden test of the reference interpreter and a claim that the
backend preserved its behaviour.

The observation convention is what makes this readable. FRACTRAN has no
output, so the backend arranges for the run to end on exactly `2 ^ answer`
and for no earlier state to be a power of two — every intermediate state
carries an odd state prime. `--out pow2` prints `k` whenever a step
produces `2 ^ k`, so it prints the answer, once, in decimal.

`rejected` pins the fragment: a construct outside it must come back as a
compile error naming it, not as silently wrong fractions.
-/

namespace Langlib.Tests.CompileFractran

open Langlib.Common

/-- Compiled FRACTRAN is slow: a register is a prime exponent, so counting
to `n` multiplies by that prime `n` times. -/
private def frFuel : Nat := 200_000_000

def compiled : Suite where
  name := "turpentine -> fractran (bespoke)"
  run := Langlib.Turpentine.Compile.Fractran.runCompiled
  cases :=
    [ { name := "a constant", source := .inline "var answer : int; answer := 7;",
        fuel := frFuel, expect := .outputs "7\n" }
    , { name := "zero", source := .inline "var answer : int;",
        fuel := frFuel, expect := .outputs "0\n" }
    , { name := "an initialiser", source := .inline "var answer : int := 9;",
        fuel := frFuel, expect := .outputs "9\n" }
    , { name := "an initialiser reading an earlier variable",
        source := .inline "var a : int := 6; var answer : int := a + 1;",
        fuel := frFuel, expect := .outputs "7\n" }
    , { name := "addition", source := .inline "var answer : int; answer := 2 + 3;",
        fuel := frFuel, expect := .outputs "5\n" }
    , { name := "multiplication", source := .inline "var answer : int; answer := 6 * 7;",
        fuel := frFuel, expect := .outputs "42\n" }
    , { name := "division", source := .inline "var answer : int; answer := 100 / 7;",
        fuel := frFuel, expect := .outputs "14\n" }
    , { name := "modulo", source := .inline "var answer : int; answer := 100 % 7;",
        fuel := frFuel, expect := .outputs "2\n" }
    , { name := "division by zero does not trap",
        source := .inline "var z : int; var answer : int := 5 / z;",
        fuel := frFuel, expect := .outputs "0\n" }
    , { name := "modulo by zero gives the dividend",
        source := .inline "var z : int; var answer : int := 5 % z;",
        fuel := frFuel, expect := .outputs "5\n" }
    , { name := "comparisons are booleans",
        source := .inline "var answer : int; if 2 < 3 { answer := 1; }",
        fuel := frFuel, expect := .outputs "1\n" }
    , { name := "the false branch",
        source := .inline "var answer : int := 4; if 3 < 2 { answer := 1; }",
        fuel := frFuel, expect := .outputs "4\n" }
    , { name := "else",
        source := .inline "var answer : int; if 3 < 2 { answer := 1; } else { answer := 2; }",
        fuel := frFuel, expect := .outputs "2\n" }
    , { name := "equality", source := .inline
          "var answer : int; if 3 == 3 { answer := 6; }",
        fuel := frFuel, expect := .outputs "6\n" }
    , { name := "inequality", source := .inline
          "var answer : int; if 3 != 4 { answer := 6; }",
        fuel := frFuel, expect := .outputs "6\n" }
    , { name := "the other four comparisons", source := .inline
          "var answer : int; if 3 <= 3 && 4 >= 4 && 5 > 4 && 4 < 5 { answer := 8; }",
        fuel := frFuel, expect := .outputs "8\n" }
    , { name := "or", source := .inline
          "var answer : int; if 1 < 0 || 2 < 3 { answer := 3; }",
        fuel := frFuel, expect := .outputs "3\n" }
    , { name := "not", source := .inline
          "var answer : int; if !(1 < 0) { answer := 3; }",
        fuel := frFuel, expect := .outputs "3\n" }
    , { name := "a while loop", source := .inline
          "var answer : int; var i : int; while i < 5 { answer := answer + i; i := i + 1; }",
        fuel := frFuel, expect := .outputs "10\n" }
    , { name := "a passing assert", source := .inline
          "var answer : int := 3; assert answer == 3;",
        fuel := frFuel, expect := .outputs "3\n" }
    , { name := "sumsq example", source := .file "Langlib/Examples/Turpentine/sumsq.turp",
        fuel := frFuel, expect := .outputs "30\n" }
    , { name := "fact-tc example", source := .file "Langlib/Examples/Turpentine/fact-tc.turp",
        fuel := frFuel, expect := .outputs "120\n" }
    , { name := "fib-tc example", source := .file "Langlib/Examples/Turpentine/fib-tc.turp",
        fuel := frFuel, expect := .outputs "55\n" }
    , { name := "isqrt-tc example", source := .file "Langlib/Examples/Turpentine/isqrt-tc.turp",
        fuel := frFuel, expect := .outputs "4\n" }
    , { name := "gcd-tc example", source := .file "Langlib/Examples/Turpentine/gcd-tc.turp",
        fuel := frFuel, expect := .outputs "21\n" }
    ]

/-- A failing assert diverges, as it does in every other backend: the
reference interpreter reports a runtime error and the compiled program
runs out of fuel. -/
def traps : Suite where
  name := "turpentine -> fractran (traps)"
  run := Langlib.Turpentine.Compile.Fractran.runCompiled
  cases :=
    [ { name := "a failing assert never halts", source := .inline
          "var answer : int := 3; assert answer == 4;",
        fuel := 200_000, expect := .diverges }
    ]

/-- Everything outside the fragment must be refused by name. The harness
reports a compile-stage `Except.error` as a parse error. -/
def rejected : Suite where
  name := "turpentine -> fractran (rejected constructs)"
  run := Langlib.Turpentine.Compile.Fractran.runCompiled
  cases :=
    [ { name := "no answer variable", source := .inline "var x : int := 1;",
        expect := .parseError "needs a variable named 'answer'" }
    , { name := "subtraction", source := .inline
          "var answer : int := 5; answer := answer - 1;",
        expect := .parseError "'-' is outside the fractran backend" }
    , { name := "a negative literal", source := .inline
          "var answer : int := 0 - 1;",
        expect := .parseError "outside the fractran backend" }
    , { name := "unary minus", source := .inline
          "var a : int := 1; var answer : int := -a;",
        expect := .parseError "unary minus" }
    , { name := "reading a number", source := .inline
          "var answer : int; answer := readInt();",
        expect := .parseError "fractran has no input" }
    , { name := "reading a byte", source := .inline
          "var answer : int; answer := readByte();",
        expect := .parseError "fractran has no input" }
    , { name := "printing a number", source := .inline
          "var answer : int := 1; println(answer);",
        expect := .parseError "fractran has no output" }
    , { name := "printing a string", source := .inline
          "var answer : int; println(\"hi\");",
        expect := .parseError "fractran has no output" }
    , { name := "printing a byte", source := .inline
          "var answer : int := 65; printByte(answer);",
        expect := .parseError "fractran has no output" }
    , { name := "an array", source := .inline
          "var a : int[3]; var answer : int;",
        expect := .parseError "outside the fractran backend" }
    ]

def suites : List Suite := [compiled, traps, rejected]

end Langlib.Tests.CompileFractran
