import Langlib.Common.TestHarness
import Langlib.Turpentine.Semantics
import Langlib.Turpentine.Compile.Brainfuck

/-!
# Compiler tests: Turpentine to brainfuck

The methodology, which is the point of this file: every case in `shared`
below is run twice, once by `Langlib.Turpentine.run` and once by
`Langlib.Turpentine.Compile.Brainfuck.runCompiled`, against the same input
and the same expected output. The second of those compiles the program,
hands the brainfuck to `Langlib.Brainfuck.evalProg` with the EOF convention
the generated code is written for (`--eof zero`), and compares bytes. So
each expected string is simultaneously a golden test of the reference
interpreter and a claim that the compiler preserved its behaviour; if the
two ever disagree, exactly one of the two suites fails and says which.

Every expected string here was obtained by running the reference
interpreter first, so the pair really is a differential test rather than two
copies of the same guess.

Two more suites cover what the compiled programs do *differently*, on
purpose:

* `traps`: Turpentine's runtime errors have no counterpart on a brainfuck
  tape, so a failed `assert` and division by zero compile to an infinite
  loop. The reference interpreter reports an error; the compiled program
  runs out of fuel. Both are failures, and both are pinned down here.
* `rejected`: constructs outside the supported fragment must come back as a
  compile error naming the construct, not as silently wrong code.

Inputs are small on purpose. The compiled programs are correct rather than
quick (`docs/brainfuck/compiler.md` has the numbers), so the examples run
here on inputs a few hundred times cheaper than the ones the interpreter
tests use.
-/

namespace Langlib.Tests.CompileBrainfuck

open Langlib.Common

private def ex (f : String) : Source :=
  .file s!"Langlib/Examples/Turpentine/{f}"

/-- The fuel the compiled programs get. A brainfuck step is a lot smaller
than a Turpentine statement, and the reference interpreter is happy to be
handed the same number. -/
private def bfFuel : Nat := 200_000_000

/-- Cases that both the reference interpreter and the compiled brainfuck
must satisfy. -/
def shared : List TestCase :=
  [ -- full examples
    { name := "hello example", source := ex "hello.turp", fuel := bfFuel,
      expect := .outputs "Hello, Turpentine!\n" }
  , { name := "cat example", source := ex "cat.turp", input := "meow\n",
      fuel := bfFuel, expect := .outputs "meow\n" }
  , { name := "isqrt example (0)", source := ex "isqrt.turp", input := "0\n",
      fuel := bfFuel, expect := .outputs "0\n" }
  , { name := "isqrt example (16)", source := ex "isqrt.turp", input := "16\n",
      fuel := bfFuel, expect := .outputs "4\n" }
  , { name := "isqrt example (17)", source := ex "isqrt.turp", input := "17\n",
      fuel := bfFuel, expect := .outputs "4\n" }
  , { name := "sumdigits example (405)", source := ex "sumdigits.turp",
      input := "405\n", fuel := bfFuel, expect := .outputs "9\n" }
  , { name := "gcd example", source := ex "gcd.turp", input := "252\n105\n",
      fuel := bfFuel, expect := .outputs "21\n" }
  , { name := "fib example (8)", source := ex "fib.turp", input := "8\n",
      fuel := bfFuel, expect := .outputs "0\n1\n1\n2\n3\n5\n8\n13\n" }
  , { name := "collatz example (6)", source := ex "collatz.turp", input := "6\n",
      fuel := bfFuel, expect := .outputs "8\n" }
  , { name := "primes example (10)", source := ex "primes.turp", input := "10\n",
      fuel := bfFuel, expect := .outputs "2\n3\n5\n7\n" }
    -- printing
  , { name := "integer literals", fuel := bfFuel, source := .inline
        "println(0); println(7); println(123); println(-5);",
      expect := .outputs "0\n7\n123\n-5\n" }
  , { name := "the extremes of the 16-bit range", fuel := bfFuel,
      source := .inline "println(32767); println(-32768);",
      expect := .outputs "32767\n-32768\n" }
  , { name := "string literals and escapes", fuel := bfFuel, source := .inline
        "println(\"tab\\there\"); print(\"no newline\"); println();",
      expect := .outputs "tab\there\nno newline\n" }
  , { name := "bool printing", fuel := bfFuel, source := .inline
        "var p : bool := 1 < 2; println(p); println(!p); println(p && !p); println(p || !p);",
      expect := .outputs "true\nfalse\nfalse\ntrue\n" }
    -- arithmetic
  , { name := "arithmetic", fuel := bfFuel, source := .inline
        "println(6 * 7); println(100 / 7); println(100 % 7);",
      expect := .outputs "42\n14\n2\n" }
  , { name := "signed multiplication", fuel := bfFuel, source := .inline
        "println(-6 * 7); println(-6 * -7); println(123 * 234);",
      expect := .outputs "-42\n42\n28782\n" }
  , { name := "euclidean division and modulo", fuel := bfFuel, source := .inline
        "println(-7 / 2); println(-7 % 2); println(7 / -2); println(7 % -2);",
      expect := .outputs "-4\n1\n-3\n1\n" }
  , { name := "initialiser sees earlier vars", fuel := bfFuel, source := .inline
        "var a : int := 6; var b : int := a * 7; println(b);",
      expect := .outputs "42\n" }
    -- comparisons and control flow
  , { name := "comparisons", fuel := bfFuel, source := .inline
        "println(3 <= 3); println(3 >= 4); println(3 != 3); println(3 == 3); println(3 > 2); println(2 < 3);",
      expect := .outputs "true\nfalse\nfalse\ntrue\ntrue\ntrue\n" }
  , { name := "comparisons across zero", fuel := bfFuel, source := .inline
        "var a : int := -5; var b : int := 3; println(a < b); println(a > b); println(a <= a);",
      expect := .outputs "true\nfalse\ntrue\n" }
  , { name := "else if chain", fuel := bfFuel, source := .inline
        "var n : int := 5; if n < 0 { println(0); } else if n == 5 { println(1); } else { println(2); }",
      expect := .outputs "1\n" }
  , { name := "nested while", fuel := bfFuel, source := .inline
        "var i : int := 1; var j : int; while i <= 3 { j := 1; while j <= i { printByte(48 + j); j := j + 1; } printByte(10); i := i + 1; }",
      expect := .outputs "1\n12\n123\n" }
  , { name := "short-circuit &&", fuel := bfFuel, source := .inline
        "var x : int := 0; if x != 0 && 1 / x == 0 { println(1); } else { println(2); }",
      expect := .outputs "2\n" }
  , { name := "short-circuit ||", fuel := bfFuel, source := .inline
        "var x : int := 0; if x == 0 || 1 / x == 0 { println(1); } else { println(2); }",
      expect := .outputs "1\n" }
  , { name := "assert that holds", fuel := bfFuel, source := .inline
        "var n : int := 4; assert n >= 0; println(n);",
      expect := .outputs "4\n" }
    -- I/O
  , { name := "byte I/O to end of input", fuel := bfFuel, source := .inline
        "var c : int; c := readByte(); while c >= 0 { printByte(c + 1); c := readByte(); }",
      input := "HAL", expect := .outputs "IBM" }
  , { name := "readByte at end of input is -1", fuel := bfFuel, source := .inline
        "var b : int; b := readByte(); println(b);",
      expect := .outputs "-1\n" }
  , { name := "readInt accepts a negative line", fuel := bfFuel, source := .inline
        "var x : int; x := readInt(); println(x * x); println(x);",
      input := "-12\n", expect := .outputs "144\n-12\n" }
  , { name := "printByte takes the low byte", fuel := bfFuel, source := .inline
        "printByte(321); printByte(-1 + 11);",  -- 321 mod 256 = 'A', then '\n'
      expect := .outputs "A\n" }
  ]

/-- The compiled programs, run on the brainfuck interpreter under the EOF
convention the compiler targets. -/
def compiled : Suite where
  name := "turpentine -> brainfuck"
  run := Langlib.Turpentine.Compile.Brainfuck.runCompiled
  cases := shared

/-- The same cases on the reference interpreter. Together with `compiled`,
this is the differential test: one expected string, two independent
machines. -/
def reference : Suite where
  name := "turpentine -> brainfuck (reference cross-check)"
  run := Langlib.Turpentine.run
  cases := shared

/-- Turpentine's runtime errors compile to `+[]`, so they show up as
divergence rather than as an error message. Small fuel: these reach the trap
almost immediately and then spin. -/
def traps : Suite where
  name := "turpentine -> brainfuck (runtime errors become traps)"
  run := Langlib.Turpentine.Compile.Brainfuck.runCompiled
  cases :=
    [ { name := "failed assert traps", source := .inline
          "assert 1 == 2; println(9);", fuel := 1_000_000, expect := .diverges }
    , { name := "division by zero traps", source := .inline
          "var x : int := 0; println(1 / x);", fuel := 1_000_000,
        expect := .diverges }
    , { name := "modulo by zero traps", source := .inline
          "var x : int := 0; println(1 % x);", fuel := 1_000_000,
        expect := .diverges }
    ]

/-- Everything outside the supported fragment must be reported by name. The
harness reports a compile-stage `Except.error` as a parse error, which is
what `.parseError` matches here. -/
def rejected : Suite where
  name := "turpentine -> brainfuck (rejected constructs)"
  run := Langlib.Turpentine.Compile.Brainfuck.runCompiled
  cases :=
    [ { name := "array declaration", source := .inline
          "var a : int[3]; println(1);",
        expect := .parseError "arrays are not supported" }
    , { name := "array element read", source := .inline
          "var a : int[3]; println(a[0]);",
        expect := .parseError "(a[i])" }
    , { name := "array element assignment", source := .inline
          "var a : int[3]; a[0] := 1;",
        expect := .parseError "(a[i] := e)" }
    , { name := "array element readInt", source := .inline
          "var a : int[3]; a[0] := readInt();",
        expect := .parseError "(a[i] := readInt())" }
    , { name := "array element readByte", source := .inline
          "var a : int[3]; a[0] := readByte();",
        expect := .parseError "(a[i] := readByte())" }
    , { name := "len of an array", source := .inline
          "var a : int[3]; println(len(a));",
        expect := .parseError "(len(a))" }
    , { name := "sieve example is out of the fragment", source := ex "sieve.turp",
        expect := .parseError "arrays are not supported" }
    , { name := "sort example is out of the fragment", source := ex "sort.turp",
        expect := .parseError "arrays are not supported" }
    , { name := "maxelem example is out of the fragment",
        source := ex "maxelem.turp",
        expect := .parseError "arrays are not supported" }
    , { name := "integer literal above the 16-bit range", source := .inline
          "println(100000);",
        expect := .parseError "above the 16-bit range" }
    , { name := "integer literal below the 16-bit range", source := .inline
          "println(-40000);",
        expect := .parseError "16-bit range" }
    , { name := "expression nested too deep", source := .inline
          ("println(" ++ String.join (List.replicate 40 "1 + (") ++ "1"
            ++ String.join (List.replicate 40 ")") ++ ");"),
        expect := .parseError "exceeds the brainfuck backend's limit" }
    , { name := "too many variables", source := .inline
          (String.join ((List.range 70).map (fun i => s!"var v{i} : int; "))
            ++ "println(1);"),
        expect := .parseError "at most 64 variables" }
    ]

def suites : List Suite := [compiled, reference, traps, rejected]

end Langlib.Tests.CompileBrainfuck
