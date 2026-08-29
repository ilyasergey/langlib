import Langlib.Common.TestHarness
import Langlib.Turpentine.Semantics

/-!
Golden tests for Turpentine: the examples, arithmetic conventions (Euclidean
division), I/O, type errors, parse errors, runtime errors, and divergence.
-/

namespace Langlib.Tests.Turpentine

open Langlib.Common
open Langlib.Turpentine (run)

private def ex (f : String) : Source :=
  .file s!"Langlib/Examples/Turpentine/{f}"

def suite : Suite where
  name := "wtf"
  run := run
  cases :=
    [ -- examples
      { name := "hello example", source := ex "hello.turp",
        expect := .outputs "Hello, Turpentine!\n" }
    , { name := "isqrt example (16)", source := ex "isqrt.turp", input := "16\n",
        expect := .outputs "4\n" }
    , { name := "isqrt example (17)", source := ex "isqrt.turp", input := "17\n",
        expect := .outputs "4\n" }
    , { name := "isqrt example (0)", source := ex "isqrt.turp", input := "0\n",
        expect := .outputs "0\n" }
    , { name := "sumdigits example", source := ex "sumdigits.turp",
        input := "9045\n", expect := .outputs "18\n" }
    , { name := "gcd example", source := ex "gcd.turp", input := "252\n105\n",
        expect := .outputs "21\n" }
    , { name := "fib example", source := ex "fib.turp", input := "8\n",
        expect := .outputs "0\n1\n1\n2\n3\n5\n8\n13\n" }
    , { name := "cat example", source := ex "cat.turp", input := "meow\n",
        expect := .outputs "meow\n" }
    , { name := "collatz example (27)", source := ex "collatz.turp",
        input := "27\n", expect := .outputs "111\n" }
    , { name := "primes example", source := ex "primes.turp", input := "30\n",
        expect := .outputs "2\n3\n5\n7\n11\n13\n17\n19\n23\n29\n" }
      -- semantics pinned down
    , { name := "euclidean division", source := .inline "println(-7 / 2);",
        expect := .outputs "-4\n" }
    , { name := "euclidean modulo", source := .inline "println(-7 % 2);",
        expect := .outputs "1\n" }
    , { name := "printByte wraps mod 256",
        source := .inline "printByte(321);",  -- 321 mod 256 = 65 = 'A'
        expect := .outputs "A" }
    , { name := "negative readInt", source := .inline
          "var x : int; x := readInt(); println(x * x);",
        input := "-12\n", expect := .outputs "144\n" }
    , { name := "readByte EOF is -1", source := .inline
          "var b : int; b := readByte(); println(b);",
        expect := .outputs "-1\n" }
    , { name := "short-circuit and", source := .inline
          "var x : int := 0; if x != 0 && 1 / x == 0 { println(1); } else { println(2); }",
        expect := .outputs "2\n" }
    , { name := "initialiser sees earlier vars", source := .inline
          "var a : int := 6; var b : int := a * 7; println(b);",
        expect := .outputs "42\n" }
    , { name := "bool printing", source := .inline
          "var p : bool := 1 < 2; println(p); println(!p);",
        expect := .outputs "true\nfalse\n" }
    , { name := "else if chain", source := .inline
          "var n : int := 5; if n < 0 { println(0); } else if n == 5 { println(1); } else { println(2); }",
        expect := .outputs "1\n" }
      -- runtime errors
    , { name := "division by zero", source := .inline
          "var x : int := 0; println(1 / x);",
        expect := .runtimeError "division by zero" }
    , { name := "assert failure", source := .inline "assert 1 == 2;",
        expect := .runtimeError "assertion failed" }
    , { name := "readInt at EOF", source := .inline
          "var x : int; x := readInt();",
        expect := .runtimeError "end of input" }
    , { name := "readInt malformed", source := .inline
          "var x : int; x := readInt();", input := "twelve\n",
        expect := .runtimeError "not an integer" }
      -- divergence
    , { name := "while true diverges", source := .inline
          "while true { }", fuel := 10_000, expect := .diverges }
      -- type errors (reported as parse-stage errors by the harness contract:
      -- run returns Except.error for both parse and type errors)
    , { name := "type error: int plus bool", source := .inline
          "println(1 + true);",
        expect := .parseError "type error" }
    , { name := "type error: undeclared variable", source := .inline
          "x := 4;",
        expect := .parseError "undeclared" }
    , { name := "type error: redeclaration", source := .inline
          "var x : int; var x : int;",
        expect := .parseError "declared twice" }
    , { name := "type error: bool read target", source := .inline
          "var p : bool; p := readInt();",
        expect := .parseError "which is a bool" }
    , { name := "type error: non-bool invariant", source := .inline
          "var x : int := 3; while x > 0 invariant x { x := x - 1; }",
        expect := .parseError "invariant" }
      -- parse errors
    , { name := "parse error: missing semicolon", source := .inline
          "var x : int := 1\nprintln(x);",
        expect := .parseError "expected ';'" }
    , { name := "parse error: late declaration", source := .inline
          "println(1);\nvar x : int;",
        expect := .parseError "must precede" }
    , { name := "parse error: unterminated string", source := .inline
          "println(\"oops);",
        expect := .parseError "unterminated string" }
    ]

def suites : List Suite := [suite]

end Langlib.Tests.Turpentine
