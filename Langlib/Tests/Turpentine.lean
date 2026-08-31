import Langlib.Common.TestHarness
import Langlib.Languages.Turpentine.Semantics
import Langlib.Tests.BeerSong

/-!
Golden tests for Turpentine: the examples, arithmetic conventions (Euclidean
division), I/O, type errors, parse errors, runtime errors, and divergence.

`99bottles.turp` is checked against `Langlib.Tests.BeerSong.song`, the same
11459 bytes the Malbolge suite checks `99bottles.mal` against, so the two
programs are held to one standard rather than each to its own output.
-/

namespace Langlib.Tests.Turpentine

open Langlib.Common
open Langlib.Turpentine (run)

private def ex (f : String) : Source :=
  .file s!"Langlib/Examples/Turpentine/{f}"

def suite : Suite where
  name := "turpentine"
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
      -- arrays
    , { name := "maxelem example", source := ex "maxelem.turp",
        input := "3\n1\n4\n1\n5\n6\n9\n2\n", expect := .outputs "9\n" }
    , { name := "sort example", source := ex "sort.turp",
        input := "5\n2\n9\n1\n5\n6\n",
        expect := .outputs "1\n2\n5\n5\n6\n9\n" }
    , { name := "sumsq example (certified fragment)", source := ex "sumsq.turp",
        expect := .outputs "" }
    , { name := "isqrt-tc example (certified fragment)", source := ex "isqrt-tc.turp",
        expect := .outputs "" }
    , { name := "fact-tc example (certified fragment)", source := ex "fact-tc.turp",
        expect := .outputs "" }
    , { name := "gcd-tc example", source := ex "gcd-tc.turp", expect := .outputs "" }
    , { name := "sumdigits-tc example", source := ex "sumdigits-tc.turp", expect := .outputs "" }
    , { name := "collatz-tc example", source := ex "collatz-tc.turp", expect := .outputs "" }
    , { name := "fib-tc example", source := ex "fib-tc.turp", expect := .outputs "" }
    , { name := "maxelem-tc example", source := ex "maxelem-tc.turp", expect := .outputs "" }
    , { name := "primes-tc example", source := ex "primes-tc.turp", expect := .outputs "" }
    , { name := "sieve-tc example", source := ex "sieve-tc.turp", expect := .outputs "" }
    , { name := "sort-tc example", source := ex "sort-tc.turp", expect := .outputs "" }
    , { name := "hello-tc example", source := ex "hello-tc.turp", expect := .outputs "" }
    , { name := "cat-tc example", source := ex "cat-tc.turp", expect := .outputs "" }
    , { name := "sieve example", source := ex "sieve.turp",
        expect := .outputs "2\n3\n5\n7\n11\n13\n17\n19\n23\n29\n31\n37\n41\n43\n47\n" }
    , { name := "99bottles example (all 99 verses)", source := ex "99bottles.turp",
        expect := .outputs BeerSong.song }
    , { name := "array elements start at zero", source := .inline
          "var a : int[3]; println(a[0] + a[1] + a[2]);",
        expect := .outputs "0\n" }
    , { name := "bool array starts false", source := .inline
          "var f : bool[2]; println(f[1]);",
        expect := .outputs "false\n" }
    , { name := "len is the declared length", source := .inline
          "var a : int[7]; println(len(a));",
        expect := .outputs "7\n" }
    , { name := "computed index", source := .inline
          "var a : int[4]; var i : int := 1; a[i + 2] := 9; println(a[3]);",
        expect := .outputs "9\n" }
    , { name := "array read from input", source := .inline
          "var a : int[2]; a[0] := readInt(); a[1] := readByte(); println(a[0]); println(a[1]);",
        input := "42\nA", expect := .outputs "42\n65\n" }
    , { name := "index out of bounds (high)", source := .inline
          "var a : int[2]; println(a[2]);",
        expect := .runtimeError "out of bounds" }
    , { name := "index out of bounds (negative)", source := .inline
          "var a : int[2]; println(a[-1]);",
        expect := .runtimeError "out of bounds" }
    , { name := "write out of bounds", source := .inline
          "var a : int[2]; a[5] := 1;",
        expect := .runtimeError "out of bounds" }
    , { name := "type error: index a scalar", source := .inline
          "var x : int; println(x[0]);",
        expect := .parseError "cannot be indexed" }
    , { name := "type error: bool index", source := .inline
          "var a : int[2]; println(a[true]);",
        expect := .parseError "must be an int" }
    , { name := "type error: wrong element type", source := .inline
          "var a : int[2]; a[0] := true;",
        expect := .parseError "expected int" }
    , { name := "type error: print whole array", source := .inline
          "var a : int[2]; println(a);",
        expect := .parseError "index it as" }
    , { name := "type error: len of a scalar", source := .inline
          "var x : int; println(len(x));",
        expect := .parseError "cannot be indexed" }
    , { name := "type error: zero-length array", source := .inline
          "var a : int[0]; println(len(a));",
        expect := .parseError "length 0" }
    , { name := "type error: array initialiser", source := .inline
          "var a : int[2] := 1; println(len(a));",
        expect := .parseError "cannot have an initialiser" }
    , { name := "parse error: non-literal length", source := .inline
          "var n : int := 3; var a : int[n];",
        expect := .parseError "must be a literal" }
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
    , { name := "type error: non-bool while condition", source := .inline
          "var x : int := 3; while x { x := x - 1; }",
        expect := .parseError "'while' condition" }
    , { name := "invariant is no longer a keyword", source := .inline
          "var invariant : int := 7; println(invariant);",
        expect := .outputs "7\n" }
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
