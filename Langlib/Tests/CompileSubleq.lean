import Langlib.Common.TestHarness
import Langlib.Turpentine.Compile.Subleq
import Langlib.Languages.Subleq.Semantics

/-!
Differential tests for the Turpentine → Subleq compiler.

Every case in the first suite is a *pair* of runs. The `run` field takes
Turpentine source, compiles it to subleq assembler text, assembles that, and
runs the resulting memory image on the subleq interpreter; the expected
output is what the Turpentine reference interpreter produces on the same
input (the values are the ones pinned down by `Langlib/Tests/Turpentine.lean`
where the two suites overlap). A case passes only when the two interpreters
agree.

The second suite checks the assembler round trip: the text emitted by
`compileSource` parses back, through our own `Langlib.Subleq.assemble`, to
exactly the image `compile` produces directly.

The subleq backend has no arithmetic divergence at all (its `divmod` routine
is Euclidean by construction, and byte output already reduces mod 256 the
way Turpentine does), and even `readByte` agrees at end of input, since both
languages answer `-1` there. The one thing subleq cannot reproduce is a
runtime error *message*, so the cases labelled "trap" assert the single
error the machine can raise; out-of-bounds indexing arrives there too. See
`docs/subleq/compiler.md`.
-/

namespace Langlib.Tests.CompileSubleq

open Langlib.Common
open Langlib.Turpentine.Compile.Subleq (compileSource compile buildChecked assembleItems renderItems)

/-- Compile Turpentine source to subleq assembler text, then assemble and run
it. Going through the text rather than the image also exercises the renderer
and our own assembler. -/
def run (src : String) (input : Input) (fuel : Nat) : Except String RunResult := do
  let text ← compileSource src
  Langlib.Subleq.run text input fuel

/-- Check that the emitted assembler text assembles back to exactly the
image `compile` builds directly. Reported through the harness as output. -/
def roundTrip (src : String) (_input : Input) (_fuel : Nat) :
    Except String RunResult := do
  let prog ← Langlib.Turpentine.parse src
  let types ← (Langlib.Turpentine.checkProgram prog).mapError ("type error: " ++ ·)
  let items ← buildChecked prog types
  let direct ← assembleItems items
  let parsed ← Langlib.Subleq.assemble (renderItems items)
  if parsed == direct then
    return { output := "round trip ok".toUTF8, exit := .halted }
  else
    return { exit := .error s!"round trip differs: {parsed.size} words assembled, {direct.size} words built" }

private def ex (f : String) : Source :=
  .file s!"Langlib/Examples/Turpentine/{f}.turp"

def suite : Suite where
  name := "turpentine -> subleq"
  run := run
  cases :=
    [ -- Literals, strings, output
      { name := "string literal", source := .inline "println(\"Hello, Turpentine!\");",
        expect := .outputs "Hello, Turpentine!\n" }
    , { name := "string escapes",
        source := .inline "print(\"a\\tb\\n\"); println(\"\\\"q\\\\\\\"\");",
        expect := .outputs "a\tb\n\"q\\\"\n" }
    , { name := "bare newline and print without one",
        source := .inline "print(1); print(2); println(); println(3);",
        expect := .outputs "12\n3\n" }
      -- The decimal printing routine
    , { name := "printint on zero and one digit",
        source := .inline "println(0); println(7);",
        expect := .outputs "0\n7\n" }
    , { name := "printint across digit boundaries",
        source := .inline "println(9); println(10); println(99); println(100); println(1000);",
        expect := .outputs "9\n10\n99\n100\n1000\n" }
    , { name := "printint on negatives",
        source := .inline "println(-1); println(-31337); println(-1000000);",
        expect := .outputs "-1\n-31337\n-1000000\n" }
    , { name := "printint has no digit ceiling",
        source := .inline "println(123456789012345678901234567890);",
        expect := .outputs "123456789012345678901234567890\n" }
      -- Arithmetic
    , { name := "precedence", source := .inline "println(2 + 3 * 4 - 10 / 3);",
        expect := .outputs "11\n" }
    , { name := "unary minus and negative operands",
        source := .inline "println(-(3 * 4)); println(-5 + 2); println(0 - 7 * -3);",
        expect := .outputs "-12\n-3\n21\n" }
    , { name := "multiplication with every sign",
        source := .inline "println(-6 * 7); println(6 * -7); println(-6 * -7); println(0 * -5);",
        expect := .outputs "-42\n-42\n42\n0\n" }
    , { name := "unbounded multiplication",
        source := .inline "var a : int := 1; var i : int := 0; while i < 20 { i := i + 1; a := a * i; } println(a);",
        expect := .outputs "2432902008176640000\n" }
      -- Euclidean division, which the divmod routine implements directly
    , { name := "euclidean division, positive divisor",
        source := .inline "println(-7 / 2); println(-7 % 2); println(7 / 2); println(7 % 2);",
        expect := .outputs "-4\n1\n3\n1\n" }
    , { name := "euclidean division, negative divisor",
        source := .inline "println(7 / -2); println(7 % -2); println(-7 / -2); println(-7 % -2);",
        expect := .outputs "-3\n1\n4\n1\n" }
    , { name := "nested division",
        source := .inline "println((100 / -7) / (-3 / 2)); println(100 % (7 % -3));",
        expect := .outputs "7\n0\n" }
      -- Comparisons and booleans
    , { name := "all six comparisons",
        source := .inline
          "println(1 < 2); println(2 <= 2); println(3 > 4); println(-1 >= -1); println(5 == 5); println(5 != 5);",
        expect := .outputs "true\ntrue\nfalse\ntrue\ntrue\nfalse\n" }
    , { name := "comparisons on negatives",
        source := .inline "println(-5 < -4); println(-5 > -4); println(-5 <= -5); println(0 == -0);",
        expect := .outputs "true\nfalse\ntrue\ntrue\n" }
    , { name := "boolean variables and negation",
        source := .inline "var p : bool := 1 < 2; var q : bool; println(p); println(!p); println(q);",
        expect := .outputs "true\nfalse\nfalse\n" }
    , { name := "short-circuit && never divides by zero",
        source := .inline
          "var x : int := 0; if x != 0 && 1 / x == 0 { println(1); } else { println(2); }",
        expect := .outputs "2\n" }
    , { name := "short-circuit || never divides by zero",
        source := .inline
          "var x : int := 0; if x == 0 || 1 / x == 0 { println(1); } else { println(2); }",
        expect := .outputs "1\n" }
      -- Control flow
    , { name := "else if chain",
        source := .inline
          "var n : int := 5; if n < 0 { println(0); } else if n == 5 { println(1); } else { println(2); }",
        expect := .outputs "1\n" }
    , { name := "nested while",
        source := .inline
          "var i : int := 0; var j : int; while i < 3 { j := 0; while j < 3 { print(i * 3 + j); print(\",\"); j := j + 1; } i := i + 1; } println();",
        expect := .outputs "0,1,2,3,4,5,6,7,8,\n" }
    , { name := "initialiser sees earlier variables",
        source := .inline "var a : int := 6; var b : int := a * 7; println(b);",
        expect := .outputs "42\n" }
    , { name := "assert that holds is silent",
        source := .inline "var n : int := 4; assert n >= 0 && n < 10; println(n);",
        expect := .outputs "4\n" }
      -- Both I/O styles, including the decimal parsing routine
    , { name := "readInt with a negative number",
        source := .inline "var x : int; x := readInt(); println(x * x);",
        input := "-12\n", expect := .outputs "144\n" }
    , { name := "readInt tolerates padding",
        source := .inline "var x : int; x := readInt(); println(x);",
        input := "\t  -13 \r\n", expect := .outputs "-13\n" }
    , { name := "readInt accepts an unterminated last line",
        source := .inline "var x : int; x := readInt(); println(x);",
        input := "42", expect := .outputs "42\n" }
    , { name := "readInt reads exactly one line at a time",
        source := .inline "var a : int; var b : int; a := readInt(); b := readInt(); println(a - b);",
        input := "1000\n1\n", expect := .outputs "999\n" }
    , { name := "readByte at end of input yields -1, as in Turpentine",
        source := .inline "var c : int; c := readByte(); println(c);",
        expect := .outputs "-1\n" }
    , { name := "readByte and printByte round trip",
        source := .inline "var c : int; c := readByte(); printByte(c + 1); println();",
        input := "A", expect := .outputs "B\n" }
    , { name := "printByte reduces mod 256 like Turpentine",
        source := .inline "printByte(321); printByte(-191); printByte(65);",
        expect := .outputs "AAA" }
      -- Arrays, via self-modifying address patching
    , { name := "array write then read",
        source := .inline "var a : int[3]; a[0] := 7; a[2] := 9; println(a[0] + a[2]);",
        expect := .outputs "16\n" }
    , { name := "array elements start at zero",
        source := .inline "var a : int[3]; println(a[0]); println(a[1] + a[2]);",
        expect := .outputs "0\n0\n" }
    , { name := "len is a literal",
        source := .inline "var a : int[5]; var b : bool[2]; println(len(a)); println(len(b) * 3);",
        expect := .outputs "5\n6\n" }
    , { name := "computed indices in a loop",
        source := .inline
          "var a : int[4]; var i : int := 0; while i < len(a) { a[i] := i * i; i := i + 1; } i := 0; while i < 4 { print(a[i]); print(\",\"); i := i + 1; } println();",
        expect := .outputs "0,1,4,9,\n" }
    , { name := "bool array",
        source := .inline "var b : bool[3]; b[1] := true; println(b[0]); println(b[1]); println(b[2]);",
        expect := .outputs "false\ntrue\nfalse\n" }
    , { name := "index by an arbitrary expression",
        source := .inline "var a : int[5]; a[2 + 1] := 42; println(a[6 / 2]);",
        expect := .outputs "42\n" }
    , { name := "an array element indexes another array",
        source := .inline
          "var a : int[3]; var b : int[3]; a[0] := 2; b[2] := 99; println(b[a[0]]);",
        expect := .outputs "99\n" }
    , { name := "two arrays do not overlap",
        source := .inline
          "var a : int[3]; var b : int[3]; var i : int := 0; while i < 3 { a[i] := i + 1; b[i] := 10 * (i + 1); i := i + 1; } println(a[0] + a[1] + a[2]); println(b[0] + b[1] + b[2]);",
        expect := .outputs "6\n60\n" }
    , { name := "short-circuit && keeps a bad index unevaluated",
        source := .inline
          "var a : int[3]; var j : int := -1; if j >= 0 && a[j] > 0 { println(1); } else { println(2); }",
        expect := .outputs "2\n" }
    , { name := "readInt into an element",
        source := .inline "var a : int[3]; a[1] := readInt(); println(a[1] * 2);",
        input := "21\n", expect := .outputs "42\n" }
    , { name := "readByte into an element",
        source := .inline "var a : int[2]; a[0] := readByte(); println(a[0]);",
        input := "A", expect := .outputs "65\n" }
    , { name := "readByte into an element at end of input yields -1",
        source := .inline "var a : int[2]; a[0] := readByte(); println(a[0]);",
        expect := .outputs "-1\n" }
      -- Out of bounds reaches the same trap as every other runtime error
    , { name := "trap: negative index, read",
        source := .inline "var a : int[3]; println(a[-1]);",
        expect := .runtimeError "negative address -2 in operand A" }
    , { name := "trap: index past the end, read",
        source := .inline "var a : int[3]; println(a[3]);",
        expect := .runtimeError "negative address -2 in operand A" }
    , { name := "trap: negative index, write",
        source := .inline "var a : int[3]; a[-2] := 1;",
        expect := .runtimeError "negative address -2 in operand A" }
    , { name := "trap: index past the end, write",
        source := .inline "var a : int[3]; a[9] := 1;",
        expect := .runtimeError "negative address -2 in operand A" }
    , { name := "rejects indexing a scalar",
        source := .inline "var x : int; println(x[0]);",
        expect := .parseError "cannot be indexed" }
      -- Example programs, compiled and run on the target
    , { name := "hello example", source := ex "hello",
        expect := .outputs "Hello, Turpentine!\n" }
    , { name := "isqrt example (16)", source := ex "isqrt", input := "16\n",
        expect := .outputs "4\n" }
    , { name := "isqrt example (17)", source := ex "isqrt", input := "17\n",
        expect := .outputs "4\n" }
    , { name := "isqrt example (0)", source := ex "isqrt", input := "0\n",
        expect := .outputs "0\n" }
    , { name := "sumdigits example", source := ex "sumdigits", input := "9045\n",
        expect := .outputs "18\n" }
    , { name := "gcd example", source := ex "gcd", input := "252\n105\n",
        expect := .outputs "21\n" }
    , { name := "fib example", source := ex "fib", input := "8\n",
        expect := .outputs "0\n1\n1\n2\n3\n5\n8\n13\n" }
    , { name := "cat example, EOF included", source := ex "cat", input := "meow\n",
        expect := .outputs "meow\n" }
    , { name := "collatz example (27)", source := ex "collatz", input := "27\n",
        expect := .outputs "111\n" }
    , { name := "primes example (30)", source := ex "primes", input := "30\n",
        expect := .outputs "2\n3\n5\n7\n11\n13\n17\n19\n23\n29\n" }
    , { name := "maxelem example", source := ex "maxelem",
        input := "3\n1\n4\n1\n5\n6\n9\n2\n", expect := .outputs "9\n" }
    , { name := "sort example", source := ex "sort",
        input := "5\n2\n9\n1\n5\n6\n", expect := .outputs "1\n2\n5\n5\n6\n9\n" }
    , { name := "sieve example", source := ex "sieve",
        expect := .outputs "2\n3\n5\n7\n11\n13\n17\n19\n23\n29\n31\n37\n41\n43\n47\n" }
      -- Every Turpentine runtime error becomes the one trap subleq can raise
    , { name := "trap: division by zero",
        source := .inline "var x : int := 0; println(1 / x);",
        expect := .runtimeError "negative address -2 in operand A" }
    , { name := "trap: modulo by zero",
        source := .inline "var x : int := 0; println(1 % x);",
        expect := .runtimeError "negative address -2 in operand A" }
    , { name := "trap: failed assert",
        source := .inline "assert 1 == 2;",
        expect := .runtimeError "negative address -2 in operand A" }
    , { name := "trap: readInt at end of input",
        source := .inline "var x : int; x := readInt();",
        expect := .runtimeError "negative address -2 in operand A" }
    , { name := "trap: readInt on a malformed line",
        source := .inline "var x : int; x := readInt();", input := "twelve\n",
        expect := .runtimeError "negative address -2 in operand A" }
    , { name := "trap: readInt on a line with two numerals",
        source := .inline "var x : int; x := readInt();", input := "1 2\n",
        expect := .runtimeError "negative address -2 in operand A" }
      -- Divergence of the program itself is preserved
    , { name := "while true still diverges", source := .inline "while true { }",
        fuel := 100_000, expect := .diverges }
      -- Rejected programs (the compiler type-checks before it emits)
    , { name := "rejects an ill-typed program", source := .inline "println(1 + true);",
        expect := .parseError "type error" }
    , { name := "rejects an undeclared variable", source := .inline "x := 4;",
        expect := .parseError "undeclared" }
    , { name := "rejects a bool read target",
        source := .inline "var p : bool; p := readInt();",
        expect := .parseError "which is a bool" }
    , { name := "rejects a program that does not parse",
        source := .inline "var x : int := 1\nprintln(x);",
        expect := .parseError "expected ';'" }
    ]

/-- The emitted assembler text is not decoration: our own assembler parses
it back to the same image the compiler built. -/
def roundTripSuite : Suite where
  name := "turpentine -> subleq (assembler round trip)"
  run := roundTrip
  cases :=
    ( ["hello", "isqrt", "sumdigits", "gcd", "fib", "cat", "collatz", "primes",
       "maxelem", "sort", "sieve"].map
        fun f => { name := s!"{f} example", source := ex f,
                   expect := .outputs "round trip ok" : TestCase } ) ++
    [ { name := "arrays, patched addressing and a padded data block",
        source := .inline
          "var a : int[9]; var b : bool[1]; a[3] := readInt(); b[0] := a[3] > 0; println(a[len(a) - 6]); println(b[0]);",
        expect := .outputs "round trip ok" }
    , { name := "every routine at once",
        source := .inline
          "var x : int; x := readInt(); println(x * x / 3 % 7); printByte(x); println(\"done\");",
        expect := .outputs "round trip ok" }
    , { name := "no routines at all", source := .inline "println(\"flat\");",
        expect := .outputs "round trip ok" }
    ]

def suites : List Suite := [suite, roundTripSuite]

end Langlib.Tests.CompileSubleq
