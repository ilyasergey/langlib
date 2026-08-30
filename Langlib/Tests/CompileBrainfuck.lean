import Langlib.Common.TestHarness
import Langlib.Languages.Turpentine.Semantics
import Langlib.Languages.Turpentine.Compile.Brainfuck

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

Three more suites cover what the compiled programs do *differently*, on
purpose:

* `traps`: Turpentine's runtime errors have no counterpart on a brainfuck
  tape, so a failed `assert`, division by zero and an out-of-range array
  index compile to an infinite loop. The reference interpreter reports an
  error; the compiled program runs out of fuel. Both are failures, and both
  are pinned down here.
* `referenceErrors`: the same programs on the reference interpreter, which
  is where the trap cases get their claim about *which* error the source
  language reports. It is also the only way to test the evaluation order of
  `a[i] := e`: the reference evaluates the right-hand side before the index,
  so a program whose right-hand side divides by zero and whose index is out
  of range reports the division, and only the interpreter can say so, since
  the compiled program has one trap for both.
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
    -- the array examples, end to end
  , { name := "maxelem example", source := ex "maxelem.turp",
      input := "3\n1\n4\n1\n5\n6\n9\n2\n", fuel := bfFuel,
      expect := .outputs "9\n" }
  , { name := "sort example", source := ex "sort.turp",
      input := "5\n2\n9\n1\n5\n6\n", fuel := bfFuel,
      expect := .outputs "1\n2\n5\n5\n6\n9\n" }
  , { name := "sieve example", source := ex "sieve.turp", fuel := bfFuel,
      expect := .outputs
        "2\n3\n5\n7\n11\n13\n17\n19\n23\n29\n31\n37\n41\n43\n47\n" }
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
    -- arrays
  , { name := "array elements start at zero", fuel := bfFuel, source := .inline
        "var a : int[3]; println(a[0]); println(a[1]); println(a[2]);",
      expect := .outputs "0\n0\n0\n" }
  , { name := "array element write and read", fuel := bfFuel, source := .inline
        "var a : int[3]; a[0] := 7; a[2] := -5; println(a[0]); println(a[1]); println(a[2]);",
      expect := .outputs "7\n0\n-5\n" }
  , { name := "computed index", fuel := bfFuel, source := .inline
        ("var a : int[5]; var i : int := 0; "
          ++ "while i < len(a) { a[i] := i * i; i := i + 1; } "
          ++ "i := 0; while i < len(a) { print(a[i]); print(\" \"); i := i + 1; } println();"),
      expect := .outputs "0 1 4 9 16 \n" }
  , { name := "index is itself an array element", fuel := bfFuel, source := .inline
        "var a : int[4]; a[0] := 3; a[a[0]] := 42; println(a[3]); println(a[a[0] - 3]);",
      expect := .outputs "42\n3\n" }
  , { name := "walking backwards through an array", fuel := bfFuel,
      source := .inline
        ("var a : int[4]; var i : int := 0; "
          ++ "while i < len(a) { a[i] := i + 1; i := i + 1; } "
          ++ "i := len(a) - 1; while i >= 0 { print(a[i]); i := i - 1; } println();"),
      expect := .outputs "4321\n" }
  , { name := "len is a compile-time constant", fuel := bfFuel, source := .inline
        "var a : int[7]; var b : bool[3]; println(len(a)); println(len(a) - len(b));",
      expect := .outputs "7\n4\n" }
  , { name := "bool array", fuel := bfFuel, source := .inline
        ("var f : bool[4]; var i : int := 0; f[1] := true; f[3] := !f[1]; "
          ++ "while i < len(f) { println(f[i]); i := i + 1; }"),
      expect := .outputs "false\ntrue\nfalse\nfalse\n" }
  , { name := "readInt into an element", fuel := bfFuel, source := .inline
        ("var a : int[3]; var i : int := 0; "
          ++ "while i < len(a) { a[i] := readInt(); i := i + 1; } "
          ++ "println(a[0] + a[1] + a[2]); println(a[2]);"),
      input := "10\n20\n-30\n", expect := .outputs "0\n-30\n" }
  , { name := "readByte into an element", fuel := bfFuel, source := .inline
        ("var a : int[3]; a[0] := readByte(); a[1] := readByte(); a[2] := readByte(); "
          ++ "println(a[0]); println(a[1]); println(a[2]);"),
      input := "AB", expect := .outputs "65\n66\n-1\n" }
  , { name := "arrays and scalars share the tape peacefully", fuel := bfFuel,
      source := .inline
        ("var a : int[3]; var n : int := 11; var b : int[2]; "
          ++ "a[2] := n; b[0] := a[2] * 2; n := n + b[0]; "
          ++ "println(a[2]); println(b[0]); println(n); println(b[1]);"),
      expect := .outputs "11\n22\n33\n0\n" }
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
    , { name := "index at the length traps", source := .inline
          "var a : int[3]; println(a[3]);", fuel := 2_000_000,
        expect := .diverges }
    , { name := "index one further still traps", source := .inline
          "var a : int[3]; var i : int := 4; println(a[i]);", fuel := 2_000_000,
        expect := .diverges }
    , { name := "negative index traps", source := .inline
          "var a : int[3]; println(a[-1]);", fuel := 2_000_000,
        expect := .diverges }
    , { name := "writing out of range traps", source := .inline
          "var a : int[3]; a[3] := 1; println(0);", fuel := 2_000_000,
        expect := .diverges }
    , { name := "writing at a negative index traps", source := .inline
          "var a : int[3]; a[-2] := 1; println(0);", fuel := 2_000_000,
        expect := .diverges }
    , { name := "reading into an out-of-range element traps", source := .inline
          "var a : int[3]; a[9] := readInt(); println(0);", input := "1\n",
        fuel := 2_000_000, expect := .diverges }
    , { name := "the last element is in range", source := .inline
          "var a : int[3]; a[2] := 5; println(a[2]);", fuel := bfFuel,
        expect := .outputs "5\n" }
    , { name := "right-hand side before index, both bad", source := .inline
          "var a : int[2]; var z : int := 0; a[5] := 1 / z;", fuel := 2_000_000,
        expect := .diverges }
    ]

/-- The same programs on the reference interpreter, which is where the trap
cases above get their claim about what the *source* language does. The last
case is the evaluation order of `a[i] := e`: the right-hand side runs first,
so the division is what fails, even though the index is out of range too.
The compiled program cannot show that, because it has one trap for both. -/
def referenceErrors : Suite where
  name := "turpentine -> brainfuck (what the reference reports instead)"
  run := Langlib.Turpentine.run
  cases :=
    [ { name := "index at the length is an error", source := .inline
          "var a : int[3]; println(a[3]);",
        expect := .runtimeError "index 3 out of bounds" }
    , { name := "negative index is an error", source := .inline
          "var a : int[3]; println(a[-1]);",
        expect := .runtimeError "index -1 out of bounds" }
    , { name := "writing out of range is an error", source := .inline
          "var a : int[3]; a[3] := 1; println(0);",
        expect := .runtimeError "index 3 out of bounds" }
    , { name := "right-hand side before index, both bad", source := .inline
          "var a : int[2]; var z : int := 0; a[5] := 1 / z;",
        expect := .runtimeError "division by zero" }
    ]

/-- Everything outside the supported fragment must be reported by name. The
harness reports a compile-stage `Except.error` as a parse error, which is
what `.parseError` matches here. -/
def rejected : Suite where
  name := "turpentine -> brainfuck (rejected constructs)"
  run := Langlib.Turpentine.Compile.Brainfuck.runCompiled
  cases :=
    [ { name := "an array longer than the walk counter", source := .inline
          "var a : int[256]; println(1);",
        expect := .parseError "at most 255 elements" }
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

def suites : List Suite :=
  [compiled, reference, traps, referenceErrors, rejected]

end Langlib.Tests.CompileBrainfuck
