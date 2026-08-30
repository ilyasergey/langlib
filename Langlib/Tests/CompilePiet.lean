import Langlib.Common.TestHarness
import Langlib.Languages.Turpentine.Compile.Piet

/-!
# Compiler tests: Turpentine to Piet, the hand-written backend

Every case compiles the source to a codel grid, paints the grid as an
ASCII P3 PPM, reads that back with Piet's own parser, and runs it on the
reference interpreter. So a case exercises the whole round trip — the code
generator, the layout, `Grid.toImage`, and `parseGrid` — and the expected
output is what the Turpentine reference interpreter produces for the same
source.

`rejected` pins the fragment, which is everything but arrays.

The fuel is generous and the programs are small on purpose. Finding the
block under the pointer is a flood fill and it happens at every step, so
the cost of one Piet instruction grows with the area of the picture;
`docs/piet/compiler.md` has the measurements. These are tests of a
compiler, not a benchmark of an interpreter.
-/

namespace Langlib.Tests.CompilePiet

open Langlib.Common

private def pFuel : Nat := 2_000_000

def compiled : Suite where
  name := "turpentine -> piet (bespoke)"
  run := Langlib.Turpentine.Compile.Piet.runCompiled
  cases :=
    [ { name := "a string", source := .inline "print(\"hi\\n\");",
        fuel := pFuel, expect := .outputs "hi\n" }
    , { name := "a constant", source := .inline
          "var a : int; a := 5; println(a);",
        fuel := pFuel, expect := .outputs "5\n" }
    , { name := "an initialiser", source := .inline
          "var a : int := 9; println(a);",
        fuel := pFuel, expect := .outputs "9\n" }
    , { name := "an initialiser reading an earlier variable",
        source := .inline "var a : int := 6; var b : int := a + 1; println(b);",
        fuel := pFuel, expect := .outputs "7\n" }
    , { name := "multiplication", source := .inline
          "var a : int := 6; var b : int := 7; println(a * b);",
        fuel := pFuel, expect := .outputs "42\n" }
    , { name := "subtraction and negatives", source := .inline
          "println(3 - 10);",
        fuel := pFuel, expect := .outputs "-7\n" }
    , { name := "unary minus", source := .inline
          "var a : int := 4; println(-a);",
        fuel := pFuel, expect := .outputs "-4\n" }
      -- Piet's `divide` and `mod` floor; Turpentine's are Euclidean, and
      -- the two differ exactly when the divisor is negative.
    , { name := "division", source := .inline "println(100 / 7);",
        fuel := pFuel, expect := .outputs "14\n" }
    , { name := "modulo", source := .inline "println(100 % 7);",
        fuel := pFuel, expect := .outputs "2\n" }
    , { name := "division with a negative dividend", source := .inline
          "println(0 - 7); println((0 - 7) / 2); println((0 - 7) % 2);",
        fuel := pFuel, expect := .outputs "-7\n-4\n1\n" }
    , { name := "division with a negative divisor", source := .inline
          "println(7 / (0 - 2)); println(7 % (0 - 2));",
        fuel := pFuel, expect := .outputs "-3\n1\n" }
    , { name := "both negative", source := .inline
          "println((0 - 7) / (0 - 2)); println((0 - 7) % (0 - 2));",
        fuel := pFuel, expect := .outputs "4\n1\n" }
    , { name := "comparisons", source := .inline
          "if 3 <= 3 && 4 >= 4 && 5 > 4 && 4 < 5 { println(8); }",
        fuel := pFuel, expect := .outputs "8\n" }
    , { name := "equality and inequality", source := .inline
          "if 3 == 3 { println(1); } if 3 != 4 { println(2); }",
        fuel := pFuel, expect := .outputs "1\n2\n" }
    , { name := "else", source := .inline
          "if 3 < 2 { println(1); } else { println(2); }",
        fuel := pFuel, expect := .outputs "2\n" }
    , { name := "or", source := .inline
          "if 1 < 0 || 2 < 3 { println(3); }",
        fuel := pFuel, expect := .outputs "3\n" }
    , { name := "not", source := .inline
          "if !(1 < 0) { println(3); }",
        fuel := pFuel, expect := .outputs "3\n" }
      -- `&&` and `||` short-circuit, and it is observable: the right
      -- operand here would divide by zero, which traps.
    , { name := "&& short-circuits", source := .inline
          "var z : int; if z != 0 && 1 / z == 0 { println(1); } else { println(0); }",
        fuel := pFuel, expect := .outputs "0\n" }
    , { name := "|| short-circuits", source := .inline
          "var z : int; if z == 0 || 1 / z == 0 { println(1); } else { println(0); }",
        fuel := pFuel, expect := .outputs "1\n" }
    , { name := "booleans print as words", source := .inline
          "var b : bool := true; println(b); b := false; println(b);",
        fuel := pFuel, expect := .outputs "true\nfalse\n" }
    , { name := "a while loop", source := .inline
          "var i : int; var s : int; while i < 5 { s := s + i; i := i + 1; } println(s);",
        fuel := pFuel, expect := .outputs "10\n" }
    , { name := "nested loops", source := .inline
          "var i : int := 1; var j : int; while i <= 3 { j := 1; while j <= i { printByte(42); j := j + 1; } printByte(10); i := i + 1; }",
        fuel := pFuel, expect := .outputs "*\n**\n***\n" }
    , { name := "byte output", source := .inline
          "printByte(72); printByte(105); printByte(10);",
        fuel := pFuel, expect := .outputs "Hi\n" }
    , { name := "a large constant is built, not spelled out",
        source := .inline "println(16384);",
        fuel := pFuel, expect := .outputs "16384\n" }
    , { name := "a passing assert", source := .inline
          "var a : int := 3; assert a == 3; println(a);",
        fuel := pFuel, expect := .outputs "3\n" }
    , { name := "count example", source := .file "Langlib/Examples/Turpentine/suite/count.turp",
        fuel := pFuel, expect := .outputs "1\n2\n3\n4\n5\n6\n7\n8\n9\n10\n" }
      -- Arrays live on the stack, addressed by `roll`, with the computed
      -- index parked in a scratch slot below every variable.
    , { name := "an array at literal indices", source := .inline
          "var a : int[3]; a[0] := 7; a[1] := 8; a[2] := 9; println(a[0]); println(a[1]); println(a[2]);",
        fuel := pFuel, expect := .outputs "7\n8\n9\n" }
    , { name := "len is a literal", source := .inline
          "var a : bool[5]; println(len(a));",
        fuel := pFuel, expect := .outputs "5\n" }
    , { name := "arrays start at zero", source := .inline
          "var a : int[3]; var b : bool[2]; println(a[1]); println(b[0]);",
        fuel := pFuel, expect := .outputs "0\nfalse\n" }
    , { name := "a computed index on both sides", source := .inline
          "var a : int[5]; var i : int; while i < 5 { a[i] := i * i; i := i + 1; } i := 0; while i < 5 { println(a[i]); i := i + 1; }",
        fuel := pFuel, expect := .outputs "0\n1\n4\n9\n16\n" }
    , { name := "an index that is itself an array read", source := .inline
          "var a : int[3]; var b : int[3]; a[0] := 2; b[2] := 41; println(b[a[0]] + 1);",
        fuel := pFuel, expect := .outputs "42\n" }
    , { name := "two arrays and a scalar keep their slots", source := .inline
          "var a : int[2]; var x : int := 5; var b : int[2]; a[1] := 1; b[0] := 2; println(a[1]); println(x); println(b[0]);",
        fuel := pFuel, expect := .outputs "1\n5\n2\n" }
    , { name := "sort example", source := .file "Langlib/Examples/Turpentine/suite/sort.turp",
        fuel := pFuel, expect := .outputs "0\n1\n2\n5\n5\n6\n7\n9\n" }
    ]

/-- A failed `assert`, and a division by zero, become the trap lane: a
white wire that runs straight back into the lane it left. The reference
interpreter reports a runtime error at that point; the compiled program
runs out of fuel, as in every other backend.

Division by zero cannot be let through, and that is a Piet-specific
hazard rather than a choice. Piet *ignores* a command it cannot perform,
so a `divide` by zero would leave both operands on the stack and put every
later variable access off by one — silently wrong output rather than a
stopped program. -/
def traps : Suite where
  name := "turpentine -> piet (traps)"
  run := Langlib.Turpentine.Compile.Piet.runCompiled
  cases :=
    [ { name := "a failing assert never halts", source := .inline
          "var a : int := 3; assert a == 4;",
        fuel := 30_000, expect := .diverges }
    , { name := "division by zero never halts", source := .inline
          "var z : int; println(5 / z);",
        fuel := 30_000, expect := .diverges }
      -- Every array access is bounds-checked, and it has to be: without the
      -- check an index off the end would rotate the wrong distance and
      -- silently corrupt the variables below it.
    , { name := "an index past the end never halts", source := .inline
          "var a : int[3]; var i : int := 5; println(a[i]);",
        fuel := 60_000, expect := .diverges }
    , { name := "a negative index never halts", source := .inline
          "var a : int[3]; var i : int := 0 - 1; a[i] := 1;",
        fuel := 60_000, expect := .diverges }
    ]

/-- Nothing is outside the fragment any more, so what this pins is that the
whole language really does compile: one program using every statement form
the backend has to lay out. -/
def wholeLanguage : Suite where
  name := "turpentine -> piet (every construct)"
  run := Langlib.Turpentine.Compile.Piet.runCompiled
  cases :=
    [ { name := "every statement form at once", source := .inline
          "var a : int[3]; var i : int; var b : bool := true; \
           a[0] := 3; a[1] := 1; a[2] := 2; \
           while i < len(a) { if a[i] > 2 { print(\"big \"); } else { print(\"small \"); } println(a[i]); i := i + 1; } \
           assert i == 3; \
           if b && !(i == 3) { println(0); } else { printByte(111); printByte(107); printByte(10); }",
        fuel := pFuel,
        expect := .outputs "big 3\nsmall 1\nsmall 2\nok\n" }
    ]

def suites : List Suite := [compiled, traps, wholeLanguage]

end Langlib.Tests.CompilePiet
