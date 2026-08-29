import Langlib.Common.TestHarness
import Langlib.Languages.Subleq.Semantics

/-!
Golden tests for the subleq interpreter: the examples, the three branch
outcomes (negative, exactly zero, positive), the `-1` I/O conventions
including EOF and mod-256 output, `?` resolution, both clean-halt paths,
divergence, runtime errors, and parse errors.
-/

namespace Langlib.Tests.Subleq

open Langlib.Common
open Langlib.Subleq (run)

private def ex (f : String) : Source :=
  .file s!"Langlib/Examples/Subleq/{f}"

def suite : Suite where
  name := "subleq"
  run := run
  cases :=
    [ -- Examples.
      { name := "hello example", source := ex "hello.sq",
        expect := .outputs "Hello, World!\n" }
    , { name := "cat example", source := ex "cat.sq",
        input := "subleq says meow", expect := .outputs "subleq says meow" }
    , { name := "cat example on empty input", source := ex "cat.sq",
        expect := .outputs "" }
    , { name := "cat example passes a NUL byte", source := ex "cat.sq",
        input := "\x00A", expect := .outputsBytes (ByteArray.mk #[0, 65]) }
    , { name := "add example", source := ex "add.sq",
        expect := .outputs "i" }
    , { name := "countdown example", source := ex "countdown.sq",
        expect := .outputs "9876543210\n" }
      -- Subtraction and branching.
    , { name := "result exactly 0 branches",
        source := .inline "a a skip  b -1 ?+1  skip: Z Z -1  a: 5 b: 66 Z: 0",
        expect := .outputs "" }
    , { name := "positive result does not branch",
        source := .inline "one b bomb  b -1 ?+1  Z Z -1
                           bomb: x -1 ?+1  Z Z -1
                           one: 1 b: 66 x: 88 Z: 0",
        expect := .outputs "A" }
    , { name := "negative result branches",
        source := .inline "five b out  b -1 ?+1  Z Z -1
                           out: y -1 ?+1  Z Z -1
                           five: 5 b: 3 y: 89 Z: 0",
        expect := .outputs "Y" }
      -- I/O conventions.
    , { name := "input stores the byte",
        source := .inline "-1 c ?+1  c -1 ?+1  Z Z -1  c: 0 Z: 0",
        input := "Q", expect := .outputs "Q" }
    , { name := "input at EOF stores -1",
        source := .inline "-1 c ?+1  Z c isneg  n -1 ?+1  Z Z -1
                           isneg: e -1 ?+1  Z Z -1
                           Z: 0 c: 0 n: 78 e: 69",
        expect := .outputs "E" }
    , { name := "input mid-stream is nonnegative",
        source := .inline "-1 c ?+1  Z c isneg  n -1 ?+1  Z Z -1
                           isneg: e -1 ?+1  Z Z -1
                           Z: 0 c: 0 n: 78 e: 69",
        input := "A", expect := .outputs "N" }
    , { name := "input never branches",
        source := .inline "-1 c trap  c -1 ?+1  Z Z -1
                           trap: x -1 ?+1  Z Z -1
                           c: 0 x: 88 Z: 0",
        input := "A", expect := .outputs "A" }
    , { name := "output never branches (even on 0)",
        source := .inline "z -1 trap  w -1 ?+1  Z Z -1
                           trap: x -1 ?+1  Z Z -1
                           z: 0 w: 87 x: 88 Z: 0",
        expect := .outputsBytes (ByteArray.mk #[0, 87]) }
    , { name := "output byte is mod 256",
        source := .inline "x -1 ?+1  y -1 ?+1  Z Z -1  x: 321 y: -191 Z: 0",
        expect := .outputs "AA" }
      -- Halting.
    , { name := "halt via negative jump target",
        source := .inline "Z Z -1  Z: 0", expect := .outputs "" }
    , { name := "jump past end of memory halts cleanly",
        source := .inline "Z Z 100  Z: 0", expect := .outputs "" }
    , { name := "empty program halts",
        source := .inline "# only comments here\n; nothing at all",
        expect := .outputs "" }
      -- `?` resolves to the address of its own cell.
    , { name := "? is its own address",
        source := .inline "p -1 ?+1  Z Z -1  p: ?  Z: 0",
        expect := .outputsBytes (ByteArray.mk #[6]) }
      -- Runtime errors.
    , { name := "negative A is a runtime error",
        source := .inline "-5 x ?+1  x: 0",
        expect := .runtimeError "negative address -5" }
    , { name := "negative B is a runtime error",
        source := .inline "x -2 ?+1  x: 0",
        expect := .runtimeError "negative address -2" }
    , { name := "input into negative address is a runtime error",
        source := .inline "-1 -1 0",
        expect := .runtimeError "input into negative address" }
      -- Divergence.
    , { name := "tight loop diverges",
        source := .inline "loop: Z Z loop  Z: 0",
        fuel := 10_000, expect := .diverges }
      -- Parse errors.
    , { name := "bad token",
        source := .inline "12abc x ?+1\nx: 0",
        expect := .parseError "1:1: bad token '12abc'" }
    , { name := "undefined label",
        source := .inline "foo Z ?+1\nZ: 0",
        expect := .parseError "undefined label 'foo'" }
    , { name := "duplicate label",
        source := .inline "a: 1\na: 2",
        expect := .parseError "2:1: duplicate label 'a'" }
    , { name := "colon without a label name",
        source := .inline ": 5",
        expect := .parseError "':' without a label name" }
    ]

def suites : List Suite := [suite]

end Langlib.Tests.Subleq
