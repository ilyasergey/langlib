import Langlib.Common.TestHarness
import Langlib.Languages.Unlambda.Semantics

/-!
Golden tests for the Unlambda interpreter: the example programs, and
micro-programs pinning down each builtin, the delay special form, `e`, and
the parser's errors.

The interesting cases are the ones where the reference implementations
disagree with each other, so the tests say what langlib does: `d` tested on
the *value* of the operator rather than its syntax, `e` exiting rather than
being a second `c`, and `@` at end of input applying its argument to `v`.
-/

namespace Langlib.Tests.Unlambda

open Langlib.Common
open Langlib.Unlambda (run)

private def ex (f : String) : Source :=
  .file s!"Langlib/Examples/Unlambda/{f}"

def suite : Suite where
  name := "unlambda"
  run := run
  cases :=
    [ -- The examples.
      { name := "hello example", source := ex "hello.unl",
        expect := .outputs "Hello, world!\n" }
    , { name := "delay example prints in the other order",
        source := ex "delay.unl", expect := .outputs "now\nlater\n" }
    , { name := "stars example", source := ex "stars.unl",
        expect := .outputs "*\n**\n***\n****\n*****\n" }
    , { name := "call/cc example escapes the skipped operand",
        source := ex "callcc.unl", expect := .outputs "start\nend\n" }
    , { name := "cat example copies its input", source := ex "cat.unl",
        input := "meow", expect := .outputs "meow" }
    , { name := "cat example on empty input prints nothing",
        source := ex "cat.unl", expect := .outputs "" }
    , { name := "until example stops at the first q",
        source := ex "until.unl", input := "abcqdef", expect := .outputs "abc" }
    , { name := "quine example prints itself", source := ex "quine.unl",
        expect := .selfReproduces }
      -- The builtins.
    , { name := "i alone halts silently", source := .inline "i",
        expect := .outputs "" }
    , { name := ".x prints its byte and returns its argument",
        source := .inline "`.Ai", expect := .outputs "A" }
    , { name := "r is a dot carrying a newline", source := .inline "`ri",
        expect := .outputs "\n" }
    , { name := "k discards the second argument", source := .inline "``k.A.B",
        expect := .outputs "" }
    , { name := "s duplicates its argument: `sxyz = `xz`yz",
        source := .inline "```s.A.B.C", expect := .outputs "ABC" }
    , { name := "v swallows everything applied to it",
        source := .inline "``vi.A", expect := .outputs "" }
      -- The delay special form.
    , { name := "d delays its operand until the promise is applied",
        source := .inline "``d`.Bi`.Ai", expect := .outputs "AB" }
    , { name := "forcing a promise runs the delayed expression",
        source := .inline "``d`.Xii", expect := .outputs "X" }
    , { name := "d applied to a value keeps that value",
        source := .inline "``d.Xi", expect := .outputs "X" }
      -- Exit.
    , { name := "e exits at once", source := .inline "``e.X.Y",
        expect := .outputs "" }
    , { name := "e exits only when it is applied", source := .inline "``.Xe.Y",
        expect := .outputs "X" }
      -- Parse errors.
    , { name := "empty program", source := .inline "",
        expect := .parseError "empty program" }
    , { name := "backquote without operands", source := .inline "`",
        expect := .parseError "unfinished application" }
    , { name := "dot at end of input", source := .inline "`i.",
        expect := .parseError "it needs a character" }
    , { name := "unrecognised character", source := .inline "z",
        expect := .parseError "unrecognised character" }
    , { name := "text after the program", source := .inline "ii",
        expect := .parseError "text after the end of the program" }
    ]

def suites : List Suite := [suite]

end Langlib.Tests.Unlambda
