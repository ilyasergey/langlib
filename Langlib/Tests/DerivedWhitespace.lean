import Langlib.Common.TestHarness
import Langlib.Computability.Derived
import Langlib.Turpentine.Compile.Whitespace
import Langlib.Languages.Whitespace.Semantics
import Langlib.Languages.Subleq.Semantics

/-!
Tests for the certified pipeline: Turpentine → URM → Whitespace, where the
second arrow is `whitespaceComplete`'s own compiler rather than a hand-written
backend (`Langlib/Computability/Derived.lean`).

Three suites.

* **derived pipeline** compiles Turpentine source through
  `derivedWhitespace`, renders the result to whitespace text, parses that
  text back and runs it. The expected output is the answer, in decimal:
  `compileToURM` copies the variable `answer` into URM register 0, and the
  whitespace epilogue prints register 0.
* **derived vs reference** additionally runs the Turpentine reference
  interpreter on the same source with `print(answer);` appended, and reports a
  runtime error unless the two agree. A case passes only when the certified
  pipeline and the reference interpreter produce the same string, so the suite
  is a running check that the theorem's `answer` convention matches what the
  source language actually computes.
* **out of fragment** pins the rejections. `compileToURM` accepts exactly the
  fragment it proves itself correct on, so every rejection is part of the
  specification and every message names the offending construct. These cases
  use `Expectation.parseError`, which is the harness's "the pipeline returned
  `Except.error`" case; the errors here come from the compiler, not the parser.

A fourth suite runs the same source through `derivedSubleq` instead. It is
here rather than in a file of its own because it is testing `derived`, not
subleq: the same construction, applied to a different completeness witness,
with no new proof written.

The output is large by design: `Langlib/Turpentine/Compile/URM.lean` and
`docs/certified-compilation.md` record the measured sizes. Programs are kept
tiny for that reason.
-/

namespace Langlib.Tests.DerivedWhitespace

open Langlib.Common

/-- Compile Turpentine source with the derived compiler, render it to
whitespace text, then parse and run that text. Going through the text
exercises `Prog.render` and the whitespace parser as well. -/
def run (src : String) (input : Input) (fuel : Nat) : Except String RunResult := do
  let prog ← Langlib.Computability.derivedWhitespace.compileSource src
  Langlib.Whitespace.run prog.render input fuel

/-- Run the source both ways and insist they agree: through the derived
pipeline, and through the Turpentine reference interpreter on the same
program with `print(answer);` appended. -/
def runBoth (src : String) (input : Input) (fuel : Nat) : Except String RunResult := do
  let p ← Langlib.Turpentine.parse src
  let _ ← (Langlib.Turpentine.checkProgram p).mapError ("type error: " ++ ·)
  let refProg : Langlib.Turpentine.Program :=
    { p with body := .seq p.body (.printExpr (.var "answer") false) }
  let refRes := Langlib.Turpentine.evalProgram refProg input fuel
  let ws ← Langlib.Computability.derivedWhitespace.compile p
  let wsRes ← Langlib.Whitespace.run ws.render input fuel
  match refRes.exit, wsRes.exit with
  | .halted, .halted =>
    if refRes.outputString == wsRes.outputString then
      return wsRes
    else
      let msg := s!"disagreement: reference '{refRes.outputString}', " ++
        s!"derived '{wsRes.outputString}'"
      return { exit := .error msg }
  | .halted, e => return { exit := .error s!"derived pipeline did not halt: {repr e}" }
  | e, _ => return { exit := .error s!"reference interpreter did not halt: {repr e}" }

private def sumTo5 : String :=
  "var answer : int;\nvar i : int;\nwhile i < 5 { i := i + 1; answer := answer + i; }"

private def factorial6 : String :=
  "var answer : int;\nvar i : int;\nvar n : int;\n" ++
  "n := 6;\nanswer := 1;\nwhile i < n { i := i + 1; answer := answer * i; }"

def pipeline : Suite where
  name := "turpentine -> URM -> whitespace (derived)"
  run := run
  cases :=
    [ { name := "default zero", source := .inline "var answer : int;",
        expect := .outputs "0" }
    , { name := "constant", source := .inline "var answer : int; answer := 7;",
        expect := .outputs "7" }
    , { name := "addition", source := .inline "var answer : int; answer := 2 + 3;",
        expect := .outputs "5" }
    , { name := "multiplication", source := .inline "var answer : int; answer := 3 * 4;",
        expect := .outputs "12" }
    , { name := "nested arithmetic",
        source := .inline "var answer : int; answer := 2 * 3 + 4 * 5;",
        expect := .outputs "26" }
    , { name := "variable read and write",
        source := .inline "var answer : int; var x : int; x := 4; answer := x + x;",
        expect := .outputs "8" }
    , { name := "comparison to a boolean register",
        source := .inline ("var answer : int; var b : bool; b := 3 < 5; " ++
          "if b { answer := 1; } else { answer := 2; }"),
        expect := .outputs "1" }
    , { name := "the other comparisons",
        source := .inline ("var answer : int; var b : bool; " ++
          "b := 5 <= 5; if b { answer := answer + 1; } else { } " ++
          "b := 6 > 2; if b { answer := answer + 10; } else { } " ++
          "b := 2 >= 7; if b { answer := answer + 100; } else { }"),
        expect := .outputs "11" }
    , { name := "equality on integers",
        source := .inline ("var answer : int; var b : bool; b := 3 == 3; " ++
          "if b { answer := 1; } else { answer := 0; }"),
        expect := .outputs "1" }
    , { name := "inequality on booleans",
        source := .inline ("var answer : int; var b : bool; b := true != false; " ++
          "if b { answer := 1; } else { answer := 0; }"),
        expect := .outputs "1" }
    , { name := "boolean negation",
        source := .inline ("var answer : int; var b : bool; b := !(3 < 2); " ++
          "if b { answer := 1; } else { answer := 0; }"),
        expect := .outputs "1" }
    , { name := "if taking the else branch",
        source := .inline "var answer : int; if 1 > 2 { answer := 1; } else { answer := 2; }",
        expect := .outputs "2" }
    , { name := "while loop", source := .inline sumTo5, expect := .outputs "15" }
    , { name := "factorial by repeated multiplication",
        source := .inline factorial6, expect := .outputs "720" }
    , { name := "assert that holds",
        source := .inline "var answer : int; answer := 3; assert answer == 3;",
        expect := .outputs "3" }
    , { name := "assert that fails traps in a URM loop",
        source := .inline "var answer : int; answer := 3; assert answer == 4;",
        expect := .diverges, fuel := 200_000 }
    ]

def differential : Suite where
  name := "derived whitespace vs turpentine reference"
  run := runBoth
  cases :=
    [ { name := "default zero", source := .inline "var answer : int;",
        expect := .outputs "0" }
    , { name := "arithmetic",
        source := .inline "var answer : int; answer := 2 * 3 + 4 * 5;",
        expect := .outputs "26" }
    , { name := "while loop", source := .inline sumTo5, expect := .outputs "15" }
    , { name := "factorial", source := .inline factorial6, expect := .outputs "720" }
    , { name := "if and comparison",
        source := .inline ("var answer : int; var i : int; " ++
          "while i < 7 { i := i + 1; if i < 4 { answer := answer + i; } else { } }"),
        expect := .outputs "6" }
    ]

def rejections : Suite where
  name := "turpentine constructs outside the certified URM fragment"
  run := run
  cases :=
    [ { name := "print", source := .inline "var answer : int; print(answer);",
        expect := .parseError "print/println are outside" }
    , { name := "println", source := .inline "var answer : int; println(answer);",
        expect := .parseError "print/println are outside" }
    , { name := "printByte", source := .inline "var answer : int; printByte(65);",
        expect := .parseError "printByte is outside" }
    , { name := "string literal", source := .inline "var answer : int; print(\"hi\");",
        expect := .parseError "printing a string literal" }
    , { name := "readInt", source := .inline "var answer : int; answer := readInt();",
        expect := .parseError "readInt is outside" }
    , { name := "readByte", source := .inline "var answer : int; answer := readByte();",
        expect := .parseError "readByte is outside" }
    , { name := "subtraction", source := .inline "var answer : int; answer := 5 - 2;",
        expect := .parseError "'-' is outside" }
    , { name := "division", source := .inline "var answer : int; answer := 6 / 2;",
        expect := .parseError "'/' is outside" }
    , { name := "modulo", source := .inline "var answer : int; answer := 6 % 4;",
        expect := .parseError "'%' is outside" }
    , { name := "conjunction",
        source := .inline "var answer : int; var b : bool; b := true && false;",
        expect := .parseError "'&&' is outside" }
    , { name := "disjunction",
        source := .inline "var answer : int; var b : bool; b := true || false;",
        expect := .parseError "'||' is outside" }
      -- the parser desugars `-3` to a unary minus, so the negative-literal
      -- guard in `compileExpr` is only reachable from a hand-built AST
    , { name := "negated literal", source := .inline "var answer : int; answer := 0 + -3;",
        expect := .parseError "unary minus" }
    , { name := "unary minus",
        source := .inline ("var answer : int; var x : int; " ++
          "x := 3; answer := 0 + -x;"),
        expect := .parseError "unary minus" }
    , { name := "array declaration",
        source := .inline "var answer : int; var a : int[3];",
        expect := .parseError "arrays are outside" }
    , { name := "initialiser", source := .inline "var answer : int := 5;",
        expect := .parseError "has an initialiser" }
    , { name := "no answer variable", source := .inline "var x : int; x := 1;",
        expect := .parseError "needs a variable named 'answer'" }
    ]

/-- The same pipeline into subleq, through `derivedSubleq`. The subleq
witness leaves its answer in unary, so the raw output is decoded and
re-rendered in decimal before comparison. -/
def runSubleq (src : String) (_input : Input) (fuel : Nat) : Except String RunResult := do
  let prog ← Langlib.Computability.derivedSubleq.compileSource src
  let r := Langlib.Computability.ProgLang.run (L := Langlib.Computability.SubleqLang) prog
    Langlib.Computability.derivedSubleq.encodeInput fuel
  match r.exit, Langlib.Computability.derivedSubleq.decodeOutput r.output with
  | .halted, some k => return { r with output := (toString k).toUTF8 }
  | .halted, none => return { r with exit := .error "output did not decode to a number" }
  | _, _ => return r

def subleqPipeline : Suite where
  name := "turpentine -> URM -> subleq (derived)"
  run := runSubleq
  cases :=
    [ { name := "constant", source := .inline "var answer : int; answer := 4;",
        expect := .outputs "4" }
    , { name := "arithmetic", source := .inline "var answer : int; answer := 2 * 3;",
        expect := .outputs "6" }
    , { name := "while loop",
        source := .inline ("var answer : int; var i : int; " ++
          "while i < 3 { i := i + 1; answer := answer + i; }"),
        expect := .outputs "6" }
    , { name := "print is rejected here too",
        source := .inline "var answer : int; print(answer);",
        expect := .parseError "print/println are outside" }
    ]

def suites : List Suite := [pipeline, differential, rejections, subleqPipeline]

end Langlib.Tests.DerivedWhitespace
