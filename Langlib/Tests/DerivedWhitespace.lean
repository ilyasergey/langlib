import Langlib.Common.TestHarness
import Langlib.Computability.Derived
import Langlib.Languages.Turpentine.Compile.Whitespace
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

The output is large by design: `Langlib/Languages/Turpentine/Compile/URM.lean` and
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
    , { name := "declaration with an initialiser",
        source := .inline "var answer : int := 7;", expect := .outputs "7" }
    , { name := "an initialiser in scope of the earlier declarations",
        source := .inline "var x : int := 3; var answer : int := x * x;",
        expect := .outputs "9" }
    , { name := "a boolean initialiser",
        source := .inline ("var b : bool := true; var answer : int; " ++
          "if b { answer := 5; } else { answer := 6; }"),
        expect := .outputs "5" }
    , { name := "an initialiser overwritten by the body",
        source := .inline "var answer : int := 2; answer := answer + 40;",
        expect := .outputs "42" }
    , { name := "conjunction",
        source := .inline ("var answer : int; var b : bool := 1 < 2 && 3 < 4; " ++
          "if b { answer := 1; } else { answer := 0; }"),
        expect := .outputs "1" }
    , { name := "conjunction that is false on the left",
        source := .inline ("var answer : int; var b : bool := 2 < 1 && 3 < 4; " ++
          "if b { answer := 1; } else { answer := 0; }"),
        expect := .outputs "0" }
    , { name := "disjunction",
        source := .inline ("var answer : int; var b : bool := 2 < 1 || 3 < 4; " ++
          "if b { answer := 1; } else { answer := 0; }"),
        expect := .outputs "1" }
    , { name := "disjunction that is true on the left",
        source := .inline ("var answer : int; var b : bool := 1 < 2 || 4 < 3; " ++
          "if b { answer := 1; } else { answer := 0; }"),
        expect := .outputs "1" }
    , { name := "division",
        source := .inline "var answer : int; answer := 17 / 5;", expect := .outputs "3" }
    , { name := "modulo",
        source := .inline "var answer : int; answer := 17 % 5;", expect := .outputs "2" }
    , { name := "division with a zero quotient",
        source := .inline "var answer : int; answer := 3 / 5;", expect := .outputs "0" }
    , { name := "modulo that divides exactly",
        source := .inline "var answer : int; answer := 12 % 4;", expect := .outputs "0" }
      -- Division by zero is a runtime error in the reference semantics, so
      -- `TurpentineHaltsWith` never holds and the theorem says nothing about
      -- these two. The macro still halts, and must: `&&` compiles its right
      -- operand unconditionally, so a diverging `/` would break short-circuit
      -- programs the source runs happily. These pin what it settles on.
    , { name := "a zero divisor yields a zero quotient, outside the theorem",
        source := .inline "var answer : int; var z : int; answer := 5 / z;",
        expect := .outputs "0" }
    , { name := "a zero divisor yields the dividend as remainder",
        source := .inline "var answer : int; var z : int; answer := 5 % z;",
        expect := .outputs "5" }
    , { name := "the right operand is evaluated even when short-circuited away",
        source := .inline ("var answer : int; var x : int := 3; " ++
          "var b : bool := false && x * x * x > 0; " ++
          "if b { answer := 1; } else { answer := 2; }"),
        expect := .outputs "2" }
    , { name := "assert that fails traps in a URM loop",
        source := .inline "var answer : int; answer := 3; assert answer == 4;",
        expect := .diverges, fuel := 200_000 }
      -- Arrays. A variable of length `n` gets `n` consecutive registers and
      -- `a[i]` compiles to a dispatch chain: `n` guarded blocks comparing `i`
      -- against 0, 1, …, n-1, so the addressing is static.
    , { name := "an array element, written and read back",
        source := .inline "var answer : int; var a : int[3]; a[1] := 7; answer := a[1];",
        expect := .outputs "7" }
    , { name := "array elements start at zero",
        source := .inline ("var answer : int; var a : int[3]; " ++
          "answer := a[0] + a[1] + a[2] + 5;"),
        expect := .outputs "5" }
    , { name := "a computed index picks the right block",
        source := .inline ("var answer : int; var a : int[4]; var i : int; " ++
          "a[0] := 10; a[1] := 20; a[2] := 30; a[3] := 40; " ++
          "i := 1 + 1; answer := a[i];"),
        expect := .outputs "30" }
    , { name := "a computed index on the left of an assignment",
        source := .inline ("var answer : int; var a : int[4]; var i : int; " ++
          "i := 3; a[i] := 9; answer := a[3];"),
        expect := .outputs "9" }
    , { name := "a bool array",
        source := .inline ("var answer : int; var b : bool[3]; b[2] := true; " ++
          "if b[2] { answer := 1; } else { answer := 0; }"),
        expect := .outputs "1" }
    , { name := "len is a compile-time constant",
        source := .inline "var answer : int; var a : int[12]; answer := len(a);",
        expect := .outputs "12" }
    , { name := "an array beside a scalar, both laid out",
        source := .inline ("var answer : int; var a : int[2]; var x : int := 5; " ++
          "a[0] := x; a[1] := x + x; answer := a[0] + a[1];"),
        expect := .outputs "15" }
    , { name := "summing an array in a loop",
        source := .inline ("var answer : int; var a : int[4]; var i : int; " ++
          "a[0] := 1; a[1] := 2; a[2] := 3; a[3] := 4; " ++
          "while i < len(a) { answer := answer + a[i]; i := i + 1; }"),
        expect := .outputs "10" }
      -- Out of range is a runtime error in the reference semantics, so
      -- `TurpentineHaltsWith` never holds and the theorem says nothing about
      -- these two. The compiled code falls off the end of the dispatch chain
      -- into a self-loop, which is what these pin: divergence rather than a
      -- plausible-looking wrong answer.
    , { name := "an index past the end diverges",
        source := .inline ("var answer : int; var a : int[2]; var i : int; " ++
          "i := 5; answer := a[i];"),
        expect := .diverges, fuel := 200_000 }
    , { name := "an out-of-range element assignment diverges",
        source := .inline ("var answer : int; var a : int[2]; var i : int; " ++
          "i := 2; a[i] := 1; answer := 3;"),
        expect := .diverges, fuel := 200_000 }
    , { name := "maxelem-tc.turp end to end",
        source := .file "Langlib/Examples/Turpentine/maxelem-tc.turp",
        expect := .outputs "9" }
    , { name := "sieve-tc.turp end to end",
        source := .file "Langlib/Examples/Turpentine/sieve-tc.turp",
        expect := .outputs "15" }
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
    , { name := "initialisers, in declaration order",
        source := .inline ("var a : int := 2; var b : int := a + 3; " ++
          "var answer : int := a * b;"),
        expect := .outputs "10" }
    , { name := "short-circuit && against the reference interpreter",
        source := .inline ("var answer : int; var i : int; " ++
          "while i < 6 { i := i + 1; " ++
          "if i > 2 && i < 5 { answer := answer + i; } else { } }"),
        expect := .outputs "7" }
    , { name := "digit sum by / and %, against the reference interpreter",
        source := .inline ("var n : int := 9045; var answer : int; " ++
          "while n > 0 { answer := answer + n % 10; n := n / 10; }"),
        expect := .outputs "18" }
    , { name := "short-circuit || against the reference interpreter",
        source := .inline ("var answer : int; var i : int; " ++
          "while i < 6 { i := i + 1; " ++
          "if i == 1 || i == 5 { answer := answer + i; } else { } }"),
        expect := .outputs "6" }
    , { name := "an array against the reference interpreter",
        source := .inline ("var answer : int; var a : int[5]; var i : int; " ++
          "while i < len(a) { a[i] := i * i; i := i + 1; } " ++
          "i := 0; " ++
          "while i < len(a) { answer := answer + a[i]; i := i + 1; }"),
        expect := .outputs "30" }
    , { name := "a bool array against the reference interpreter",
        source := .inline ("var answer : int; var b : bool[4]; var i : int; " ++
          "b[1] := true; b[3] := true; " ++
          "while i < len(b) { if b[i] { answer := answer + i; } else { } " ++
          "i := i + 1; }"),
        expect := .outputs "4" }
    , { name := "maxelem-tc.turp against the reference interpreter",
        source := .file "Langlib/Examples/Turpentine/maxelem-tc.turp",
        expect := .outputs "9" }
    , { name := "sieve-tc.turp against the reference interpreter",
        source := .file "Langlib/Examples/Turpentine/sieve-tc.turp",
        expect := .outputs "15" }
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
      -- the parser desugars `-3` to a unary minus, so the negative-literal
      -- guard in `compileExpr` is only reachable from a hand-built AST
    , { name := "negated literal", source := .inline "var answer : int; answer := 0 + -3;",
        expect := .parseError "unary minus" }
    , { name := "unary minus",
        source := .inline ("var answer : int; var x : int; " ++
          "x := 3; answer := 0 + -x;"),
        expect := .parseError "unary minus" }
      -- Arrays are in the fragment, but three uses of them are not. The
      -- dispatch chain diverges out of range, and `&&` and `||` compile their
      -- right operand unconditionally, so an array access there is refused
      -- rather than silently turned into a hang on a program the source runs.
    , { name := "an array access on the right of &&",
        source := .inline ("var answer : int; var a : int[3]; var i : int; " ++
          "var b : bool := i < len(a) && a[i] > 0; " ++
          "if b { answer := 1; } else { answer := 0; }"),
        expect := .parseError "right operand of '&&' indexes an array" }
    , { name := "an array access on the right of ||",
        source := .inline ("var answer : int; var a : int[3]; var i : int; " ++
          "var b : bool := i >= len(a) || a[i] > 0; " ++
          "if b { answer := 1; } else { answer := 0; }"),
        expect := .parseError "right operand of '||' indexes an array" }
    , { name := "reading into an array element",
        source := .inline "var answer : int; var a : int[3]; a[0] := readInt();",
        expect := .parseError "readInt is outside" }
    , { name := "reading a byte into an array element",
        source := .inline "var answer : int; var a : int[3]; a[0] := readByte();",
        expect := .parseError "readByte is outside" }
      -- `sort-tc.turp` is the one `-tc` example still outside the fragment,
      -- and arrays are no longer why: it indexes with `a[j - 1]`.
    , { name := "sort-tc.turp still needs subtraction",
        source := .file "Langlib/Examples/Turpentine/sort-tc.turp",
        expect := .parseError "'-' is outside" }
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
    , { name := "an array through the other target",
        source := .inline ("var answer : int; var a : int[3]; var i : int; " ++
          "a[2] := 5; i := 1 + 1; answer := a[i];"),
        expect := .outputs "5" }
    , { name := "print is rejected here too",
        source := .inline "var answer : int; print(answer);",
        expect := .parseError "print/println are outside" }
    ]

def suites : List Suite := [pipeline, differential, rejections, subleqPipeline]

end Langlib.Tests.DerivedWhitespace
