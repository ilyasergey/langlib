import Langlib.Common.TestHarness
import Langlib.Languages.Turpentine.Certified.BespokeWhitespace
import Langlib.Languages.Whitespace.Semantics

/-!
Tests for `Langlib.Turpentine.Certified.bespokeWhitespace`: the hand-written
Turpentine-to-Whitespace backend, restricted to the fragment
`Langlib/Languages/Turpentine/Certified/BespokeWhitespace.lean` proves it correct on.

Four suites.

* **bespoke pipeline** compiles Turpentine source through
  `bespokeWhitespace`, renders the result to whitespace text, parses that text
  back and runs it. The expected output is the answer in decimal: the compiler
  appends `print(answer)` to the body, which is what makes the specification's
  single `Nat` observable.
* **bespoke vs reference** runs the Turpentine reference interpreter on the
  same source with `print(answer);` appended and reports a runtime error unless
  the two agree. This is the same differential check the derived pipeline gets,
  now against a compiler that is proved rather than trusted.
* **bespoke vs derived** is the runnable form of `bespokeWhitespace_agrees_derived`: on a
  program both compilers accept, both compiled programs are run and their
  decoded answers compared. The theorem says they cannot differ; the suite
  says so on concrete programs, and would catch a mismatch in the plumbing
  around the two theorems (input encoding, decoder) that the theorem statement
  does not constrain.
* **out of fragment** pins the rejections. `bespokeWhitespace.compile` returns
  `Except.error` for everything the proof does not cover, even where the
  unrestricted backend behind `lake exe turpentine` would compile it happily.
-/

namespace Langlib.Tests.BespokeWhitespace

open Langlib.Common
open Langlib.Computability
open Langlib.Turpentine.Certified
open Langlib.Turpentine.Compile (derivedWhitespace)

/-- Compile Turpentine source with the bespoke compiler, render it to
whitespace text, then parse and run that text. Going through the text
exercises `Prog.render` and the whitespace parser as well. -/
def run (src : String) (input : Input) (fuel : Nat) : Except String RunResult := do
  let prog ← bespokeWhitespace.compileSource src
  Langlib.Whitespace.run prog.render input fuel

/-- Run the source both ways and insist they agree: through the bespoke
backend, and through the Turpentine reference interpreter on the same program
with the compiler's own epilogue, `println(""); print(answer);`, appended.
Comparing the raw output strings is what makes this a byte-for-byte check:
whatever the program printed for itself has to appear, in order, before the
newline and the answer. -/
def runBoth (src : String) (input : Input) (fuel : Nat) : Except String RunResult := do
  let p ← Langlib.Turpentine.parse src
  let _ ← (Langlib.Turpentine.checkProgram p).mapError ("type error: " ++ ·)
  let refProg : Langlib.Turpentine.Program :=
    { p with body := .seq p.body (.seq (.printStr "" true)
        (.printExpr (.var "answer") false)) }
  let refRes := Langlib.Turpentine.evalProgram refProg input fuel
  let ws ← bespokeWhitespace.compile p
  let wsRes ← Langlib.Whitespace.run ws.render input fuel
  match refRes.exit, wsRes.exit with
  | .halted, .halted =>
    if refRes.outputString == wsRes.outputString then
      return wsRes
    else
      return { exit := .error s!"disagreement: reference '{refRes.outputString}', \
        bespoke '{wsRes.outputString}'" }
  | .halted, e => return { exit := .error s!"bespoke backend did not halt: {repr e}" }
  | e, _ => return { exit := .error s!"reference interpreter did not halt: {repr e}" }

/-- The behavioural theorem, executed: compile with the *behaviourally*
verified compiler, run it, and insist that the events it performed are the
events the source performed — the same list, in the same order, with no
re-encoding. `bespokeWhitespaceIO.encodeTrace` is the identity, so this is
exactly what the instance claims, run rather than proved. -/
def runTrace (src : String) (input : Input) (fuel : Nat) : Except String RunResult := do
  let p ← Langlib.Turpentine.parse src
  let _ ← (Langlib.Turpentine.checkProgram p).mapError ("type error: " ++ ·)
  let ws ← bespokeWhitespaceIO.compile p
  let srcTrace := Langlib.Turpentine.evalTrace
    (Langlib.Turpentine.Certified.BespokeWhitespace.answerProgram p) input fuel
  let tgtTrace := TraceLang.trace (L := WhitespaceLang) ws
    (bespokeWhitespaceIO.encodeInput input) fuel
  let r := ProgLang.run (L := WhitespaceLang) ws (bespokeWhitespaceIO.encodeInput input) fuel
  match r.exit with
  | .halted =>
    if srcTrace == bespokeWhitespaceIO.encodeTrace tgtTrace then
      return { output := (String.intercalate "," (srcTrace.map reprStr)).toUTF8, exit := .halted }
    else
      return { exit := .error s!"trace disagreement: source {repr srcTrace}, \
        target {repr tgtTrace}" }
  | e => return { exit := .error s!"compiled program did not halt: {repr e}" }

/-- Run one program through both verified compilers for Whitespace and
compare the decoded answers: `bespokeWhitespace_agrees_derived`, executed. -/
def runAgree (src : String) (_input : Input) (fuel : Nat) : Except String RunResult := do
  let p ← Langlib.Turpentine.parse src
  let _ ← (Langlib.Turpentine.checkProgram p).mapError ("type error: " ++ ·)
  let ws₁ ← bespokeWhitespace.compile p
  let ws₂ ← derivedWhitespace.compile p
  let r₁ := ProgLang.run (L := WhitespaceLang) ws₁ bespokeWhitespace.encodeInput fuel
  let r₂ := ProgLang.run (L := WhitespaceLang) ws₂ derivedWhitespace.encodeInput fuel
  match r₁.exit, r₂.exit with
  | .halted, .halted =>
    match bespokeWhitespace.decodeOutput r₁.output,
          derivedWhitespace.decodeOutput r₂.output with
    | some a, some b =>
      if a == b then return { output := (toString a).toUTF8, exit := .halted }
      else return { exit := .error s!"disagreement: bespoke {a}, derived {b}" }
    | _, _ => return { exit := .error "an output did not decode as a decimal number" }
  | .halted, e => return { exit := .error s!"derived compiler did not halt: {repr e}" }
  | e, _ => return { exit := .error s!"bespoke compiler did not halt: {repr e}" }

private def sumTo5 : String :=
  "var answer : int;\nvar i : int;\nwhile i < 5 { i := i + 1; answer := answer + i; }"

private def factorial6 : String :=
  "var answer : int;\nvar i : int;\nvar n : int;\n" ++
  "n := 6;\nanswer := 1;\nwhile i < n { i := i + 1; answer := answer * i; }"

private def countdown : String :=
  "var answer : int;\nvar n : int;\nn := 10;\n" ++
  "while n > 0 { answer := answer + n; n := n - 1; }"

def pipeline : Suite where
  name := "turpentine -> whitespace (bespoke, verified fragment)"
  run := run
  cases :=
    [ { name := "default zero", source := .inline "var answer : int;",
        expect := .outputs "\n0" }
    , { name := "constant", source := .inline "var answer : int; answer := 7;",
        expect := .outputs "\n7" }
    , { name := "addition", source := .inline "var answer : int; answer := 2 + 3;",
        expect := .outputs "\n5" }
    , { name := "multiplication", source := .inline "var answer : int; answer := 3 * 4;",
        expect := .outputs "\n12" }
    , { name := "nested arithmetic",
        source := .inline "var answer : int; answer := 2 * 3 + 4 * 5;",
        expect := .outputs "\n26" }
      -- subtraction, unary minus and negative literals are in this fragment
      -- and outside the certified URM one: whitespace cells are signed.
    , { name := "subtraction", source := .inline "var answer : int; answer := 5 - 2;",
        expect := .outputs "\n3" }
    , { name := "a negative answer", source := .inline "var answer : int; answer := 2 - 9;",
        expect := .outputs "\n-7" }
    , { name := "unary minus",
        source := .inline "var answer : int; var x : int; x := 4; answer := -x - 1;",
        expect := .outputs "\n-5" }
    , { name := "variable read and write",
        source := .inline "var answer : int; var x : int; x := 4; answer := x + x;",
        expect := .outputs "\n8" }
    , { name := "comparison into a boolean variable",
        source := .inline ("var answer : int; var b : bool; b := 3 < 5; " ++
          "if b { answer := 1; } else { answer := 2; }"),
        expect := .outputs "\n1" }
    , { name := "the other comparisons",
        source := .inline ("var answer : int; var b : bool; " ++
          "b := 5 <= 5; if b { answer := answer + 1; } else { } " ++
          "b := 6 > 2; if b { answer := answer + 10; } else { } " ++
          "b := 2 >= 7; if b { answer := answer + 100; } else { }"),
        expect := .outputs "\n11" }
    , { name := "equality on integers",
        source := .inline ("var answer : int; var b : bool; b := 3 == 3; " ++
          "if b { answer := 1; } else { answer := 0; }"),
        expect := .outputs "\n1" }
    , { name := "inequality on booleans",
        source := .inline ("var answer : int; var b : bool; b := true != false; " ++
          "if b { answer := 1; } else { answer := 0; }"),
        expect := .outputs "\n1" }
    , { name := "boolean negation",
        source := .inline ("var answer : int; var b : bool; b := !(3 < 2); " ++
          "if b { answer := 1; } else { answer := 0; }"),
        expect := .outputs "\n1" }
    , { name := "if taking the else branch",
        source := .inline "var answer : int; if 1 > 2 { answer := 1; } else { answer := 2; }",
        expect := .outputs "\n2" }
    , { name := "while loop", source := .inline sumTo5, expect := .outputs "\n15" }
    , { name := "counting down with subtraction",
        source := .inline countdown, expect := .outputs "\n55" }
    , { name := "factorial by repeated multiplication",
        source := .inline factorial6, expect := .outputs "\n720" }
    , { name := "assert that holds",
        source := .inline "var answer : int; answer := 3; assert answer == 3;",
        expect := .outputs "\n3" }
    , { name := "conjunction",
        source := .inline ("var answer : int; var b : bool; b := 1 < 2 && 3 < 4; " ++
          "if b { answer := 1; } else { answer := 0; }"),
        expect := .outputs "\n1" }
    , { name := "conjunction that is false on the left",
        source := .inline ("var answer : int; var b : bool; b := 2 < 1 && 3 < 4; " ++
          "if b { answer := 1; } else { answer := 0; }"),
        expect := .outputs "\n0" }
    , { name := "disjunction",
        source := .inline ("var answer : int; var b : bool; b := 2 < 1 || 3 < 4; " ++
          "if b { answer := 1; } else { answer := 0; }"),
        expect := .outputs "\n1" }
    , { name := "disjunction that is true on the left",
        source := .inline ("var answer : int; var b : bool; b := 1 < 2 || 4 < 3; " ++
          "if b { answer := 1; } else { answer := 0; }"),
        expect := .outputs "\n1" }
    , { name := "nested loops",
        source := .inline ("var answer : int; var i : int; var j : int; " ++
          "while i < 4 { i := i + 1; j := 0; " ++
          "while j < 3 { j := j + 1; answer := answer + 1; } }"),
        expect := .outputs "\n12" }
      -- a failed assert is a runtime error in the reference semantics and a
      -- forbidden heap access in the compiled program: the error class is
      -- preserved, the wording is not, and the theorem says nothing here
      -- because its hypothesis (the source halts) does not hold.
    , { name := "assert that fails traps on a negative heap address",
        source := .inline "var answer : int; answer := 3; assert answer == 4;",
        expect := .runtimeError "heap retrieve at negative address -1" }
      -- the theorem is conditional on the source halting; a source loop that
      -- never ends compiles to a target loop that never ends.
    , { name := "a loop that never ends",
        source := .inline "var answer : int; while answer == 0 { }",
        expect := .diverges, fuel := 100_000 }
    ]

def differential : Suite where
  name := "bespoke whitespace vs turpentine reference"
  run := runBoth
  cases :=
    [ { name := "default zero", source := .inline "var answer : int;",
        expect := .outputs "\n0" }
    , { name := "arithmetic",
        source := .inline "var answer : int; answer := 2 * 3 + 4 * 5;",
        expect := .outputs "\n26" }
    , { name := "subtraction and a negative result",
        source := .inline "var answer : int; answer := 3 - 11;",
        expect := .outputs "\n-8" }
    , { name := "while loop", source := .inline sumTo5, expect := .outputs "\n15" }
    , { name := "counting down", source := .inline countdown, expect := .outputs "\n55" }
    , { name := "factorial", source := .inline factorial6, expect := .outputs "\n720" }
    , { name := "if and comparison",
        source := .inline ("var answer : int; var i : int; " ++
          "while i < 7 { i := i + 1; if i < 4 { answer := answer + i; } else { } }"),
        expect := .outputs "\n6" }
    , { name := "short-circuit && against the reference interpreter",
        source := .inline ("var answer : int; var i : int; " ++
          "while i < 6 { i := i + 1; " ++
          "if i > 2 && i < 5 { answer := answer + i; } else { } }"),
        expect := .outputs "\n7" }
    , { name := "short-circuit || against the reference interpreter",
        source := .inline ("var answer : int; var i : int; " ++
          "while i < 6 { i := i + 1; " ++
          "if i == 1 || i == 5 { answer := answer + i; } else { } }"),
        expect := .outputs "\n6" }
      -- string printing is in the verified fragment: the compiled program
      -- performs the source's output events, byte for byte and in order.
    , { name := "a printed string",
        source := .inline "var answer : int; print(\"hi\"); answer := 3;",
        expect := .outputs "hi\n3" }
    , { name := "println adds its newline",
        source := .inline "var answer : int; println(\"ok\"); answer := 1;",
        expect := .outputs "ok\n\n1" }
    , { name := "printing before and after the work",
        source := .inline ("var answer : int; var i : int; print(\"[\"); " ++
          "while i < 3 { i := i + 1; answer := answer + i; } print(\"]\");"),
        expect := .outputs "[]\n6" }
    , { name := "a string printed inside a loop",
        source := .inline ("var answer : int; var i : int; " ++
          "while i < 3 { i := i + 1; print(\".\"); } answer := 9;"),
        expect := .outputs "...\n9" }
    , { name := "printing an integer variable",
        source := .inline "var answer : int; answer := 7; print(answer);",
        expect := .outputs "7\n7" }
    , { name := "println of an integer expression",
        source := .inline "var answer : int; println(2 * 3 + 1); answer := 0;",
        expect := .outputs "7\n\n0" }
    , { name := "printing a boolean, true",
        source := .inline "var answer : int; var b : bool; b := 2 < 3; print(b); answer := 1;",
        expect := .outputs "true\n1" }
    , { name := "printing a boolean, false",
        source := .inline "var answer : int; var b : bool; b := 3 < 2; print(b); answer := 1;",
        expect := .outputs "false\n1" }
    , { name := "println of a boolean",
        source := .inline "var answer : int; println(1 == 1); answer := 5;",
        expect := .outputs "true\n\n5" }
    , { name := "a negative integer printed",
        source := .inline "var answer : int; print(0 - 42); answer := 1;",
        expect := .outputs "-42\n1" }
    , { name := "strings and values interleaved",
        source := .inline ("var answer : int; var i : int; " ++
          "while i < 3 { i := i + 1; print(\"i=\"); print(i); print(\" \"); } " ++
          "answer := i;"),
        expect := .outputs "i=1 i=2 i=3 \n3" }
    , { name := "printing inside a loop, one line each",
        source := .inline ("var answer : int; var i : int; " ++
          "while i < 3 { i := i + 1; println(i * i); } answer := 0;"),
        expect := .outputs "1\n4\n9\n\n0" }
    , { name := "a string printed in one branch only",
        source := .inline ("var answer : int; if 1 < 2 { print(\"yes\"); } " ++
          "else { print(\"no\"); } answer := 2;"),
        expect := .outputs "yes\n2" }
    ]

/-- Programs both compilers accept: no initialisers (the bespoke fragment
excludes them) and no subtraction, unary minus or negative literals (the
certified URM fragment excludes those). -/
def agreement : Suite where
  name := "bespoke whitespace vs derived whitespace"
  run := runAgree
  cases :=
    [ { name := "default zero", source := .inline "var answer : int;",
        expect := .outputs "0" }
    , { name := "constant", source := .inline "var answer : int; answer := 7;",
        expect := .outputs "7" }
    , { name := "arithmetic",
        source := .inline "var answer : int; answer := 2 * 3 + 4;",
        expect := .outputs "10" }
    , { name := "while loop", source := .inline sumTo5, expect := .outputs "15" }
    , { name := "if and comparison",
        source := .inline ("var answer : int; var b : bool; b := 3 < 5; " ++
          "if b { answer := 4; } else { answer := 9; }"),
        expect := .outputs "4" }
    , { name := "assert that holds",
        source := .inline "var answer : int; answer := 3; assert answer == 3;",
        expect := .outputs "3" }
    ]

def rejections : Suite where
  name := "turpentine constructs outside the verified whitespace fragment"
  run := run
  cases :=
    [ { name := "printByte", source := .inline "var answer : int; printByte(65);",
        expect := .parseError "the body reads input" }
    , { name := "readInt", source := .inline "var answer : int; answer := readInt();",
        expect := .parseError "the body reads input" }
    , { name := "readByte", source := .inline "var answer : int; answer := readByte();",
        expect := .parseError "the body reads input" }
    , { name := "division", source := .inline "var answer : int; answer := 8 / 2;",
        expect := .parseError "'/' or '%'" }
    , { name := "modulo", source := .inline "var answer : int; answer := 8 % 3;",
        expect := .parseError "'/' or '%'" }
    , { name := "array declaration",
        source := .inline "var answer : int; var a : int[3];",
        expect := .parseError "must be a scalar" }
    , { name := "an initialiser",
        source := .inline "var answer : int := 7;",
        expect := .parseError "no initialiser" }
    , { name := "no answer variable", source := .inline "var x : int; x := 1;",
        expect := .parseError "needs a declaration 'var answer : int;'" }
    , { name := "answer declared with the wrong type",
        source := .inline "var answer : bool;",
        expect := .parseError "needs a declaration 'var answer : int;'" }
    ]

/-- The behavioural instance, executed. The expectation is the *answer*
each run leaves, so the cases read like the others; what they check is the
trace, which `runTrace` compares before reporting anything. -/
def behavioural : Suite where
  name := "bespoke whitespace performs the source's events"
  run := fun src input fuel => do
    let r ← runTrace src input fuel
    match r.exit with
    | .halted => return { output := "traces agree".toUTF8, exit := .halted }
    | e => return { exit := e }
  cases :=
    [ { name := "a program that prints nothing of its own",
        source := .inline "var answer : int; answer := 7;",
        expect := .outputs "traces agree" }
    , { name := "a printed string",
        source := .inline "var answer : int; print(\"hi\"); answer := 3;",
        expect := .outputs "traces agree" }
    , { name := "printed integers",
        source := .inline ("var answer : int; var i : int; " ++
          "while i < 3 { i := i + 1; println(i); } answer := i;"),
        expect := .outputs "traces agree" }
    , { name := "printed booleans",
        source := .inline ("var answer : int; println(1 < 2); print(2 < 1); " ++
          "answer := 0;"),
        expect := .outputs "traces agree" }
    , { name := "strings, numbers and booleans interleaved",
        source := .inline ("var answer : int; var i : int; " ++
          "while i < 3 { i := i + 1; print(\"i=\"); print(i); print(\" even=\"); " ++
          "println(i == 2); } answer := i;"),
        expect := .outputs "traces agree" }
    ]

def suites : List Suite := [pipeline, differential, agreement, behavioural, rejections]

end Langlib.Tests.BespokeWhitespace
