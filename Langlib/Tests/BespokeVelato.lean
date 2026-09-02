import Langlib.Common.TestHarness
import Langlib.Languages.Turpentine.Certified.BespokeVelato
import Langlib.Languages.Velato.Semantics

/-!
Tests for `Langlib.Turpentine.Certified.bespokeVelato` and `bespokeVelatoIO`:
the hand-written Turpentine-to-Velato backend, restricted to the fragment
`Langlib/Languages/Turpentine/Certified/BespokeVelato.lean` proves it correct
on.

Five suites.

* **bespoke pipeline** compiles Turpentine source through `bespokeVelato`,
  renders the result to Velato note names, parses that text back and runs
  it. The expected output is whatever the program printed, a newline, and
  the answer in decimal: the compiler appends `println(""); print(answer);`
  to the body, which is what makes the specification's single `Nat`
  observable.
* **bespoke vs reference** runs the Turpentine reference interpreter on the
  same source with the same epilogue appended and reports a runtime error
  unless the two outputs agree byte for byte.
* **bespoke vs derived** is the runnable form of
  `bespokeVelato_agrees_derived`: on a program both compilers accept, both
  compiled programs are run and their decoded answers compared. The derived
  compiler keeps its whole register file in one Gödel-numbered variable, so
  its programs are kept tiny.
* **out of fragment** pins the rejections. `bespokeVelato.compile` returns
  `Except.error` for everything the proof does not cover, even where the
  unrestricted backend behind `lake exe turpentine` would compile it.
* **the behavioural instance, executed**: compile with `bespokeVelatoIO`,
  run the source and the target on the *same* input stream, and insist the
  two event lists are identical. Several cases read input, which is what
  distinguishes this instance from the whitespace one: `encodeInput` is the
  identity here, and the input events have to match too.
-/

namespace Langlib.Tests.BespokeVelato

open Langlib.Common
open Langlib.Computability
open Langlib.Turpentine.Certified
open Langlib.Turpentine.Compile (derivedVelato)

/-- Compile Turpentine source with the bespoke compiler, render it to note
names, then parse and run that text. Going through the text exercises the
encoder and Velato's parser as well. -/
def run (src : String) (input : Input) (fuel : Nat) : Except String RunResult := do
  let prog ← bespokeVelato.compileSource src
  Langlib.Velato.run (Langlib.Turpentine.Compile.Velato.renderProg prog) input fuel

/-- Run the source both ways and insist they agree: through the bespoke
backend, and through the Turpentine reference interpreter on the same program
with the compiler's own epilogue, `println(""); print(answer);`, appended. -/
def runBoth (src : String) (input : Input) (fuel : Nat) : Except String RunResult := do
  let p ← Langlib.Turpentine.parse src
  let _ ← (Langlib.Turpentine.checkProgram p).mapError ("type error: " ++ ·)
  let refProg : Langlib.Turpentine.Program :=
    { p with body := .seq p.body (.seq (.printStr "" true)
        (.printExpr (.var "answer") false)) }
  let refRes := Langlib.Turpentine.evalProgram refProg input fuel
  let vel ← bespokeVelato.compile p
  let velRes := Langlib.Velato.evalProg vel input fuel
  match refRes.exit, velRes.exit with
  | .halted, .halted =>
    if refRes.outputString == velRes.outputString then
      return velRes
    else
      return { exit := .error s!"disagreement: reference '{refRes.outputString}', \
        bespoke '{velRes.outputString}'" }
  | .halted, e => return { exit := .error s!"bespoke backend did not halt: {repr e}" }
  | e, _ => return { exit := .error s!"reference interpreter did not halt: {repr e}" }

/-- The behavioural theorem, executed: compile with the *behaviourally*
verified compiler, run source and target on the same stream, and insist that
the events they performed are the same list, in the same order, input
events included. `bespokeVelatoIO.encodeTrace` and `encodeInput` are both
the identity, so this is exactly what the instance claims, run rather than
proved. -/
def runTrace (src : String) (input : Input) (fuel : Nat) : Except String RunResult := do
  let p ← Langlib.Turpentine.parse src
  let _ ← (Langlib.Turpentine.checkProgram p).mapError ("type error: " ++ ·)
  let vel ← bespokeVelatoIO.compile p
  let srcTrace := Langlib.Turpentine.evalTrace (answerProgram p) input fuel
  let tgtTrace := TraceLang.trace (L := VelatoLang) vel (bespokeVelatoIO.encodeInput input) fuel
  let r := ProgLang.run (L := VelatoLang) vel (bespokeVelatoIO.encodeInput input) fuel
  match r.exit with
  | .halted =>
    if srcTrace == bespokeVelatoIO.encodeTrace tgtTrace then
      return { output := (String.intercalate "," (srcTrace.map reprStr)).toUTF8, exit := .halted }
    else
      return { exit := .error s!"trace disagreement: source {repr srcTrace}, \
        target {repr tgtTrace}" }
  | e => return { exit := .error s!"compiled program did not halt: {repr e}" }

/-- Run one program through both verified compilers for Velato and compare
the decoded answers: `bespokeVelato_agrees_derived`, executed. -/
def runAgree (src : String) (_input : Input) (fuel : Nat) : Except String RunResult := do
  let p ← Langlib.Turpentine.parse src
  let _ ← (Langlib.Turpentine.checkProgram p).mapError ("type error: " ++ ·)
  let v₁ ← bespokeVelato.compile p
  let v₂ ← derivedVelato.compile p
  let r₁ := ProgLang.run (L := VelatoLang) v₁ bespokeVelato.encodeInput fuel
  let r₂ := ProgLang.run (L := VelatoLang) v₂ derivedVelato.encodeInput fuel
  match r₁.exit, r₂.exit with
  | .halted, .halted =>
    match bespokeVelato.decodeOutput r₁.output, derivedVelato.decodeOutput r₂.output with
    | some a, some b =>
      if a == b then return { output := (toString a).toUTF8, exit := .halted }
      else return { exit := .error s!"disagreement: bespoke {a}, derived {b}" }
    | _, _ => return { exit := .error "an output did not decode as a number" }
  | .halted, e => return { exit := .error s!"derived compiler did not halt: {repr e}" }
  | e, _ => return { exit := .error s!"bespoke compiler did not halt: {repr e}" }

private def sumTo5 : String :=
  "var answer : int;\nvar i : int;\nwhile i < 5 { i := i + 1; answer := answer + i; }"

private def factorial6 : String :=
  "var answer : int;\nvar i : int;\nvar n : int;\n" ++
  "n := 6;\nanswer := 1;\nwhile i < n { i := i + 1; answer := answer * i; }"

/-- Sum the bytes of the input: `readByte` in a loop, stopping at the `-1`
Turpentine reports at end of input and the backend manufactures from
Velato's `0`. -/
private def sumBytes : String :=
  "var answer : int;\nvar c : int;\nc := readByte();\n" ++
  "while c != -1 { answer := answer + c; c := readByte(); }"

/-- Echo each byte's value on a line of its own, then the count: reads and
writes interleaved, which is what a trace test is for. -/
private def echoValues : String :=
  "var answer : int;\nvar c : int;\nc := readByte();\n" ++
  "while c != -1 { println(c); answer := answer + 1; c := readByte(); }"

def pipeline : Suite where
  name := "turpentine -> velato (bespoke, verified fragment)"
  run := run
  cases :=
    [ { name := "default zero", source := .inline "var answer : int;",
        expect := .outputs "\n0" }
    , { name := "constant", source := .inline "var answer : int; answer := 7;",
        expect := .outputs "\n7" }
    , { name := "nested arithmetic",
        source := .inline "var answer : int; answer := 2 * 3 + 4 * 5;",
        expect := .outputs "\n26" }
    , { name := "a negative answer", source := .inline "var answer : int; answer := 2 - 9;",
        expect := .outputs "\n-7" }
    , { name := "unary minus",
        source := .inline "var answer : int; var x : int; x := 4; answer := -x - 1;",
        expect := .outputs "\n-5" }
    , { name := "the six comparisons",
        source := .inline ("var answer : int; var b : bool; " ++
          "b := 5 <= 5; if b { answer := answer + 1; } else { } " ++
          "b := 6 > 2; if b { answer := answer + 10; } else { } " ++
          "b := 2 >= 7; if b { answer := answer + 100; } else { } " ++
          "b := 3 < 2; if b { answer := answer + 1000; } else { } " ++
          "b := 3 == 3; if b { answer := answer + 10000; } else { } " ++
          "b := 3 != 3; if b { answer := answer + 100000; } else { }"),
        expect := .outputs "\n10011" }
    , { name := "equality and inequality on booleans",
        source := .inline ("var answer : int; var b : bool; b := true != false; " ++
          "if b && (true == true) { answer := 1; } else { answer := 0; }"),
        expect := .outputs "\n1" }
    , { name := "boolean negation and short circuits",
        source := .inline ("var answer : int; var b : bool; b := !(3 < 2) && (2 < 1 || 1 < 2); " ++
          "if b { answer := 1; } else { answer := 0; }"),
        expect := .outputs "\n1" }
    , { name := "while loop", source := .inline sumTo5, expect := .outputs "\n15" }
    , { name := "factorial", source := .inline factorial6, expect := .outputs "\n720" }
    , { name := "strings, integers and booleans printed",
        source := .inline ("var answer : int; var i : int; " ++
          "while i < 3 { i := i + 1; print(\"i=\"); print(i); print(\" even=\"); " ++
          "println(i == 2); } answer := i;"),
        expect := .outputs "i=1 even=false\ni=2 even=true\ni=3 even=false\n\n3" }
    , { name := "reading bytes to the end of input", source := .inline sumBytes,
        input := "abc", expect := .outputs "\n294" }
    , { name := "reading from an empty stream", source := .inline sumBytes,
        expect := .outputs "\n0" }
    , { name := "reads and writes interleaved", source := .inline echoValues,
        input := "AZ", expect := .outputs "65\n90\n\n2" }
      -- the theorem is conditional on the source halting; a source loop that
      -- never ends compiles to a target loop that never ends.
    , { name := "a loop that never ends",
        source := .inline "var answer : int; while answer == 0 { }",
        expect := .diverges, fuel := 100_000 }
    ]

def differential : Suite where
  name := "bespoke velato vs turpentine reference"
  run := runBoth
  cases :=
    [ { name := "default zero", source := .inline "var answer : int;",
        expect := .outputs "\n0" }
    , { name := "arithmetic",
        source := .inline "var answer : int; answer := 2 * 3 + 4 * 5;",
        expect := .outputs "\n26" }
    , { name := "while loop", source := .inline sumTo5, expect := .outputs "\n15" }
    , { name := "factorial", source := .inline factorial6, expect := .outputs "\n720" }
    , { name := "short-circuit && against the reference interpreter",
        source := .inline ("var answer : int; var i : int; " ++
          "while i < 6 { i := i + 1; " ++
          "if i > 2 && i < 5 { answer := answer + i; } else { } }"),
        expect := .outputs "\n7" }
    , { name := "printing inside a loop, one line each",
        source := .inline ("var answer : int; var i : int; " ++
          "while i < 3 { i := i + 1; println(i * i); } answer := 0;"),
        expect := .outputs "1\n4\n9\n\n0" }
    , { name := "printing a boolean, false",
        source := .inline "var answer : int; var b : bool; b := 3 < 2; print(b); answer := 1;",
        expect := .outputs "false\n1" }
    , { name := "a negative integer printed",
        source := .inline "var answer : int; print(0 - 42); answer := 1;",
        expect := .outputs "-42\n1" }
    , { name := "summing the input bytes", source := .inline sumBytes,
        input := "velato", expect := .outputs "\n651" }
    , { name := "echoing byte values", source := .inline echoValues,
        input := "hi", expect := .outputs "104\n105\n\n2" }
    ]

/-- Programs both compilers accept: no initialisers, no subtraction, no
negative literals and no I/O. The derived compiler's programs do their
arithmetic on one Gödel number, so the values are kept small. -/
def agreement : Suite where
  name := "bespoke velato vs derived velato"
  run := runAgree
  cases :=
    [ { name := "default zero", source := .inline "var answer : int;",
        expect := .outputs "0" }
    , { name := "constant", source := .inline "var answer : int; answer := 3;",
        expect := .outputs "3" }
    , { name := "addition", source := .inline "var answer : int; answer := 2 + 2;",
        expect := .outputs "4" }
    ]

def rejections : Suite where
  name := "turpentine constructs outside the verified velato fragment"
  run := run
  cases :=
    [ { name := "printByte", source := .inline "var answer : int; printByte(65);",
        expect := .parseError "printByte" }
    , { name := "readInt", source := .inline "var answer : int; answer := readInt();",
        expect := .parseError "readInt" }
    , { name := "division", source := .inline "var answer : int; answer := 8 / 2;",
        expect := .parseError "'/' or '%'" }
    , { name := "modulo", source := .inline "var answer : int; answer := 8 % 3;",
        expect := .parseError "'/' or '%'" }
    , { name := "assert", source := .inline "var answer : int; assert answer == 0;",
        expect := .parseError "assert" }
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

/-- The behavioural instance, executed. What each case checks is the trace,
which `runTrace` compares before reporting anything. -/
def behavioural : Suite where
  name := "bespoke velato performs the source's events"
  run := fun src input fuel => do
    let r ← runTrace src input fuel
    match r.exit with
    | .halted => return { output := "traces agree".toUTF8, exit := .halted }
    | e => return { exit := e }
  cases :=
    [ { name := "a program that prints nothing of its own",
        source := .inline "var answer : int; answer := 7;",
        expect := .outputs "traces agree" }
    , { name := "printed integers",
        source := .inline ("var answer : int; var i : int; " ++
          "while i < 3 { i := i + 1; println(i); } answer := i;"),
        expect := .outputs "traces agree" }
    , { name := "strings, numbers and booleans interleaved",
        source := .inline ("var answer : int; var i : int; " ++
          "while i < 3 { i := i + 1; print(\"i=\"); print(i); print(\" even=\"); " ++
          "println(i == 2); } answer := i;"),
        expect := .outputs "traces agree" }
    , { name := "input events, read to the end", source := .inline sumBytes,
        input := "bytes", expect := .outputs "traces agree" }
    , { name := "input and output events interleaved", source := .inline echoValues,
        input := "xyz", expect := .outputs "traces agree" }
    , { name := "a read on an empty stream records nothing", source := .inline echoValues,
        expect := .outputs "traces agree" }
    ]

def suites : List Suite := [pipeline, differential, agreement, rejections, behavioural]

end Langlib.Tests.BespokeVelato
