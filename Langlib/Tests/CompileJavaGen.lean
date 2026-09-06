import Langlib.Tests.CompileFractran
import Langlib.Languages.Turpentine.Compile.JavaGen
import Langlib.Languages.Turpentine.Semantics

/-! # Turpentine-to-JavaGen differential tests

The shared Minsky front end adds an array-enabled layout for JavaGen.
Run its arithmetic/control-flow fixtures both on the Turpentine interpreter
(printing `answer` afterwards) and on the emitted, reparsed JavaGen source.
Also check divergence, rejected source constructs, and agreement of the
compact answer observation with the ordinary proof-record evaluator.
-/

namespace Langlib.Tests.CompileJavaGen
open Langlib.Common Langlib.Turpentine.Compile

def compiled : Suite where
  name := "turpentine -> javagen"
  run := JavaGen.runCompiled
  cases := CompileFractran.compiled.cases

def reference : Suite where
  name := "turpentine -> javagen (source answers)"
  run := fun src => Langlib.Turpentine.run (src ++ "\nprintln(answer);\n")
  cases := compiled.cases.map fun c =>
    -- The shared Minsky pass defines total arithmetic at zero divisors;
    -- Turpentine instead errors. Pin both sides of this documented boundary.
    if c.name == "division by zero does not trap" then
      { c with expect := .runtimeError "division by zero" }
    else if c.name == "modulo by zero gives the dividend" then
      { c with expect := .runtimeError "modulo by zero" }
    else c

def rejected : Suite where
  name := "turpentine -> javagen (rejected constructs)"
  run := JavaGen.runCompiled
  cases := (CompileFractran.rejected.cases.filter (·.name != "an array")).map fun c =>
    { c with expect := match c.expect with
        | .parseError m => .parseError (m.replace "fractran" "javagen")
        | e => e }

def loops : Suite where
  name := "turpentine -> javagen (nontermination)"
  run := JavaGen.runCompiled
  cases :=
    [ { name := "empty infinite loop", source := .inline
          "var answer : int; while true {}", fuel := 1000, expect := .diverges }
    , { name := "growing loop", source := .inline
          "var answer : int; while true { answer := answer + 1; }",
        fuel := 10000, expect := .diverges }
    , { name := "failed assertion", source := .inline
          "var answer : int := 3; assert answer == 4;", fuel := 1000, expect := .diverges }
    , { name := "zero iterations", source := .inline
          "var answer : int := 2; while false { answer := 9; }", expect := .outputs "2\n" }
    , { name := "nested loops", source := .inline
          "var answer : int; var i : int; var j : int; while i < 2 { j := 0; while j < 3 { answer := answer + 1; j := j + 1; } i := i + 1; }",
        expect := .outputs "6\n" }
    ]

def checks : IO (List String) := do
  let mut failures := []
  for n in [0, 1, 3] do
    match JavaGen.compileSource s!"var answer : int := {n};" >>= Langlib.JavaGen.parse with
    | .error e => failures := e :: failures
    | .ok p =>
      for fuel in [0, 1, 7, 100, 1000] do
        let ordinary := Langlib.JavaGen.evalProg p fuel
        let compact := Langlib.JavaGen.CompiledAnswer.exec p fuel p.source.query none
        unless ordinary.exit == compact.exit do
          failures := s!"answer {n}, fuel {fuel}: observation changed the exit" :: failures
        if ordinary.exit == .halted then
          let last := ((ordinary.outputString.splitOn "\n").reverse.find?
            (·.startsWith "State_")).getD ""
          unless (last.splitOn "Letter_1<").length - 1 == n &&
              compact.outputString == s!"{n}\n" do
            failures := s!"answer {n}: compact observation disagrees with proof record" :: failures
  match Langlib.JavaGen.CompiledAnswer.run "zero Z; check Z <: Z;" Input.empty 10 with
  | .ok { exit := .error _, .. } => pure ()
  | _ => failures := "an unrelated closed query was decoded as a counter answer" :: failures
  return failures.reverse

def arrayCases : List TestCase :=
  [ { name := "zero-initialized int and bool arrays", source := .inline
        "var answer : int; var a : int[2]; var b : bool[2]; if !b[1] { answer := a[0] + len(a) + len(b); }",
      expect := .outputs "4\n" }
  , { name := "last element of adjacent arrays", source := .inline
        "var answer : int; var a : int[2]; var b : int[2]; var i : int := 1; a[i] := 5; b[i] := 8; answer := a[i] + b[i];",
      expect := .outputs "13\n" }
  , { name := "initializer reads an earlier array", source := .inline
        "var a : int[2]; var answer : int := a[1] + len(a);", expect := .outputs "2\n" }
  , { name := "read and write the same indexed cell", source := .inline
        "var answer : int; var a : int[2]; var i : int := 1; a[i] := 4; a[i] := a[i] + 2; answer := a[i];",
      expect := .outputs "6\n" }
  , { name := "index and RHS refer to the cell being written", source := .inline
        "var answer : int; var a : int[2]; a[a[0]] := a[0] + 1; answer := a[0];",
      expect := .outputs "1\n" }
  , { name := "and skips an invalid read", source := .inline
        "var answer : int := 7; var a : bool[1]; if false && a[1] { answer := 9; }",
      expect := .outputs "7\n" }
  , { name := "or skips an invalid read", source := .inline
        "var answer : int; var a : bool[1]; if true || a[1] { answer := 1; }",
      expect := .outputs "1\n" }
  , { name := "while recomputes its guarded array condition", source := .inline
        "var answer : int; var a : bool[2]; a[0] := true; a[1] := true; while answer < len(a) && a[answer] { answer := answer + 1; }",
      expect := .outputs "2\n" }
  , { name := "prefix sums example", source := .file "Langlib/Examples/Turpentine/array-prefix.turp",
      expect := .outputs "10\n", fuel := 200000000 }
  , { name := "histogram example", source := .file "Langlib/Examples/Turpentine/array-histogram.turp",
      expect := .outputs "2\n", fuel := 200000000 }
  , { name := "Boolean marks example", source := .file "Langlib/Examples/Turpentine/array-marks.turp",
      expect := .outputs "3\n", fuel := 200000000 }
  , { name := "Fibonacci table example", source := .file "Langlib/Examples/Turpentine/array-fibonacci.turp",
      expect := .outputs "8\n", fuel := 200000000 }
  , { name := "existing maximum example", source := .file "Langlib/Examples/Turpentine/maxelem-tc.turp",
      expect := .outputs "9\n", fuel := 200000000 }
  , { name := "existing sieve example", source := .file "Langlib/Examples/Turpentine/sieve-tc.turp",
      expect := .outputs "15\n", fuel := 200000000 }
  ]

def arrays : Suite where
  name := "turpentine -> javagen (arrays)"
  run := JavaGen.runCompiled
  cases := arrayCases

def arrayReference : Suite where
  name := "turpentine -> javagen (array source answers)"
  run := reference.run
  cases := arrayCases

def boundsCases : List TestCase :=
  [ { name := "constant read at length", source := .inline
        "var answer : int; var a : int[1]; answer := a[1];", expect := .diverges, fuel := 1000 }
  , { name := "dynamic read beyond length", source := .inline
        "var answer : int; var a : int[2]; var i : int := 3; answer := a[i];", expect := .diverges, fuel := 1000 }
  , { name := "constant write at length", source := .inline
        "var answer : int; var a : int[1]; a[1] := 9;", expect := .diverges, fuel := 1000 }
  , { name := "dynamic write beyond length", source := .inline
        "var answer : int; var a : int[2]; var i : int := 3; a[i] := 9;", expect := .diverges, fuel := 1000 }
  , { name := "and evaluates its needed RHS", source := .inline
        "var answer : int; var a : bool[1]; if true && a[1] { answer := 1; }", expect := .diverges, fuel := 1000 }
  , { name := "or evaluates its needed RHS", source := .inline
        "var answer : int; var a : bool[1]; if false || a[1] { answer := 1; }", expect := .diverges, fuel := 1000 }
  ]

def bounds : Suite where
  name := "turpentine -> javagen (array bounds traps)"
  run := JavaGen.runCompiled
  cases := boundsCases

def boundsReference : Suite where
  name := "turpentine -> javagen (source bounds errors)"
  run := reference.run
  cases := boundsCases.map (fun c => { c with expect := .runtimeError "out of bounds" })

def suites : List Suite :=
  [compiled, reference, rejected, loops, arrays, arrayReference, bounds, boundsReference]
end Langlib.Tests.CompileJavaGen
