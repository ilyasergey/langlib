import Langlib.Tests.CompileFractran
import Langlib.Languages.Turpentine.Compile.JavaGen
import Langlib.Languages.Turpentine.Semantics

/-! # Turpentine-to-JavaGen differential tests

The shared Minsky front end accepts the same fragment as bespoke FRACTRAN.
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
  cases := CompileFractran.rejected.cases.map fun c =>
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

def suites : List Suite := [compiled, reference, rejected, loops]
end Langlib.Tests.CompileJavaGen
