import Langlib.Computability.JavaGen.CounterCompiler
import Langlib.Computability.JavaGen.Growth

/-! # Executable universal-compiler regressions

URM instructions and inputs are compiled as syntax. Expected answers are
independent constants; no source interpreter supplies the target's answer.
The universal theorem is assembled separately in `JavaGen.Main`.
-/

namespace Langlib.Tests.JavaGenCompiler
open Langlib.JavaGen Langlib.Computability.JavaGen
open Langlib.Computability.Counter

/-- Compiler examples share their definitions with the source-fixture generator. -/
def examples : List (String × Code × Nat × Option Nat) :=
  [("emit-three", [.emit, .emit, .emit], 0, some 3),
   ("transfer", [.inc 0, .inc 0, .loop 0 [.dec 0, .emit]], 1, some 2),
   ("empty-loop", [.inc 0, .loop 0 []], 1, none)]

def checks : IO (List String) := do
  let mut failures := []
  -- Reject incomplete/rejected records, prefer the last state query, and
  -- distinguish Letter_1 from neighbouring constructor names.
  let records : List (String × String × Option Nat) :=
    [("missing acceptance", "State_0<Letter_1<Z>> <: Z\n", none),
     ("missing control query", "accepted\nZ <: Z\n", none),
     ("rejected", "rejected\nState_0<Letter_1<Z>> <: Z\n", none),
     ("last query", "accepted\nState_0<Letter_1<Z>> <: Z\nState_1<Z> <: Z\n", some 0),
     ("whole names", "accepted\nState_0<Letter_11<Letter_10<Letter_1<Z>>>> <: Z\n", some 1)]
  for (name, text, want) in records do
    unless CounterCompiler.decodeOutput text.toUTF8 == want do
      failures := s!"decoder {name}: wrong answer" :: failures
  unless CounterCompiler.decodeOutput (ByteArray.mk #[255]) == none do
    failures := "decoder accepted invalid UTF-8" :: failures
  -- Both zero/nonzero loop paths, nested loops, and deletion of the last unit.
  let flows := examples ++
    [("zero-loop", [.loop 0 [.emit]], 1, some 0),
     ("nested-loop", [.inc 0, .inc 0, .loop 0 [.dec 0, .inc 1,
       .loop 1 [.dec 1, .emit]]], 2, some 2)]
  for (name, code, bound, want) in flows do
    match CounterCompiler.compileFlow (CounterCompiler.counterFlow code) bound with
    | .error e => failures := s!"{name}: {e}" :: failures
    | .ok p =>
      let result := evalProg p 10000
      let actual := CounterCompiler.decodeOutput result.output
      if (want.isSome && (result.exit != .halted || actual != want)) ||
          (want.isNone && result.exit != .outOfFuel) then
        failures := s!"{name}: {repr result.exit}, decoded {repr actual}, want {repr want}" :: failures
      match parse p.source.render with
      | .error e => failures := s!"{name} source: {e}" :: failures
      | .ok parsed =>
        unless parsed == p do failures := s!"{name}: generated source changed the prepared machine" :: failures
  let samples : List (String × Cslib.URM.Program × List Nat × Option Nat) :=
    [("empty/zero", [], [], some 0),
     ("empty/nonzero", [], [3], some 3),
     ("successor", [.S 0], [2], some 3),
     ("zero", [.Z 0], [3], some 0),
     ("copy", [.T 1 0], [0, 2], some 2),
     ("unequal jump", [.J 0 1 0], [1, 2], some 1),
     ("self jump", [.J 0 0 0], [], none)]
  for (name, source, inputs, want) in samples do
    match CounterCompiler.compileURM source inputs with
    | .error e => failures := s!"URM {name}: {e}" :: failures
    | .ok p =>
      let result := evalProg p 20000
      let actual := CounterCompiler.decodeOutput result.output
      if (want.isSome && (result.exit != .halted || actual != want)) ||
          (want.isNone && result.exit != .outOfFuel) then
        failures := s!"URM {name}: {repr result.exit}, decoded {repr actual}, want {repr want}" :: failures
      if want.isNone then
        for fuel in [0, 1, 7, 100] do
          unless (evalProg p fuel).exit == .outOfFuel do
            failures := s!"URM {name}: completed at fuel {fuel}" :: failures
  match CounterCompiler.compileFlow [.inc 2 1] 1 with
  | .error _ => pure ()
  | .ok _ => failures := "out-of-range flow register was accepted" :: failures
  return failures.reverse

end Langlib.Tests.JavaGenCompiler
