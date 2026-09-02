import Langlib.Common.TestHarness
import Langlib.Tests.Befunge93
import Langlib.Tests.Brainfuck
import Langlib.Tests.BoundedMalbolge
import Langlib.Tests.Brainloller
import Langlib.Tests.BeerSong
import Langlib.Tests.BespokeSubleq
import Langlib.Tests.BespokeWhitespace
import Langlib.Tests.CompileBrainfuck
import Langlib.Tests.CompileBrainloller
import Langlib.Tests.CompileFractran
import Langlib.Tests.CompileMalbolge
import Langlib.Tests.CompileMalbolgeUnshackled
import Langlib.Tests.CompilePiet
import Langlib.Tests.CompileOok
import Langlib.Tests.CompileSubleq
import Langlib.Tests.CompileWhitespace
import Langlib.Tests.Conformance
import Langlib.Tests.ConformanceHand
import Langlib.Tests.DerivedFractran
import Langlib.Tests.DerivedPiet
import Langlib.Tests.DerivedSubleq
import Langlib.Tests.DerivedWhitespace
import Langlib.Tests.Deadfish
import Langlib.Tests.Fractran
import Langlib.Tests.Malbolge
import Langlib.Tests.MalbolgeUnshackled
import Langlib.Tests.Ook
import Langlib.Tests.Piet
import Langlib.Tests.Ski
import Langlib.Tests.Subleq
import Langlib.Tests.URMFractran
import Langlib.Tests.SubleqTrace
import Langlib.Tests.TurpentineTrace
import Langlib.Tests.WhitespaceTrace
import Langlib.Tests.URMBrainfuck
import Langlib.Tests.URMPiet
import Langlib.Tests.URMSubleq
import Langlib.Tests.URMThue
import Langlib.Tests.URMSki
import Langlib.Tests.URMUnlambda
import Langlib.Tests.DerivedThue
import Langlib.Tests.Thue
import Langlib.Tests.Whitespace
import Langlib.Tests.Turpentine
import Langlib.Tests.Unlambda
import Langlib.Tests.Velato
import Langlib.Tests.URMVelato

/-!
Test driver for langlib, run by `lake test` (from the repository root; the
suites read example programs by relative path).

Each language contributes suites from `Langlib/Tests/<Langname>.lean`.
-/

/-! Checks that are properties of a pair of functions rather than golden
outputs, so they do not fit the `Suite` shape: each returns the problems it
found, and an empty list is a pass. -/

open Langlib.Common in
def propertyChecks : List (String × IO (List String)) :=
  [ ("velato: emit round-trips through the parser", Langlib.Tests.Velato.emitRoundTrips)
  , ("velato: MIDI round-trips through the reader", Langlib.Tests.Velato.midiRoundTrips) ]

open Langlib.Common in
def main : IO UInt32 := do
  let suiteCode ← runSuites <| List.flatten
    [ Langlib.Tests.Befunge93.suites
    , Langlib.Tests.Brainfuck.suites
    , Langlib.Tests.BoundedMalbolge.suites
    , Langlib.Tests.Brainloller.suites
    , Langlib.Tests.BespokeSubleq.suites
    , Langlib.Tests.BespokeWhitespace.suites
    , Langlib.Tests.CompileBrainfuck.suites
    , Langlib.Tests.CompileBrainloller.suites
    , Langlib.Tests.CompileFractran.suites
    , Langlib.Tests.CompileMalbolge.suites
    , Langlib.Tests.CompileMalbolgeUnshackled.suites
    , Langlib.Tests.CompilePiet.suites
    , Langlib.Tests.CompileOok.suites
    , Langlib.Tests.CompileSubleq.suites
    , Langlib.Tests.CompileWhitespace.suites
    , Langlib.Tests.Conformance.suites
    , Langlib.Tests.ConformanceHand.suites
    , Langlib.Tests.DerivedFractran.suites
    , Langlib.Tests.DerivedPiet.suites
    , Langlib.Tests.DerivedSubleq.suites
    , Langlib.Tests.DerivedThue.suites
    , Langlib.Tests.DerivedWhitespace.suites
    , Langlib.Tests.Deadfish.suites
    , Langlib.Tests.Fractran.suites
    , Langlib.Tests.Malbolge.suites
    , Langlib.Tests.MalbolgeUnshackled.suites
    , Langlib.Tests.Ook.suites
    , Langlib.Tests.Piet.suites
    , Langlib.Tests.Ski.suites
    , Langlib.Tests.Subleq.suites
    , Langlib.Tests.SubleqTrace.suites
    , Langlib.Tests.TurpentineTrace.suites
    , Langlib.Tests.WhitespaceTrace.suites
    , Langlib.Tests.URMBrainfuck.suites
    , Langlib.Tests.URMFractran.suites
    , Langlib.Tests.URMPiet.suites
    , Langlib.Tests.URMThue.suites
    , Langlib.Tests.URMSki.suites
    , Langlib.Tests.URMUnlambda.suites
    , Langlib.Tests.URMSubleq.suites
    , Langlib.Tests.Thue.suites
    , Langlib.Tests.Whitespace.suites
    , Langlib.Tests.Turpentine.suites
    , Langlib.Tests.Unlambda.suites
    , Langlib.Tests.Velato.suites
    , Langlib.Tests.URMVelato.suites
    ]
  let mut failures := 0
  for (name, check) in propertyChecks do
    let problems ← check
    if problems.isEmpty then
      IO.println s!"PASS {name}"
    else
      failures := failures + problems.length
      IO.println s!"FAIL {name}"
      for p in problems.take 10 do
        IO.println s!"  {p}"
  return if failures == 0 then suiteCode else 1
