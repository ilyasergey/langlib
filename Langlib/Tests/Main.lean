import Langlib.Common.TestHarness
import Langlib.Tests.Befunge93
import Langlib.Tests.Brainfuck
import Langlib.Tests.Brainloller
import Langlib.Tests.Deadfish
import Langlib.Tests.Fractran
import Langlib.Tests.Malbolge
import Langlib.Tests.Ook
import Langlib.Tests.Piet
import Langlib.Tests.Subleq
import Langlib.Tests.Thue
import Langlib.Tests.Whitespace
import Langlib.Tests.Turpentine

/-!
Test driver for langlib, run by `lake test` (from the repository root; the
suites read example programs by relative path).

Each language contributes suites from `Langlib/Tests/<Langname>.lean`.
-/

open Langlib.Common in
def main : IO UInt32 :=
  runSuites <| List.flatten
    [ Langlib.Tests.Befunge93.suites
    , Langlib.Tests.Brainfuck.suites
    , Langlib.Tests.Brainloller.suites
    , Langlib.Tests.Deadfish.suites
    , Langlib.Tests.Fractran.suites
    , Langlib.Tests.Malbolge.suites
    , Langlib.Tests.Ook.suites
    , Langlib.Tests.Piet.suites
    , Langlib.Tests.Subleq.suites
    , Langlib.Tests.Thue.suites
    , Langlib.Tests.Whitespace.suites
    , Langlib.Tests.Turpentine.suites
    ]
