import Langlib.Common.TestHarness
import Langlib.Tests.Brainfuck
import Langlib.Tests.Fractran
import Langlib.Tests.Subleq
import Langlib.Tests.WTF

/-!
Test driver for langlib, run by `lake test` (from the repository root; the
suites read example programs by relative path).

Each language contributes suites from `Langlib/Tests/<Langname>.lean`.
-/

open Langlib.Common in
def main : IO UInt32 :=
  runSuites <| List.flatten
    [ Langlib.Tests.Brainfuck.suites
    , Langlib.Tests.Fractran.suites
    , Langlib.Tests.Subleq.suites
    , Langlib.Tests.WTF.suites
    ]
