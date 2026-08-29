import Langlib.Common.Runner
import Langlib.Languages.Ski.Semantics

/-!
# SKI: standalone runner

```
lake exe ski [--fuel N] [--verbose] file.ski
```

The term is reduced in normal order and its normal form is printed. There
is no input; stdin is ignored.
-/

namespace Langlib.Ski

open Langlib.Common

def runner : Runner where
  name := "ski"
  ext := "ski"
  run := run
  defaultFuel := 1_000_000
  usageExtra :=
    [ "  a fuel unit is one normal-order reduction step; the normal form is"
    , "  printed on standard output, and a term with no normal form runs out"
    , "  of fuel instead" ]

end Langlib.Ski

def main (args : List String) : IO UInt32 :=
  Langlib.Ski.runner.main args
