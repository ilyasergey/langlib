import Langlib.Common.Runner
import Langlib.Languages.Malbolge.Semantics

/-!
# Malbolge: standalone runner

```
lake exe malbolge [--fuel N] file.mal
```

`.mal` is the customary extension; `.mb` is also seen in the wild (the
runner does not care). Note that many classic Malbolge programs (both cat
programs, the truth-machine on input `1`) never halt by design; run them
with a modest `--fuel`.
-/

namespace Langlib.Malbolge

open Langlib.Common

def runner : Runner where
  name := "malbolge"
  ext := "mal"
  run := run

end Langlib.Malbolge

def main (args : List String) : IO UInt32 :=
  Langlib.Malbolge.runner.main args
