import Langlib.Common.Runner
import Langlib.Languages.Subleq.Semantics

/-!
# Subleq: standalone runner

```
lake exe subleq [--fuel N] file.sq
```
-/

namespace Langlib.Subleq

open Langlib.Common

def runner : Runner where
  name := "subleq"
  ext := "sq"
  run := run

end Langlib.Subleq

def main (args : List String) : IO UInt32 :=
  Langlib.Subleq.runner.main args
