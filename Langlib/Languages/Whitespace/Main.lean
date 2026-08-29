import Langlib.Common.Runner
import Langlib.Languages.Whitespace.Semantics

/-!
# Whitespace: standalone runner

```
lake exe whitespace [--fuel N] file.ws
```
-/

namespace Langlib.Whitespace

open Langlib.Common

def runner : Runner where
  name := "whitespace"
  ext := "ws"
  run := run

end Langlib.Whitespace

def main (args : List String) : IO UInt32 :=
  Langlib.Whitespace.runner.main args
