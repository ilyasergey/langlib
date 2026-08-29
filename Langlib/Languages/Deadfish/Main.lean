import Langlib.Common.Runner
import Langlib.Languages.Deadfish.Semantics

/-!
# Deadfish: standalone runner

```
lake exe deadfish [--fuel N] file.df
```

Batch mode: the program file is read and executed; the interactive `>> `
prompt of Skinner's original shell is not printed (see `docs/deadfish/spec.md`).
Stdin is ignored; Deadfish has no input commands.
-/

namespace Langlib.Deadfish

open Langlib.Common

def runner : Runner where
  name := "deadfish"
  ext := "df"
  run := run
  usageExtra :=
    ["  (deadfish has no input commands; stdin is ignored)"]

end Langlib.Deadfish

def main (args : List String) : IO UInt32 :=
  Langlib.Deadfish.runner.main args
