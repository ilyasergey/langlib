import Langlib.Common.Runner
import Langlib.Languages.Unlambda.Semantics

/-!
# Unlambda: standalone runner

```
lake exe unlambda [--fuel N] [--verbose] file.unl
```

The program comes from the file and its input from stdin. Madore's
interpreters read the program from standard input when given no file, in
which case the program's input follows the program in the same stream; we
keep the two apart, so a file argument is required.
-/

namespace Langlib.Unlambda

open Langlib.Common

def runner : Runner where
  name := "unlambda"
  ext := "unl"
  run := run
  usageExtra :=
    [ "  a fuel unit is one evaluator step: one expression evaluated, one"
    , "  application performed, or one value returned to a continuation" ]

end Langlib.Unlambda

def main (args : List String) : IO UInt32 :=
  Langlib.Unlambda.runner.main args
