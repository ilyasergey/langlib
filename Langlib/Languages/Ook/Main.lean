import Langlib.Common.Runner
import Langlib.Languages.Ook.Semantics

/-!
# Ook!: standalone runner

```
lake exe ook [--fuel N] [--eof unchanged|zero|minus1] file.ook
```

The `--eof` flag is inherited from brainfuck, since the runtime is.
-/

namespace Langlib.Ook

open Langlib.Common

def runner (cfg : Config) : Runner where
  name := "ook"
  ext := "ook"
  run := run cfg
  usageExtra :=
    ["  --eof MODE what 'Ook. Ook!' stores at end of input: unchanged (default), zero, minus1"]

end Langlib.Ook

open Langlib.Ook in
def main (args : List String) : IO UInt32 := do
  -- Pre-process the language-specific --eof flag, then delegate.
  let mut eof : Langlib.Brainfuck.EofMode := .unchanged
  let mut rest : List String := []
  let mut args := args
  repeat
    match args with
    | [] => break
    | "--eof" :: m :: rs =>
      match m with
      | "unchanged" => eof := .unchanged; args := rs
      | "zero" => eof := .zero; args := rs
      | "minus1" => eof := .minusOne; args := rs
      | _ =>
        IO.eprintln s!"ook: unknown --eof mode '{m}' (unchanged|zero|minus1)"
        return 3
    | a :: rs => rest := a :: rest; args := rs
  (runner { eof }).main rest.reverse
