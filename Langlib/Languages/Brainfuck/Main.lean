import Langlib.Common.Runner
import Langlib.Languages.Brainfuck.Semantics

/-!
# Brainfuck: standalone runner

```
lake exe brainfuck [--fuel N] [--eof unchanged|zero|minus1] file.b
```
-/

namespace Langlib.Brainfuck

open Langlib.Common

def runner (cfg : Config) : Runner where
  name := "brainfuck"
  ext := "b"
  run := run cfg
  usageExtra :=
    ["  --eof MODE what ',' stores at end of input: unchanged (default), zero, minus1"]

end Langlib.Brainfuck

open Langlib.Brainfuck in
def main (args : List String) : IO UInt32 := do
  -- Pre-process the language-specific --eof flag, then delegate.
  let mut eof : EofMode := .unchanged
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
        IO.eprintln s!"brainfuck: unknown --eof mode '{m}' (unchanged|zero|minus1)"
        return 3
    | a :: rs => rest := a :: rest; args := rs
  (runner { eof }).main rest.reverse
