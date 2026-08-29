import Langlib.Common.Runner
import Langlib.Languages.Fractran.Semantics

/-!
# FRACTRAN: standalone runner

```
lake exe fractran [--fuel N] [--n N] [--out trajectory|final|pow2] file.ft
```

The starting value comes from `--n N`, or, if the flag is absent, from the
first line of stdin.
-/

namespace Langlib.Fractran

open Langlib.Common

def runner (cfg : Config) : Runner where
  name := "fractran"
  ext := "ft"
  run := run cfg
  usageExtra :=
    [ "  --n N      starting value (positive integer); if absent, read from stdin's first line"
    , "  --out MODE what to print: trajectory (default), final, pow2" ]

end Langlib.Fractran

open Langlib.Fractran in
def main (args : List String) : IO UInt32 := do
  -- Pre-process the language-specific --n and --out flags, then delegate.
  let mut cfg : Config := {}
  let mut rest : List String := []
  let mut args := args
  repeat
    match args with
    | [] => break
    | "--n" :: n :: rs =>
      match n.toNat? with
      | some k => cfg := { cfg with n? := some k }; args := rs
      | none =>
        IO.eprintln s!"fractran: --n expects a decimal integer, got '{n}'"
        return 3
    | "--out" :: m :: rs =>
      match m with
      | "trajectory" => cfg := { cfg with out := .trajectory }; args := rs
      | "final" => cfg := { cfg with out := .final }; args := rs
      | "pow2" => cfg := { cfg with out := .pow2 }; args := rs
      | _ =>
        IO.eprintln s!"fractran: unknown --out mode '{m}' (trajectory|final|pow2)"
        return 3
    | a :: rs => rest := a :: rest; args := rs
  (runner cfg).main rest.reverse
