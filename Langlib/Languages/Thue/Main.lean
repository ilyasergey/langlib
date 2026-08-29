import Langlib.Common.Runner
import Langlib.Languages.Thue.Semantics

/-!
# Thue: standalone runner

```
lake exe thue [--fuel N] [--strategy first|random] [--seed K] [--final-state] file.t
```
-/

namespace Langlib.Thue

open Langlib.Common

def runner (cfg : Config) : Runner where
  name := "thue"
  ext := "t"
  run := run cfg
  defaultFuel := 1_000_000
  usageExtra :=
    [ "  --strategy S  rule selection: first (deterministic, default) or random"
    , "  --seed K      PRNG seed for --strategy random (default: 0)"
    , "  --final-state on a normal halt, also print the final state and a newline" ]

end Langlib.Thue

open Langlib.Thue in
def main (args : List String) : IO UInt32 := do
  -- Pre-process the language-specific flags, then delegate.
  let mut random := false
  let mut seed : UInt64 := 0
  let mut finalState := false
  let mut rest : List String := []
  let mut args := args
  repeat
    match args with
    | [] => break
    | "--strategy" :: s :: rs =>
      match s with
      | "first" => random := false; args := rs
      | "random" => random := true; args := rs
      | _ =>
        IO.eprintln s!"thue: unknown --strategy '{s}' (first|random)"
        return 3
    | "--seed" :: k :: rs =>
      match k.toNat? with
      | some n => seed := UInt64.ofNat n; args := rs
      | none =>
        IO.eprintln s!"thue: --seed expects a number, got '{k}'"
        return 3
    | "--final-state" :: rs => finalState := true; args := rs
    | a :: rs => rest := a :: rest; args := rs
  let strategy := if random then Strategy.random seed else .first
  (runner { strategy, finalState }).main rest.reverse
