import Langlib.Common.Runner
import Langlib.Languages.Befunge93.Semantics

/-!
# Befunge-93: standalone runner

```
lake exe befunge93 [--fuel N] [--seed K] file.b93
```

The customary extension in the wild is `.bf`, which in langlib already
belongs to brainfuck's neighbourhood; we use `.b93` (any extension works,
the usage line is just advice). `--seed K` seeds the `?` direction
generator; the default (1993) makes `?` deterministic across runs.
-/

namespace Langlib.Befunge93

open Langlib.Common

def runner (cfg : Config) : Runner where
  name := "befunge93"
  ext := "b93"
  run := run cfg
  usageExtra :=
    ["  --seed K   seed for the '?' direction generator (default: 1993)"]

end Langlib.Befunge93

open Langlib.Befunge93 in
def main (args : List String) : IO UInt32 := do
  -- Pre-process the language-specific --seed flag, then delegate.
  let mut seed : UInt64 := ({} : Config).seed
  let mut rest : List String := []
  let mut args := args
  repeat
    match args with
    | [] => break
    | "--seed" :: k :: rs =>
      match k.toNat? with
      | some n => seed := UInt64.ofNat n; args := rs
      | none =>
        IO.eprintln s!"befunge93: --seed expects a number, got '{k}'"
        return 3
    | a :: rs => rest := a :: rest; args := rs
  (runner { seed }).main rest.reverse
