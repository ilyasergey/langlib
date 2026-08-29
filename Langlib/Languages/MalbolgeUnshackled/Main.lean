import Langlib.Common.Runner
import Langlib.Languages.MalbolgeUnshackled.Semantics

/-!
# Malbolge Unshackled: standalone runner

```
lake exe malbolge-unshackled [--fuel N] [--rot-width N] [--strict] file.mu
```

`.mu` is the customary extension. Two flags beyond the shared ones, both
corresponding to freedoms of the language rather than of the runner:

* `--rot-width N` sets the starting rotation width. The language promises
  only that it is at least 10 and that it grows when `j` widens `d`, so a
  correct program has to work at every setting. Values below 10 are raised
  to 10. Johansen's interpreter randomises this (and its growth steps) on
  every run for exactly this reason; ours is deterministic and lets you
  sweep it by hand.
* `--strict` is Johansen's `-n`: reject source characters outside 33..126
  rather than loading them unchecked.

Many Malbolge and Unshackled programs never halt by design (both cat
programs, the truth-machine on `1`); run those with a modest `--fuel`.
-/

namespace Langlib.MalbolgeUnshackled

open Langlib.Common

def runner (cfg : Config) : Runner where
  name := "malbolge-unshackled"
  ext := "mu"
  run := runWith cfg
  usageExtra :=
    [ "  --rot-width N  starting rotation width (default 10, the minimum the"
    , "                 language allows; correct programs work at any setting)"
    , "  --strict       reject source characters outside 33..126 (Johansen's -n)" ]

end Langlib.MalbolgeUnshackled

open Langlib.MalbolgeUnshackled in
def main (args : List String) : IO UInt32 := do
  -- Pre-process the language-specific flags, then delegate.
  let mut cfg : Config := {}
  let mut rest : List String := []
  let mut args := args
  repeat
    match args with
    | [] => break
    | "--strict" :: rs => cfg := { cfg with strict := true }; args := rs
    | "--rot-width" :: n :: rs =>
      match n.toNat? with
      | some k => cfg := { cfg with rotWidth := k }; args := rs
      | none =>
        IO.eprintln s!"malbolge-unshackled: --rot-width expects a number, got '{n}'"
        return 3
    | a :: rs => rest := a :: rest; args := rs
  (runner cfg).main rest.reverse
