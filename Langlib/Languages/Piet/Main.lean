import Langlib.Common.Runner
import Langlib.Languages.Piet.Semantics

/-!
# Piet: standalone runner

```
lake exe piet [--fuel N] [--codel-size N] [--unknown-white] file.ppm
```

The program image must be a PPM; the runner reads files as text, so use
ASCII P3 (convert anything with `magick prog.png -compress none
prog.ppm`). Binary P6 is supported by the library
(`Langlib.Common.Image.parsePpm`) for direct users of the API.
-/

namespace Langlib.Piet

open Langlib.Common

def runner (cfg : Config) : Runner where
  name := "piet"
  ext := "ppm"
  run := run cfg
  usageExtra :=
    [ "  --codel-size N  pixels per codel side (default 1; no auto-detection)"
    , "  --unknown-white read colours outside the Piet palette as white"
    , "                  (default: they are a parse error)"
    , "  images must be ASCII PPM (P3); convert with e.g."
    , "    magick prog.png -compress none prog.ppm" ]

end Langlib.Piet

open Langlib.Piet in
def main (args : List String) : IO UInt32 := do
  -- Pre-process the language-specific flags, then delegate.
  let mut cfg : Config := {}
  let mut rest : List String := []
  let mut args := args
  repeat
    match args with
    | [] => break
    | "--codel-size" :: n :: rs =>
      match n.toNat? with
      | some k =>
        if k == 0 then
          IO.eprintln "piet: --codel-size must be at least 1"
          return 3
        cfg := { cfg with codelSize := k }; args := rs
      | none =>
        IO.eprintln s!"piet: --codel-size expects a number, got '{n}'"
        return 3
    | "--unknown-white" :: rs =>
      cfg := { cfg with unknownWhite := true }; args := rs
    | a :: rs => rest := a :: rest; args := rs
  (runner cfg).main rest.reverse
