import Langlib.Common.Runner
import Langlib.Languages.Piet.Semantics

/-!
# Piet: standalone runner

```
lake exe piet [--fuel N] [--codel-size N] [--unknown-white] file.ppm
lake exe piet --svg out.svg [--codel-size N] [--scale N] [--grid] file.ppm
```

`--svg` renders the program instead of running it, one square per codel, so
a Piet program can be looked at in a browser or a documentation page. The
images in `docs/piet/` are produced this way.

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
    , "  --svg PATH      render the program as SVG instead of running it"
    , "  --scale N       SVG pixels per codel side (default 12, with --svg)"
    , "  --grid          draw codel boundaries in the SVG"
    , "  images must be ASCII PPM (P3); convert with e.g."
    , "    magick prog.png -compress none prog.ppm" ]

/-- `--svg`: read the program image, sample it at the configured codel
size, and write an SVG of it. Nothing is executed. -/
def renderSvg (cfg : Config) (scale : Nat) (grid : Bool) (out : String)
    (args : List String) : IO UInt32 := do
  match args with
  | [file] =>
    let data ← try
        IO.FS.readBinFile file
      catch e =>
        IO.eprintln s!"piet: cannot read {file}: {e}"
        return 3
    match Image.parsePpm data with
    | .error msg =>
      IO.eprintln s!"piet: {file}: {msg}"
      return 3
    | .ok img =>
      let img := img.sample cfg.codelSize
      IO.FS.writeFile out (img.toSvg scale grid)
      IO.println s!"piet: wrote {img.width}x{img.height} codels to {out}"
      return 0
  | [] =>
    IO.eprintln "piet: --svg needs a program file"
    return 3
  | _ =>
    IO.eprintln "piet: --svg takes exactly one program file"
    return 3

end Langlib.Piet

open Langlib.Piet in
def main (args : List String) : IO UInt32 := do
  -- Pre-process the language-specific flags, then delegate.
  let mut cfg : Config := {}
  let mut svg? : Option String := none
  let mut scale : Nat := 12
  let mut grid : Bool := false
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
    | "--svg" :: path :: rs =>
      svg? := some path; args := rs
    | "--scale" :: n :: rs =>
      match n.toNat? with
      | some k =>
        if k == 0 then
          IO.eprintln "piet: --scale must be at least 1"
          return 3
        scale := k; args := rs
      | none =>
        IO.eprintln s!"piet: --scale expects a number, got '{n}'"
        return 3
    | "--grid" :: rs =>
      grid := true; args := rs
    | a :: rs => rest := a :: rest; args := rs
  match svg? with
  | some out => renderSvg cfg scale grid out rest.reverse
  | none => (runner cfg).main rest.reverse
