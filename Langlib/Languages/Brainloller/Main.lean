import Langlib.Common.Runner
import Langlib.Languages.Brainloller.Semantics

/-!
# Brainloller: standalone runner and encoder

```
lake exe brainloller [--fuel N] [--eof unchanged|zero|minus1] file.ppm
lake exe brainloller --encode out.ppm [--width N] file.b
```

Programs must be ASCII PPM (P3); convert anything else with
`magick prog.png -compress none prog.ppm`. The `--encode` mode goes the
other way: it reads brainfuck source and writes a Brainloller image
(single row by default; `--width N` wraps it into a serpentine).
-/

namespace Langlib.Brainloller

open Langlib.Common

def runner (cfg : Langlib.Brainfuck.Config) : Runner where
  name := "brainloller"
  ext := "ppm"
  run := run cfg
  usageExtra :=
    [ "  --eof MODE what ',' stores at end of input: unchanged (default),"
    , "             zero, minus1 (the brainfuck core's conventions)"
    , "  --encode OUT.ppm [--width N] FILE.b"
    , "             encode brainfuck source as a Brainloller image instead"
    , "  images must be ASCII PPM (P3); convert with e.g."
    , "    magick prog.png -compress none prog.ppm" ]

/-- `--encode` mode: brainfuck source in, P3 image out. -/
def encodeMain (outFile : String) (args : List String) : IO UInt32 := do
  let mut width := 0
  let mut file? : Option String := none
  let mut args := args
  repeat
    match args with
    | [] => break
    | "--width" :: n :: rs =>
      match n.toNat? with
      | some k => width := k; args := rs
      | none =>
        IO.eprintln s!"brainloller: --width expects a number, got '{n}'"
        return 3
    | a :: rs =>
      if a.startsWith "--" then
        IO.eprintln s!"brainloller: unknown flag '{a}' in --encode mode"
        return 3
      else if file?.isSome then
        IO.eprintln "brainloller: more than one input file"
        return 3
      else
        file? := some a; args := rs
  let some file := file? |
    IO.eprintln "usage: lake exe brainloller --encode OUT.ppm [--width N] FILE.b"
    return 3
  let src ← try
      IO.FS.readFile file
    catch e =>
      IO.eprintln s!"brainloller: cannot read '{file}': {e}"
      return 3
  let img := encode src width
  IO.FS.writeFile outFile img.toPpm3
  IO.eprintln s!"brainloller: wrote {img.width}x{img.height} image to {outFile}"
  return 0

end Langlib.Brainloller

open Langlib.Brainloller in
def main (args : List String) : IO UInt32 := do
  -- Pre-process --encode and --eof, then delegate to the shared runner.
  let mut eof : Langlib.Brainfuck.EofMode := .unchanged
  let mut rest : List String := []
  let mut args := args
  repeat
    match args with
    | [] => break
    | "--encode" :: out :: rs => return ← encodeMain out rs
    | "--encode" :: [] =>
      IO.eprintln "brainloller: --encode expects an output file"
      return 3
    | "--eof" :: m :: rs =>
      match m with
      | "unchanged" => eof := .unchanged; args := rs
      | "zero" => eof := .zero; args := rs
      | "minus1" => eof := .minusOne; args := rs
      | _ =>
        IO.eprintln s!"brainloller: unknown --eof mode '{m}' (unchanged|zero|minus1)"
        return 3
    | a :: rs => rest := a :: rest; args := rs
  (runner { eof }).main rest.reverse
