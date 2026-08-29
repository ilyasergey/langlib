import Langlib.Common.Image
import Langlib.Languages.Piet.Syntax

/-!
# Piet: image to codel grid

"Parsing" a Piet program means turning a bitmap into a codel grid. Two
policies are configurable:

* **Codel size** (`--codel-size N`): Piet programs are often published
  upscaled so the pixels are visible; a codel is then an N x N pixel
  square. We default to 1 and make no attempt at auto-detection (the
  detected size is not unique: any program is also a valid program at
  codel size 1). Each codel is sampled at its upper-left pixel, as npiet
  does; we do not check that codels are uniformly coloured.
* **Unknown colours**: only the 20 standard colours are meaningful. By
  default any other colour is a parse error (the loud option); with
  `unknownWhite := true` (npiet's behaviour under `-w`) unknown colours
  are read as white.
-/

namespace Langlib.Piet

open Langlib.Common

/-- Image-to-grid options; see the module docstring. -/
structure ParseConfig where
  codelSize : Nat := 1
  unknownWhite : Bool := false
deriving Repr, Inhabited

/-- Turn an image into a codel grid under the given options. -/
def gridOfImage (cfg : ParseConfig) (img : Image) : Except String Grid := do
  let cs := cfg.codelSize
  unless cs > 0 do
    throw "codel size must be at least 1"
  unless img.width % cs == 0 && img.height % cs == 0 do
    throw s!"image size {img.width}x{img.height} is not a multiple of \
      codel size {cs}"
  let w := img.width / cs
  let h := img.height / cs
  let mut codels : Array Codel := Array.mkEmpty (w * h)
  for y in [0:h] do
    for x in [0:w] do
      let px := (img.get? (x * cs) (y * cs)).getD default
      match colorOfRgb px with
      | some c => codels := codels.push c
      | none =>
        if cfg.unknownWhite then
          codels := codels.push .white
        else
          throw s!"unknown colour ({px.r.toNat},{px.g.toNat},{px.b.toNat}) \
            at codel ({x},{y}); only the 20 Piet colours are allowed \
            (rerun with --unknown-white to read others as white)"
  return { width := w, height := h, codels }

/-- Parse a PPM image into a codel grid. -/
def parseGrid (cfg : ParseConfig) (data : ByteArray) : Except String Grid :=
  Image.parsePpm data >>= gridOfImage cfg

end Langlib.Piet
