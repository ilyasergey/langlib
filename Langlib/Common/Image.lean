/-!
# Shared RGB image model and PPM reader

The graphical languages (Piet, Brainloller) take images as programs. This
module gives them a minimal shared image type and a reader for the netpbm
PPM formats `P3` (ASCII) and `P6` (binary), the lingua franca of image
tooling: anything can be converted to PPM (`magick prog.png prog.ppm`).

Only maxval 255 is supported; `#` comments are handled per the PPM
specification (http://netpbm.sourceforge.net/doc/ppm.html). A `P3` writer
(`Image.toPpm3`) is provided so tools and encoders can emit images that
diff nicely in git.
-/

namespace Langlib.Common

/-- One RGB pixel, 8 bits per channel. -/
structure Rgb where
  r : UInt8
  g : UInt8
  b : UInt8
deriving Repr, BEq, Inhabited

/-- A raster image: `pixels` is row-major, of size `width * height`. -/
structure Image where
  width : Nat
  height : Nat
  pixels : Array Rgb
deriving Repr, Inhabited

namespace Image

/-- Pixel at column `x`, row `y`; `none` outside the image. -/
def get? (img : Image) (x y : Nat) : Option Rgb :=
  if x < img.width && y < img.height then
    img.pixels[y * img.width + x]?
  else
    none

/-- PPM whitespace: space, TAB, CR, LF, VT, FF. -/
private def isSpace (b : UInt8) : Bool :=
  b == 32 || b == 9 || b == 10 || b == 13 || b == 11 || b == 12

/-- Skip whitespace and `#` comments (which run to end of line). The fuel
is the number of bytes left, so recursion is structural. -/
private def skipWsAux (data : ByteArray) : Nat → Nat → Bool → Nat
  | 0, pos, _ => pos
  | fuel + 1, pos, inComment =>
    if h : pos < data.size then
      let b := data[pos]
      if inComment then skipWsAux data fuel (pos + 1) (b != 10)
      else if isSpace b then skipWsAux data fuel (pos + 1) false
      else if b == 35 then skipWsAux data fuel (pos + 1) true -- '#'
      else pos
    else pos

private def skipWs (data : ByteArray) (pos : Nat) : Nat :=
  skipWsAux data (data.size + 1) pos false

private def digitsAux (data : ByteArray) : Nat → Nat → Nat → Nat × Nat
  | 0, pos, acc => (pos, acc)
  | fuel + 1, pos, acc =>
    if h : pos < data.size then
      let b := data[pos]
      if 48 ≤ b && b ≤ 57 then
        digitsAux data fuel (pos + 1) (acc * 10 + (b.toNat - 48))
      else (pos, acc)
    else (pos, acc)

/-- Read an unsigned decimal number at `pos`; `none` if no digit there. -/
private def readNat? (data : ByteArray) (pos : Nat) : Option (Nat × Nat) :=
  if h : pos < data.size then
    let b := data[pos]
    if 48 ≤ b && b ≤ 57 then some (digitsAux data (data.size + 1) pos 0).swap
    else none
  else none

/-- Parse a PPM image (`P3` ASCII or `P6` binary, maxval 255) from raw
bytes. Error messages point at what was expected. -/
def parsePpm (data : ByteArray) : Except String Image := do
  unless data.size ≥ 2 && data[0]! == 80 do -- 'P'
    throw "not a PPM image (expected magic number P3 or P6)"
  let isP3 := data[1]! == 51 -- '3'
  let isP6 := data[1]! == 54 -- '6'
  unless isP3 || isP6 do
    throw "not a PPM image (expected magic number P3 or P6)"
  let mut pos := skipWs data 2
  let some (w, p) := readNat? data pos
    | throw "PPM header: expected width"
  pos := skipWs data p
  let some (h, p) := readNat? data pos
    | throw "PPM header: expected height"
  pos := skipWs data p
  let some (maxval, p) := readNat? data pos
    | throw "PPM header: expected maxval"
  pos := p
  unless maxval == 255 do
    throw s!"PPM maxval {maxval} is not supported (only 255)"
  unless w > 0 && h > 0 do
    throw "PPM image has zero width or height"
  let count := w * h
  let mut pixels : Array Rgb := Array.mkEmpty count
  if isP3 then
    for _ in [0:count] do
      let mut sample : Array Nat := #[]
      for _ in [0:3] do
        pos := skipWs data pos
        let some (v, p) := readNat? data pos
          | throw s!"P3 pixel data: expected a sample value \
              (pixel {pixels.size + 1} of {count})"
        unless v ≤ 255 do
          throw s!"P3 pixel data: sample {v} exceeds maxval 255"
        sample := sample.push v
        pos := p
      pixels := pixels.push
        ⟨sample[0]!.toUInt8, sample[1]!.toUInt8, sample[2]!.toUInt8⟩
  else
    -- P6: a single whitespace byte after the maxval, then raw bytes.
    unless pos < data.size && isSpace data[pos]! do
      throw "P6: expected a whitespace byte after the maxval"
    pos := pos + 1
    unless pos + 3 * count ≤ data.size do
      throw s!"P6: truncated pixel data \
        (need {3 * count} bytes, have {data.size - pos})"
    for i in [0:count] do
      pixels := pixels.push
        ⟨data[pos + 3 * i]!, data[pos + 3 * i + 1]!, data[pos + 3 * i + 2]!⟩
  return { width := w, height := h, pixels }

/-- Render as ASCII PPM (`P3`), one image row per output line. Handy for
tests and for emitting example programs that diff well in git. -/
def toPpm3 (img : Image) : String := Id.run do
  let mut out := s!"P3\n{img.width} {img.height}\n255\n"
  for y in [0:img.height] do
    let mut line := ""
    for x in [0:img.width] do
      let px := (img.get? x y).getD default
      let sep := if x == 0 then "" else " "
      line := line ++ s!"{sep}{px.r.toNat} {px.g.toNat} {px.b.toNat}"
    out := out ++ line ++ "\n"
  return out

end Image

end Langlib.Common
