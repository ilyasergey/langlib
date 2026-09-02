import Langlib.Languages.Velato.Sheet

/-!
# Velato: three ways out of a `Scene`

`Langlib/Languages/Velato/Sheet.lean` engraves a program into a `Scene`: a
resolution-independent list of stroked paths, filled note heads and labels.
This module turns a `Scene` into something you can look at, in the three
formats the project needs and with no dependency outside Lean:

* **PDF** (`toPdf`), for printing and for handing to a musician. Vector, one
  page, text set in Helvetica — a base-14 font every reader has, so the file
  embeds no font programme and stays a few kilobytes.
* **SVG** (`toSvg`), for the web and for the runner's `--svg` flag.
* **A raster `Image`** (`toImage`), which the runner writes as a PPM and
  `scripts/ppm-to-png.py` turns into the PNGs on the documentation pages.
  That converter is the one Brainloller already uses, so adding a graphical
  language added no new tooling.

The three consume the same `Scene`, so a picture in the documentation cannot
drift from the PDF a composer prints or the SVG the runner writes.

## Why a rasteriser at all

Because the alternative is a dependency. Turning SVG into PNG needs
`rsvg-convert`, Inkscape or a Python cairo binding, none of which the rest of
this repository needs, and `CLAUDE.md` asks that a committed image be
reproducible by a script that works on a bare checkout. So the raster
backend draws the same paths itself: it flattens each Bézier to a polyline
and stamps a filled disc along it, which gives round caps and joins for
free, and it fills note heads by testing points against the rotated ellipse.
Labels use the 5×7 bitmap font at the end of this file, written as ASCII art
so that a change to a glyph is legible in a diff.
-/

namespace Langlib.Velato.Sheet

open Langlib.Common

/-! ## A 5×7 bitmap font

One entry per character: seven rows of five columns, `#` for ink, `.` for
paper, rows separated by `/`. Lowercase is drawn with the uppercase glyphs,
and anything with no glyph at all is drawn as a blank, so a label can never
crash a render. -/

def fontGlyphs : List (Char × String) :=
  [ ('A', ".###./#...#/#...#/#####/#...#/#...#/#...#")
  , ('B', "####./#...#/#...#/####./#...#/#...#/####.")
  , ('C', ".###./#...#/#..../#..../#..../#...#/.###.")
  , ('D', "####./#...#/#...#/#...#/#...#/#...#/####.")
  , ('E', "#####/#..../#..../####./#..../#..../#####")
  , ('F', "#####/#..../#..../####./#..../#..../#....")
  , ('G', ".###./#...#/#..../#.##./#...#/#...#/.###.")
  , ('H', "#...#/#...#/#...#/#####/#...#/#...#/#...#")
  , ('I', ".###./..#../..#../..#../..#../..#../.###.")
  , ('J', "....#/....#/....#/....#/#...#/#...#/.###.")
  , ('K', "#...#/#..#./#.#../##.../#.#../#..#./#...#")
  , ('L', "#..../#..../#..../#..../#..../#..../#####")
  , ('M', "#...#/##.##/#.#.#/#...#/#...#/#...#/#...#")
  , ('N', "#...#/##..#/#.#.#/#..##/#...#/#...#/#...#")
  , ('O', ".###./#...#/#...#/#...#/#...#/#...#/.###.")
  , ('P', "####./#...#/#...#/####./#..../#..../#....")
  , ('Q', ".###./#...#/#...#/#...#/#.#.#/#..#./.##.#")
  , ('R', "####./#...#/#...#/####./#.#../#..#./#...#")
  , ('S', ".###./#...#/#..../.###./....#/#...#/.###.")
  , ('T', "#####/..#../..#../..#../..#../..#../..#..")
  , ('U', "#...#/#...#/#...#/#...#/#...#/#...#/.###.")
  , ('V', "#...#/#...#/#...#/#...#/#...#/.#.#./..#..")
  , ('W', "#...#/#...#/#...#/#...#/#.#.#/##.##/#...#")
  , ('X', "#...#/#...#/.#.#./..#../.#.#./#...#/#...#")
  , ('Y', "#...#/#...#/.#.#./..#../..#../..#../..#..")
  , ('Z', "#####/....#/...#./..#../.#.../#..../#####")
  , ('0', ".###./#...#/#..##/#.#.#/##..#/#...#/.###.")
  , ('1', "..#../.##../..#../..#../..#../..#../.###.")
  , ('2', ".###./#...#/....#/...#./..#../.#.../#####")
  , ('3', "#####/...#./..#../...#./....#/#...#/.###.")
  , ('4', "...#./..##./.#.#./#..#./#####/...#./...#.")
  , ('5', "#####/#..../####./....#/....#/#...#/.###.")
  , ('6', "..##./.#.../#..../####./#...#/#...#/.###.")
  , ('7', "#####/....#/...#./..#../.#.../.#.../.#...")
  , ('8', ".###./#...#/#...#/.###./#...#/#...#/.###.")
  , ('9', ".###./#...#/#...#/.####/....#/...#./.##..")
  , (' ', "...../...../...../...../...../...../.....")
  , ('#', ".#.#./.#.#./#####/.#.#./#####/.#.#./.#.#.")
  , ('-', "...../...../...../#####/...../...../.....")
  , ('.', "...../...../...../...../...../.##../.##..")
  , (',', "...../...../...../...../.##../.##../.#...")
  , (':', "...../.##../.##../...../.##../.##../.....")
  , (';', "...../.##../.##../...../.##../.##../.#...")
  , ('(', "...#./..#../.#.../.#.../.#.../..#../...#.")
  , (')', ".#.../..#../...#./...#./...#./..#../.#...")
  , ('\'', "..#../..#../..#../...../...../...../.....")
  , ('"', ".#.#./.#.#./...../...../...../...../.....")
  , ('/', "....#/...#./...#./..#../.#.../.#.../#....")
  , ('+', "...../..#../..#../#####/..#../..#../.....")
  , ('=', "...../...../#####/...../#####/...../.....")
  , ('<', "...#./..#../.#.../#..../.#.../..#../...#.")
  , ('>', ".#.../..#../...#./....#/...#./..#../.#...")
  , ('!', "..#../..#../..#../..#../..#../...../..#..")
  , ('?', ".###./#...#/....#/...#./..#../...../..#..")
  , ('*', "...../#.#.#/.###./#####/.###./#.#.#/.....")
  , ('%', "##..#/##..#/...#./..#../.#.../#..##/#..##")
  , ('&', ".##../#..#./#.#../.#.../#.#.#/#..#./.##.#")
  ]

/-- The rows of a character's glyph, uppercasing letters and falling back to
a blank, so a label can never crash a render. -/
def glyphOf (c : Char) : Array String :=
  match fontGlyphs.lookup c.toUpper with
  | some rows => (rows.splitOn "/").toArray
  | none => Array.replicate 7 "....."

/-- A `Float` truncated to a pixel index. Coordinates are always inside the
canvas by construction, and `Canvas.set` drops anything that is not. -/
def f2i (x : Float) : Int :=
  if x < 0 then -((-x).toUInt64.toNat : Int) else ((x.toUInt64.toNat : Nat) : Int)

/-- The same, as a count. -/
def f2n (x : Float) : Nat := if x < 0 then 0 else x.toUInt64.toNat

/-! ## The raster backend -/

/-- A mutable-ish drawing surface. `px` is row-major, as `Image` wants. -/
structure Canvas where
  width : Nat
  height : Nat
  px : Array Rgb

namespace Canvas

def blank (w h : Nat) (bg : Rgb := ⟨255, 255, 255⟩) : Canvas :=
  { width := w, height := h, px := Array.replicate (w * h) bg }

/-- Set one pixel, ignoring anything outside the surface. -/
def set (cv : Canvas) (x y : Int) (c : Rgb) : Canvas :=
  if 0 ≤ x && x < cv.width && 0 ≤ y && y < cv.height then
    { cv with px := cv.px.set! (y.toNat * cv.width + x.toNat) c }
  else cv

/-- Stamp a filled disc of radius `r` at `(cx, cy)`. This is the brush the
stroker drags along a polyline, which is what gives round caps and joins. -/
def disc (cv : Canvas) (cx cy r : Float) (c : Rgb) : Canvas := Id.run do
  let mut cv := cv
  let r := if r < 0.5 then 0.5 else r
  let x0 := (cx - r - 1.0).floor
  let x1 := (cx + r + 1.0).ceil
  let y0 := (cy - r - 1.0).floor
  let y1 := (cy + r + 1.0).ceil
  let mut y := y0
  while y ≤ y1 do
    let mut x := x0
    while x ≤ x1 do
      let dx := x + 0.5 - cx
      let dy := y + 0.5 - cy
      if dx * dx + dy * dy ≤ r * r then
        cv := cv.set (f2i x) (f2i y) c
      x := x + 1.0
    y := y + 1.0
  return cv

/-- Draw a polyline of the given width by stamping discs along it, closely
enough that the discs overlap. -/
def polyline (cv : Canvas) (pts : List Vec) (w : Float) (c : Rgb) : Canvas := Id.run do
  let mut cv := cv
  let r := w / 2.0
  let mut prev : Option Vec := none
  for p in pts do
    match prev with
    | none => cv := cv.disc p.1 p.2 r c
    | some q =>
      let dx := p.1 - q.1
      let dy := p.2 - q.2
      let len := (dx * dx + dy * dy).sqrt
      let steps := (len * 2.0).ceil
      let n := if steps < 1.0 then 1 else f2n steps
      for i in [0:n + 1] do
        let t := Float.ofNat i / Float.ofNat n
        cv := cv.disc (q.1 + dx * t) (q.2 + dy * t) r c
    prev := some p
  return cv

/-- Fill a rotated ellipse: the note head. -/
def ellipse (cv : Canvas) (cx cy rx ry angle : Float) (c : Rgb) : Canvas := Id.run do
  let mut cv := cv
  let ca := angle.cos
  let sa := angle.sin
  let rad := (if rx > ry then rx else ry) + 1.0
  let mut y := (cy - rad).floor
  while y ≤ (cy + rad).ceil do
    let mut x := (cx - rad).floor
    while x ≤ (cx + rad).ceil do
      let dx := x + 0.5 - cx
      let dy := y + 0.5 - cy
      -- rotate the sample point back into the ellipse's own frame
      let u := dx * ca + dy * sa
      let v := -dx * sa + dy * ca
      if (u * u) / (rx * rx) + (v * v) / (ry * ry) ≤ 1.0 then
        cv := cv.set (f2i x) (f2i y) c
      x := x + 1.0
    y := y + 1.0
  return cv

/-- Draw a label with the bitmap font, scaled so its cap height is `size`
pixels. `anchor` is `0` left, `1` centred, `2` right. -/
def label (cv : Canvas) (x y : Float) (s : String) (size : Float) (anchor : Nat)
    (c : Rgb) : Canvas := Id.run do
  -- Round *down*: the engraver budgets one scene unit per font pixel when
  -- it spaces the notes, and rounding up would draw labels wider than the
  -- gap it left for them, which is how "end while" ends up touching its
  -- neighbour.
  let scale := size / Float.ofNat glyphH
  let scale := if scale < 1.0 then 1.0 else scale.floor
  let w := Float.ofNat (labelWidth s) * scale
  let x0 := match anchor with
    | 0 => x
    | 1 => x - w / 2.0
    | _ => x - w
  let y0 := y - Float.ofNat glyphH * scale
  let mut cv := cv
  for (ch, i) in s.toList.zipIdx do
    let g := glyphOf ch
    let gx := x0 + Float.ofNat (i * (glyphW + glyphGap)) * scale
    for row in [0:glyphH] do
      let line := g[row]!.toList
      for col in [0:glyphW] do
        if line[col]? == some '#' then
          -- one font pixel becomes a scale x scale block
          let px := gx + Float.ofNat col * scale
          let py := y0 + Float.ofNat row * scale
          let mut dy := 0.0
          while dy < scale do
            let mut dx := 0.0
            while dx < scale do
              cv := cv.set (f2i (px + dx)) (f2i (py + dy)) c
              dx := dx + 1.0
            dy := dy + 1.0
  return cv

def toImage (cv : Canvas) : Image :=
  { width := cv.width, height := cv.height, pixels := cv.px }

end Canvas

/-- Rasterise a scene. `scale` multiplies every coordinate, so `2` gives a
picture at twice the engraved size with no loss of sharpness. -/
def Scene.toImage (sc : Scene) (scale : Nat := 2) : Image := Id.run do
  let k := Float.ofNat scale
  let ink : Rgb := ⟨17, 17, 17⟩
  let mut cv := Canvas.blank (sc.width * scale) (sc.height * scale)
  let sc' : Vec → Vec := fun v => (v.1 * k, v.2 * k)
  for sh in sc.shapes do
    match sh with
    | .stroke path w =>
      for sp in path do
        cv := cv.polyline ((sp.flatten).map sc') (w * k) ink
    | .fill path =>
      for sp in path do
        cv := cv.polyline ((sp.flatten).map sc') (1.0 * k) ink
    | .head c rx ry angle =>
      cv := cv.ellipse (c.1 * k) (c.2 * k) (rx * k) (ry * k) angle ink
    | .text at_ s size anchor =>
      cv := cv.label (at_.1 * k) (at_.2 * k) s (size * k) anchor ink
  return cv.toImage

/-! ## The SVG backend -/

private def f2 (x : Float) : String :=
  let r := (x * 100.0).round / 100.0
  toString r

private def pathData (sp : SubPath) : String := Id.run do
  let mut d := s!"M {f2 sp.start.1} {f2 sp.start.2}"
  for s in sp.segs do
    d := d ++ s!" C {f2 s.c1.1} {f2 s.c1.2} {f2 s.c2.1} {f2 s.c2.2} {f2 s.to.1} {f2 s.to.2}"
  if sp.closed then d := d ++ " Z"
  return d

/-- Render a scene as SVG. -/
def Scene.toSvg (sc : Scene) : String := Id.run do
  let mut out :=
    s!"<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"{sc.width}\" height=\"{sc.height}\" \
      viewBox=\"0 0 {sc.width} {sc.height}\">\n\
      <rect width=\"{sc.width}\" height=\"{sc.height}\" fill=\"#ffffff\"/>\n\
      <g stroke=\"#111111\" fill=\"none\" stroke-linecap=\"round\" stroke-linejoin=\"round\">\n"
  for sh in sc.shapes do
    match sh with
    | .stroke path w =>
      for sp in path do
        out := out ++ s!"<path d=\"{pathData sp}\" stroke-width=\"{f2 w}\"/>\n"
    | .fill path =>
      for sp in path do
        out := out ++ s!"<path d=\"{pathData sp}\" fill=\"#111111\" stroke=\"none\"/>\n"
    | .head c rx ry angle =>
      let deg := angle * 180.0 / 3.14159265358979
      out := out ++
        s!"<ellipse cx=\"{f2 c.1}\" cy=\"{f2 c.2}\" rx=\"{f2 rx}\" ry=\"{f2 ry}\" \
          fill=\"#111111\" stroke=\"none\" \
          transform=\"rotate({f2 deg} {f2 c.1} {f2 c.2})\"/>\n"
    | .text at_ s size anchor =>
      let a := match anchor with
        | 0 => "start" | 1 => "middle" | _ => "end"
      let esc := s.replace "&" "&amp;" |>.replace "<" "&lt;" |>.replace ">" "&gt;"
      out := out ++
        s!"<text x=\"{f2 at_.1}\" y=\"{f2 at_.2}\" font-size=\"{f2 size}\" \
          font-family=\"Helvetica, Arial, sans-serif\" text-anchor=\"{a}\" \
          fill=\"#111111\" stroke=\"none\">{esc}</text>\n"
  return out ++ "</g>\n</svg>\n"

/-! ## The PDF backend

A PDF is a handful of objects, a cross-reference table listing where each
one starts, and a trailer pointing at the table. This writes the smallest
file that holds one page: a catalogue, a page tree, the page, the content
stream, and the name of a standard font.

The one thing to keep in mind while reading the content stream is that
PDF's `y` axis points *up* and the `Scene`'s points down, so every
coordinate is flipped through the page height. -/

private def pdfEsc (s : String) : String :=
  s.foldl (fun acc c =>
    if c == '(' || c == ')' || c == '\\' then acc ++ "\\" ++ String.singleton c
    else if c.toNat < 32 || c.toNat > 126 then acc
    else acc.push c) ""

/-- The four cubic Béziers that approximate an ellipse, rotated. `0.5523`
is the usual circular constant: the control points of a quarter arc sit that
fraction of the radius along the tangent. -/
private def ellipseSegs (cx cy rx ry angle : Float) : List Vec × List (Vec × Vec × Vec) :=
  let k := 0.5522847498
  let ca := angle.cos
  let sa := angle.sin
  -- map a point of the unrotated ellipse's frame into the page
  let m : Float → Float → Vec := fun u v => (cx + u * ca - v * sa, cy + u * sa + v * ca)
  let p0 := m rx 0.0
  let arcs :=
    [ (m rx (k * ry), m (k * rx) ry, m 0.0 ry)
    , (m (-(k * rx)) ry, m (-rx) (k * ry), m (-rx) 0.0)
    , (m (-rx) (-(k * ry)), m (-(k * rx)) (-ry), m 0.0 (-ry))
    , (m (k * rx) (-ry), m rx (-(k * ry)), m rx 0.0) ]
  ([p0], arcs)

/-- Render a scene as a one-page PDF. -/
def Scene.toPdf (sc : Scene) (title : String := "Velato") : ByteArray := Id.run do
  let h := Float.ofNat sc.height
  let fy : Float → Float := fun y => h - y
  -- the content stream
  let mut cs := "1 J 1 j 0.067 0.067 0.067 RG 0.067 0.067 0.067 rg\n"
  for sh in sc.shapes do
    match sh with
    | .stroke path w =>
      cs := cs ++ s!"{f2 w} w\n"
      for sp in path do
        cs := cs ++ s!"{f2 sp.start.1} {f2 (fy sp.start.2)} m\n"
        for s in sp.segs do
          cs := cs ++ s!"{f2 s.c1.1} {f2 (fy s.c1.2)} {f2 s.c2.1} {f2 (fy s.c2.2)} \
            {f2 s.to.1} {f2 (fy s.to.2)} c\n"
        cs := cs ++ (if sp.closed then "h S\n" else "S\n")
    | .fill path =>
      for sp in path do
        cs := cs ++ s!"{f2 sp.start.1} {f2 (fy sp.start.2)} m\n"
        for s in sp.segs do
          cs := cs ++ s!"{f2 s.c1.1} {f2 (fy s.c1.2)} {f2 s.c2.1} {f2 (fy s.c2.2)} \
            {f2 s.to.1} {f2 (fy s.to.2)} c\n"
        cs := cs ++ "f\n"
    | .head c rx ry angle =>
      let (starts, arcs) := ellipseSegs c.1 c.2 rx ry angle
      match starts with
      | [p0] =>
        cs := cs ++ s!"{f2 p0.1} {f2 (fy p0.2)} m\n"
        for (a, b, e) in arcs do
          cs := cs ++ s!"{f2 a.1} {f2 (fy a.2)} {f2 b.1} {f2 (fy b.2)} \
            {f2 e.1} {f2 (fy e.2)} c\n"
        cs := cs ++ "f\n"
      | _ => pure ()
    | .text at_ s size anchor =>
      -- Helvetica's average advance is about 0.5 em, which is close enough
      -- for the short labels a sheet carries
      let w := Float.ofNat s.length * size * 0.5
      let x := match anchor with
        | 0 => at_.1
        | 1 => at_.1 - w / 2.0
        | _ => at_.1 - w
      cs := cs ++ s!"BT /F1 {f2 size} Tf {f2 x} {f2 (fy at_.2)} Td ({pdfEsc s}) Tj ET\n"
  let csBytes := cs.toUTF8
  let objs : List String :=
    [ "<< /Type /Catalog /Pages 2 0 R >>"
    , "<< /Type /Pages /Kids [3 0 R] /Count 1 >>"
    , s!"<< /Type /Page /Parent 2 0 R /MediaBox [0 0 {sc.width} {sc.height}] \
        /Contents 4 0 R /Resources << /Font << /F1 5 0 R >> >> >>"
    , s!"<< /Length {csBytes.size} >>"
    , "<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica /Encoding /WinAnsiEncoding >>"
    , s!"<< /Title ({pdfEsc title}) /Producer (langlib velato) >>" ]
  let mut out := "%PDF-1.4\n".toUTF8
  let mut offsets : Array Nat := #[]
  for (body, i) in objs.zipIdx do
    offsets := offsets.push out.size
    out := out ++ s!"{i + 1} 0 obj\n{body}\n".toUTF8
    if i == 3 then
      out := out ++ "stream\n".toUTF8 ++ csBytes ++ "\nendstream\n".toUTF8
    out := out ++ "endobj\n".toUTF8
  let xref := out.size
  let n := objs.length + 1
  out := out ++ s!"xref\n0 {n}\n0000000000 65535 f \n".toUTF8
  for o in offsets do
    -- each entry is exactly twenty bytes, which the format insists on
    let s := toString o
    let padded := "".pushn '0' (10 - s.length) ++ s
    out := out ++ s!"{padded} 00000 n \n".toUTF8
  out := out ++ s!"trailer\n<< /Size {n} /Root 1 0 R /Info 6 0 R >>\nstartxref\n{xref}\n%%EOF\n".toUTF8
  return out

end Langlib.Velato.Sheet
