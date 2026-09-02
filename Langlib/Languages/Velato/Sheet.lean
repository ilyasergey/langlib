import Langlib.Common.Image
import Langlib.Languages.Velato.Note

/-!
# Velato: engraving a program as sheet music

A Velato program is a piece of music, so the natural way to read one is off a
staff. This module engraves a note sequence: staff lines, clefs, note heads,
stems, accidentals, ledger lines, bar lines, and a row of labels underneath
saying what each note is doing.

## Everything except the pitches is editorial

Velato ignores duration, metre, key signature, dynamics and repeats: the
language sees pitch and order and nothing else. So the durations on these
sheets carry no information — every note is engraved as a quarter note, and
the bar lines every four notes are a reading aid, not a time signature. What
*is* information is the pitch of each note head, the accidental in front of
it, and its position in the sequence. A reader who wants to know what a
program does reads the note heads; a reader who wants to know how it sounds
needs the MIDI file, where the durations live.

## Two backends, one description

`Scene` is a list of drawing primitives — stroked and filled Bézier paths,
note-head ellipses, and text — and both backends consume it, so the PNG on
the documentation page and the SVG the runner emits cannot disagree about
what a program looks like. The raster backend draws text with a 5×7 bitmap
font defined at the bottom of this file as ASCII art, which is reviewable in
a diff in a way that packed hexadecimal is not; the SVG backend uses a
`<text>` element and the reader's own font.

Both are pure functions of a note list, so `scripts/render-docs-images.sh`
regenerates every picture in `docs/velato/img/` byte for byte, and
`--check` there fails if a committed image has gone stale.
-/

namespace Langlib.Velato.Sheet

open Langlib.Common

/-! ## Geometry -/

/-- A point. Coordinates are in output pixels, `y` growing downward. -/
abbrev Vec := Float × Float

/-- A cubic Bézier segment, given its endpoint and two control points; the
start point is the previous segment's end. -/
structure Seg where
  c1 : Vec
  c2 : Vec
  to : Vec

/-- A subpath: a starting point and a run of cubic segments. -/
structure SubPath where
  start : Vec
  segs : List Seg
  closed : Bool := false

/-- Sample a cubic Bézier at `t`. -/
private def bezier (p0 p1 p2 p3 : Vec) (t : Float) : Vec :=
  let u := 1.0 - t
  let a := u * u * u
  let b := 3.0 * u * u * t
  let c := 3.0 * u * t * t
  let d := t * t * t
  (a * p0.1 + b * p1.1 + c * p2.1 + d * p3.1,
   a * p0.2 + b * p1.2 + c * p2.2 + d * p3.2)

/-- Flatten a subpath to a polyline, `steps` samples per segment. -/
def SubPath.flatten (sp : SubPath) (steps : Nat := 24) : List Vec := Id.run do
  let mut pts : List Vec := [sp.start]
  let mut cur := sp.start
  for s in sp.segs do
    for i in [1:steps+1] do
      let t := Float.ofNat i / Float.ofNat steps
      pts := bezier cur s.c1 s.c2 s.to t :: pts
    cur := s.to
  if sp.closed then pts := sp.start :: pts
  return pts.reverse

/-! ## Scenes -/

/-- One thing to draw. -/
inductive Shape where
  /-- A stroked path of the given width. -/
  | stroke (path : List SubPath) (width : Float)
  /-- A filled path. -/
  | fill (path : List SubPath)
  /-- A note head: an ellipse with semi-axes `rx`, `ry`, rotated by `angle`
  radians. Kept as its own shape because both backends can draw an ellipse
  far better than they can draw four Béziers approximating one. -/
  | head (centre : Vec) (rx ry angle : Float)
  /-- A label. `anchor` is `0` for left, `1` for centred, `2` for right. -/
  | text (at_ : Vec) (s : String) (size : Float) (anchor : Nat)

/-- A drawing: a size and the shapes in it, back to front. -/
structure Scene where
  width : Nat
  height : Nat
  shapes : List Shape

/-! ## Clefs

A G clef and an F clef, as Bézier outlines in a unit box: `x` and `y` both
run over roughly `0 … 1`, and the engraver scales and places them. They are
stroked rather than filled, so the strokes are what give them weight; that
is a simplification of real engraving, where a clef is a filled outline with
varying thickness, and it is what keeps the data here small enough to
read. -/

private def P (x y : Float) : Vec := (x, y)

/-- The G clef, drawn as one continuous stroke: the hook below the staff,
the ascending stem, the great loop to the left, and the spiral that closes
on the G line. Its unit box is `1.0` wide and `2.6` tall, with the G line
(the centre of the spiral) at `y = 1.72`. -/
def gClef : List SubPath :=
  [ { start := P 0.36 2.58
    , segs :=
      [ { c1 := P 0.02 2.55, c2 := P 0.00 2.10, to := P 0.30 2.02 }
      , { c1 := P 0.62 1.94, c2 := P 0.80 2.18, to := P 0.74 2.42 }
      , { c1 := P 0.70 2.58, c2 := P 0.62 1.30, to := P 0.56 0.72 }
      , { c1 := P 0.52 0.28, c2 := P 0.62 0.00, to := P 0.76 0.02 }
      , { c1 := P 0.94 0.05, c2 := P 1.00 0.52, to := P 0.86 0.86 }
      , { c1 := P 0.74 1.16, c2 := P 0.34 1.42, to := P 0.18 1.62 }
      , { c1 := P 0.00 1.86, c2 := P 0.06 2.24, to := P 0.38 2.24 }
      , { c1 := P 0.72 2.24, c2 := P 0.86 1.92, to := P 0.62 1.74 }
      , { c1 := P 0.46 1.62, c2 := P 0.24 1.70, to := P 0.26 1.86 } ] } ]

/-- Where the G clef's spiral centre sits in its own unit box: this is the
point the engraver puts on the G line. -/
def gClefLineY : Float := 1.80

/-- The F clef: the comma-shaped body, the ascending curve, and the two dots
that straddle the F line. Its unit box is `1.0` wide and `1.35` tall, with
the F line at `y = 0.18`. -/
def fClef : List SubPath :=
  [ { start := P 0.02 0.06
    , segs :=
      [ { c1 := P 0.30 (-0.06), c2 := P 0.66 0.02, to := P 0.66 0.34 }
      , { c1 := P 0.66 0.78, c2 := P 0.24 1.10, to := P 0.00 1.24 } ] } ]

/-- The two dots of the F clef, as offsets in its unit box. -/
def fClefDots : List Vec := [P 0.84 0.02, P 0.84 0.34]

/-- A sharp sign in a unit box `0.55` wide and `1.0` tall: two uprights and
two thick slanted crossbars. -/
def sharpSign : List SubPath :=
  [ { start := P 0.16 0.06, segs := [{ c1 := P 0.16 0.36, c2 := P 0.16 0.66, to := P 0.16 0.94 }] }
  , { start := P 0.40 0.02, segs := [{ c1 := P 0.40 0.32, c2 := P 0.40 0.62, to := P 0.40 0.90 }] }
  , { start := P 0.02 0.42, segs := [{ c1 := P 0.20 0.38, c2 := P 0.38 0.34, to := P 0.54 0.30 }] }
  , { start := P 0.02 0.70, segs := [{ c1 := P 0.20 0.66, c2 := P 0.38 0.62, to := P 0.54 0.58 }] } ]

/-! ## Layout

The staff is the usual five lines a semitone-blind distance apart, and a
note's vertical position is its *diatonic* position: C, D, E, F, G, A, B are
seven steps to the octave and an accidental does not move the head. So the
engraver works in diatonic numbers — seven per octave, counted from C-1 —
and converts a pitch to one by looking up which letter its pitch class
spells. -/

/-- Which letter a pitch class spells, and whether it needs a sharp. Every
black key is spelled as the sharp of the white key below it, because MIDI
has no spelling and something has to be chosen; velato.net's own examples
mix sharps and flats freely, and the language cannot tell. -/
def spell (pc : Nat) : Nat × Bool :=
  match pc % 12 with
  | 0 => (0, false) | 1 => (0, true)
  | 2 => (1, false) | 3 => (1, true)
  | 4 => (2, false)
  | 5 => (3, false) | 6 => (3, true)
  | 7 => (4, false) | 8 => (4, true)
  | 9 => (5, false) | 10 => (5, true)
  | _ => (6, false)

/-- The diatonic position of a pitch: seven per octave, counting from C-1
(MIDI 0) as zero. Middle C (MIDI 60) is 35, and E4, the bottom line of the
treble staff, is 37. -/
def diatonic (p : Pitch) : Nat := 7 * (p / 12) + (spell (p % 12)).1

/-- Whether a pitch is engraved with a sharp. -/
def needsSharp (p : Pitch) : Bool := (spell (p % 12)).2

/-- Glyph metrics of the 5x7 label font in `Render.lean`: five columns and
one column of gap. The engraver needs them to know how much room a label
takes, so they are stated here and used there. -/
def glyphW : Nat := 5
def glyphGap : Nat := 1
def glyphH : Nat := 7

/-- The width of a label, in the units the scene is laid out in. -/
def labelWidth (s : String) : Nat :=
  if s.isEmpty then 0 else s.length * (glyphW + glyphGap) - glyphGap

/-- Engraving parameters. `space` is the distance between two staff lines,
which every other measurement is stated in. -/
structure Style where
  /-- Distance between adjacent staff lines, in pixels. -/
  space : Float := 11.0
  /-- Horizontal distance between note heads. -/
  advance : Float := 34.0
  /-- Notes per bar. Purely a reading aid: Velato has no metre. -/
  perBar : Nat := 4
  /-- Notes per system before wrapping to the next line. -/
  perSystem : Nat := 16
  /-- Draw the note name under every note. -/
  noteNames : Bool := true
deriving Inhabited

/-- One engraved note: its pitch and an optional label to print beneath it,
which is how a sheet shows what the program is doing. -/
structure Item where
  pitch : Pitch
  /-- A short label under the note, e.g. `"print"` or `"7"`. -/
  label : String := ""
deriving Inhabited

/-- Whether a run of notes is engraved on the treble or the bass staff.
Chosen by where the notes actually sit: a program that lives below middle C
reads far better on an F clef than under six ledger lines. -/
def useBass (items : List Item) : Bool :=
  let ds := items.map fun i => diatonic i.pitch
  match ds with
  | [] => false
  | _ =>
    let total := ds.foldl (· + ·) 0
    -- 35 is middle C; below it on average, use the bass staff
    total * 1 < 35 * ds.length

/-! ## Engraving -/

private def staffTop (sys : Float) (st : Style) : Float :=
  40.0 + sys * (st.space * 13.0)

/-- Turn a list of items into a scene. -/
def engrave (items : List Item) (st : Style := {}) (title : String := "") : Scene := Id.run do
  let bass := useBass items
  -- the diatonic number of the staff's bottom line: E4 for treble, G2 for bass
  let refLine : Float := if bass then 18.0 else 37.0
  let n := items.length
  let systems := (n + st.perSystem - 1) / st.perSystem
  let systems := if systems == 0 then 1 else systems
  let leftPad : Float := 66.0
  -- Widen the note spacing until the widest label fits between two heads.
  -- Otherwise a run of long roles ("end while", "end num") overprints, and
  -- the label row is the part of these sheets that teaches the language.
  let widest := items.foldl (fun w it =>
    max w (max (labelWidth it.pitch.name) (labelWidth it.label))) 0
  let advance := max st.advance (Float.ofNat widest + 7.0)
  -- A system is only as wide as the notes actually on it, so an eight-note
  -- program does not get sixteen notes' worth of empty staff.
  let perSys := if n < st.perSystem then max n 1 else st.perSystem
  let width := leftPad + Float.ofNat perSys * advance + 28.0
  -- the last system's staff, plus room for the two label rows under it
  let height := staffTop (Float.ofNat (systems - 1)) st + st.space * 9.0 + 14.0
  let mut shapes : List Shape := []

  if !title.isEmpty then
    shapes := .text (16.0, 26.0) title 11.0 0 :: shapes

  for sys in [0:systems] do
    let top := staffTop (Float.ofNat sys) st
    let bottom := top + 4.0 * st.space
    -- five staff lines
    let right := leftPad + Float.ofNat perSys * advance
    for k in [0:5] do
      let y := top + Float.ofNat k * st.space
      shapes := .stroke [{ start := (leftPad - 46.0, y)
                         , segs := [{ c1 := (leftPad, y), c2 := (right, y), to := (right, y) }] }] 1.3
                  :: shapes
    -- the clef
    if bass then
      let h := st.space * 3.2
      let x0 := leftPad - 40.0
      -- the F line is the second line from the top
      let fy := top + st.space
      let place : Vec → Vec := fun v => (x0 + v.1 * h * 0.78, fy + (v.2 - 0.18) * h)
      shapes := .stroke (fClef.map fun sp =>
          { start := place sp.start
            segs := sp.segs.map fun s => { c1 := place s.c1, c2 := place s.c2, to := place s.to }
            closed := sp.closed }) 2.6 :: shapes
      for d in fClefDots do
        let c := place d
        shapes := .head c 1.9 1.9 0.0 :: shapes
    else
      let h := st.space * 2.55
      let x0 := leftPad - 42.0
      -- the G line is the second line from the bottom
      let gy := bottom - st.space
      let place : Vec → Vec := fun v => (x0 + v.1 * h * 0.86, gy + (v.2 - gClefLineY) * h)
      shapes := .stroke (gClef.map fun sp =>
          { start := place sp.start
            segs := sp.segs.map fun s => { c1 := place s.c1, c2 := place s.c2, to := place s.to }
            closed := sp.closed }) 2.2 :: shapes
    -- opening and closing bar lines
    for x in [leftPad - 46.0, right] do
      shapes := .stroke [{ start := (x, top)
                         , segs := [{ c1 := (x, bottom), c2 := (x, bottom), to := (x, bottom) }] }] 1.6
                  :: shapes

    let slice := (items.drop (sys * st.perSystem)).take st.perSystem
    for (it, idx) in slice.zipIdx do
      let x := leftPad + (Float.ofNat idx + 0.5) * advance
      let d := Float.ofNat (diatonic it.pitch)
      -- each diatonic step is half a staff space, and y grows downward
      let y := bottom - (d - refLine) * (st.space / 2.0)
      -- ledger lines, at whole staff spaces above and below
      let mut k := 1
      while top - Float.ofNat k * st.space ≥ y - 0.1 && k ≤ 8 do
        let ly := top - Float.ofNat k * st.space
        shapes := .stroke [{ start := (x - st.space, ly)
                           , segs := [{ c1 := (x + st.space, ly), c2 := (x + st.space, ly),
                                        to := (x + st.space, ly) }] }] 1.3 :: shapes
        k := k + 1
      let mut j := 1
      while bottom + Float.ofNat j * st.space ≤ y + 0.1 && j ≤ 8 do
        let ly := bottom + Float.ofNat j * st.space
        shapes := .stroke [{ start := (x - st.space, ly)
                           , segs := [{ c1 := (x + st.space, ly), c2 := (x + st.space, ly),
                                        to := (x + st.space, ly) }] }] 1.3 :: shapes
        j := j + 1
      -- the accidental
      if needsSharp it.pitch then
        let sh := st.space * 1.9
        let place : Vec → Vec :=
          fun v => (x - st.space * 1.85 + v.1 * sh * 0.62, y - sh / 2.0 + v.2 * sh)
        shapes := .stroke (sharpSign.map fun sp =>
            { start := place sp.start
              segs := sp.segs.map fun s => { c1 := place s.c1, c2 := place s.c2, to := place s.to }
              closed := sp.closed }) 1.5 :: shapes
      -- stem: up when the head is below the middle line, down when above
      let middle := top + 2.0 * st.space
      let stemLen := st.space * 3.4
      let sx := if y > middle then x + st.space * 0.62 else x - st.space * 0.62
      let sy := if y > middle then y - stemLen else y + stemLen
      shapes := .stroke [{ start := (sx, y)
                         , segs := [{ c1 := (sx, sy), c2 := (sx, sy), to := (sx, sy) }] }] 1.5
                  :: shapes
      -- the head
      shapes := .head (x, y) (st.space * 0.68) (st.space * 0.50) (-0.34) :: shapes
      -- bar lines between groups
      if (idx + 1) % st.perBar == 0 && idx + 1 < slice.length then
        let bx := x + advance / 2.0
        shapes := .stroke [{ start := (bx, top)
                           , segs := [{ c1 := (bx, bottom), c2 := (bx, bottom), to := (bx, bottom) }] }] 1.1
                    :: shapes
      -- labels beneath
      if st.noteNames then
        shapes := .text (x, bottom + st.space * 2.1) it.pitch.name 9.0 1 :: shapes
      if !it.label.isEmpty then
        shapes := .text (x, bottom + st.space * 3.5) it.label 9.0 1 :: shapes

  return { width := width.toUInt32.toNat, height := height.toUInt32.toNat,
           shapes := shapes.reverse }

end Langlib.Velato.Sheet
