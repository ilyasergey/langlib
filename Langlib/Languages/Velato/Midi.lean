import Langlib.Languages.Velato.Note

/-!
# Velato: Standard MIDI Files

A Velato program *is* a MIDI file, so langlib has to read one. This module
is a small, self-contained implementation of the Standard MIDI File format
(SMF 1.0) in both directions: enough of the reader to recover a program's
note sequence, and enough of the writer to emit a file that a sequencer or a
synthesiser will play.

## What the reader keeps, and what it throws away

Almost everything. Velato reads pitch and order and nothing else, so
tempo, key and time signatures, note durations, velocities, rests, bar
lines and repeats are all invisible to the language. The reader therefore
returns an `Array Pitch`: the note numbers of the note-on events of the
first track that has any, in the order they appear in the file.

Three details of that sentence are load-bearing, and all three are the
reference implementation's:

* **Note-on with velocity zero is a note-off.** The format allows a
  performer's note-off to be encoded as a note-on with zero velocity, and
  most sequencers do exactly that. Counting those as notes would double
  every program.
* **In the order they appear in the file**, not in the order they sound.
  Notes of a chord have the same timestamp, so the file's order is the only
  order there is — which is why velato.net warns that the order of the
  notes inside a chord is part of the program.
* **The first track that has notes**, and only that one. Later tracks are
  ignored, which is what lets a Velato piece be accompanied: the program is
  the first track, and the harmony parts are free.

## Running status

The format lets a stream omit a repeated status byte, so a run of note-ons
can be a status byte followed by bare pairs of data bytes. A reader that
ignores this reads garbage from most real files, so the reader here tracks
it. Meta events (`FF`) and system-exclusive events (`F0`, `F7`) cancel
running status, as the specification requires.
-/

namespace Langlib.Velato.Midi

open Langlib.Velato

/-! ## Reading -/

/-- A cursor over the file's bytes. -/
private structure Cur where
  data : ByteArray
  pos : Nat

private def Cur.byte? (c : Cur) : Option (UInt8 × Cur) :=
  if h : c.pos < c.data.size then some (c.data[c.pos], { c with pos := c.pos + 1 })
  else none

/-- Read `n` big-endian bytes as a natural number. -/
private def Cur.beNat (c : Cur) : Nat → Option (Nat × Cur)
  | 0 => some (0, c)
  | n + 1 => do
    let (b, c) ← c.byte?
    let (rest, c) ← c.beNat n
    some (b.toNat * (256 ^ n) + rest, c)

/-- A variable-length quantity: seven bits per byte, high bit set on every
byte but the last. Delta times are written this way, and so are the lengths
of meta and system-exclusive events. The fuel bound is the bytes left, which
is more than the four a well-formed quantity can occupy. -/
private def Cur.vlq (c : Cur) : Nat → Nat → Option (Nat × Cur)
  | 0, _ => none
  | fuel + 1, acc => do
    let (b, c) ← c.byte?
    let acc := acc * 128 + (b.toNat % 128)
    if b.toNat ≥ 128 then c.vlq fuel acc else some (acc, c)

/-- How many data bytes a channel-voice status byte is followed by. Program
change and channel pressure take one; everything else takes two. -/
private def channelDataBytes (status : UInt8) : Nat :=
  match status.toNat / 16 with
  | 0xC | 0xD => 1
  | _ => 2

/-- Read the events of one track chunk, collecting the pitches of its
sounding note-ons.

`running` carries the last channel status byte. `fuel` is the bytes left in
the chunk, so the loop is structural. -/
private partial def readTrackEvents (c : Cur) (stop : Nat) (running : Option UInt8)
    (acc : Array Pitch) : Except String (Array Pitch) :=
  if c.pos ≥ stop then .ok acc
  else
    match c.vlq (stop - c.pos + 1) 0 with
    | none => .error "a MIDI track ends in the middle of a delta time"
    | some (_, c) =>
      match c.byte? with
      | none => .error "a MIDI track ends in the middle of an event"
      | some (b, c') =>
        if b == 0xFF then
          -- meta event: type byte, then a length-prefixed payload
          match c'.byte? with
          | none => .error "a MIDI meta event has no type byte"
          | some (_, c'') =>
            match c''.vlq (stop - c''.pos + 1) 0 with
            | none => .error "a MIDI meta event has no length"
            | some (len, c₃) => readTrackEvents { c₃ with pos := c₃.pos + len } stop none acc
        else if b == 0xF0 || b == 0xF7 then
          match c'.vlq (stop - c'.pos + 1) 0 with
          | none => .error "a MIDI system-exclusive event has no length"
          | some (len, c₃) => readTrackEvents { c₃ with pos := c₃.pos + len } stop none acc
        else
          -- a channel-voice event, possibly using running status
          let (status, c, _useRunning) :=
            if b.toNat ≥ 0x80 then (b, c', false) else
              match running with
              | some r => (r, c, true)
              | none => (0, c, true)
          if status.toNat < 0x80 then
            .error "a MIDI event uses running status before any status byte"
          else
            let n := channelDataBytes status
            match c.beNat n with
            | none => .error "a MIDI event is cut short by the end of its track"
            | some (_, cAfter) =>
              let acc :=
                if status.toNat / 16 == 0x9 then
                  -- note on: pitch is the first data byte, velocity the second,
                  -- and velocity zero means note off
                  match c.byte? with
                  | some (pitch, c₂) =>
                    match c₂.byte? with
                    | some (vel, _) => if vel.toNat > 0 then acc.push pitch.toNat else acc
                    | none => acc
                  | none => acc
                else acc
              readTrackEvents cAfter stop (some status) acc

/-- Read the pitches of a Standard MIDI File: the note-on events of the
first track that has any, in file order. -/
def readNotes (data : ByteArray) : Except String (Array Pitch) := do
  let c : Cur := { data, pos := 0 }
  let some (magic, c) := c.beNat 4 | .error "not a MIDI file: it is under four bytes long"
  if magic != 0x4D546864 then
    .error "not a MIDI file: it does not begin with the header chunk 'MThd'"
  let some (hdrLen, c) := c.beNat 4 | .error "a MIDI file with a truncated header"
  let some (_, c) := c.beNat 2 | .error "a MIDI file with a truncated header"
  let some (ntrks, c) := c.beNat 2 | .error "a MIDI file with a truncated header"
  let some (_, c) := c.beNat 2 | .error "a MIDI file with a truncated header"
  -- skip any header bytes beyond the six the format defines
  let mut c : Cur := { c with pos := 8 + hdrLen }
  for _ in [0:ntrks] do
    let some (tag, c') := c.beNat 4 | break
    let some (len, c') := c'.beNat 4 | .error "a MIDI track with no length"
    if tag == 0x4D54726B then
      let notes ← readTrackEvents c' (c'.pos + len) none #[]
      if !notes.isEmpty then return notes
    c := { c' with pos := c'.pos + len }
  .error "this MIDI file has no note-on events, so it is not a Velato program"

/-! ## Writing

The writer exists so that langlib can hand a composer, a synthesiser or
another Velato implementation a real `.mid` file — the examples in this
repository are kept in a readable text form, and `lake exe velato --midi`
turns one into the binary the language actually speaks.

A written file is format 1: a tempo track, then one track per voice. The
program is the first voice, so an accompaniment written into later tracks
changes nothing about what the file means. -/

/-- One sounding note, placed in absolute time. Chords are expressed by
giving several notes the same `start`; the writer emits them in list order,
which is the order Velato reads them in. -/
structure NoteEvent where
  pitch : Pitch
  /-- Onset, in ticks. -/
  start : Nat
  /-- Duration, in ticks. -/
  dur : Nat
  velocity : UInt8 := 80
deriving Repr, Inhabited

/-- A voice: a General MIDI program number, a name, and its notes. -/
structure Track where
  name : String := ""
  /-- General MIDI program: `0` is Acoustic Grand Piano. -/
  program : UInt8 := 0
  notes : List NoteEvent := []
deriving Repr, Inhabited

/-- A whole file: the pulses-per-quarter-note division, the tempo in
microseconds per quarter note, and the voices. -/
structure File where
  division : Nat := 480
  /-- Microseconds per quarter note; 500000 is 120 bpm. -/
  tempo : Nat := 500000
  tracks : List Track := []
deriving Repr, Inhabited

/-- Big-endian bytes of a number. -/
private def be (n width : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  for i in [0:width] do
    out := out.push (UInt8.ofNat (n / (256 ^ (width - 1 - i)) % 256))
  return out

/-- A variable-length quantity, seven bits at a time. -/
private def vlqBytes (n : Nat) : ByteArray := Id.run do
  -- collect the seven-bit groups, least significant first
  let mut groups : List Nat := []
  let mut k := n
  groups := [k % 128]
  k := k / 128
  for _ in [0:4] do
    if k > 0 then
      groups := (k % 128) :: groups
      k := k / 128
  let mut out := ByteArray.empty
  let last := groups.length - 1
  for (g, i) in groups.zipIdx do
    out := out.push (UInt8.ofNat (if i == last then g else g + 128))
  return out

/-- One MIDI event, flattened to an absolute time and its raw bytes. The
`seq` field breaks ties in a stable way: the writer sorts by `(time, seq)`,
and `seq` is the position the caller gave the note, so the note-on order
inside a chord is the order the caller wrote it. -/
private structure Raw where
  time : Nat
  seq : Nat
  bytes : ByteArray

/-- The bytes of one track chunk. -/
private def trackChunk (t : Track) (extraPrefix : ByteArray) : ByteArray := Id.run do
  let mut raws : Array Raw := #[]
  for (n, i) in t.notes.zipIdx do
    -- note-offs sort before note-ons at the same instant, so a repeated
    -- pitch is released before it is struck again
    let on := ByteArray.mk #[0x90, UInt8.ofNat (n.pitch % 128), n.velocity]
    let off := ByteArray.mk #[0x80, UInt8.ofNat (n.pitch % 128), 0]
    raws := raws.push { time := n.start, seq := 2 * i + 1, bytes := on }
    raws := raws.push { time := n.start + n.dur, seq := 2 * i, bytes := off }
  let sorted := raws.qsort fun a b =>
    if a.time == b.time then
      -- at the same instant, note-offs (even seq) come first
      if a.seq % 2 == b.seq % 2 then a.seq < b.seq else a.seq % 2 < b.seq % 2
    else a.time < b.time
  let mut body := extraPrefix
  if !t.name.isEmpty then
    body := body ++ ByteArray.mk #[0x00, 0xFF, 0x03] ++ vlqBytes t.name.toUTF8.size
      ++ t.name.toUTF8
  body := body ++ ByteArray.mk #[0x00, 0xC0, t.program]
  let mut last := 0
  for r in sorted do
    body := body ++ vlqBytes (r.time - last) ++ r.bytes
    last := r.time
  body := body ++ ByteArray.mk #[0x00, 0xFF, 0x2F, 0x00]
  return "MTrk".toUTF8 ++ be body.size 4 ++ body

/-- Render a file to Standard MIDI File bytes. -/
def File.toBytes (f : File) : ByteArray := Id.run do
  let ntrks := f.tracks.length + 1
  let mut out := "MThd".toUTF8 ++ be 6 4 ++ be 1 2 ++ be ntrks 2 ++ be f.division 2
  -- the conductor track carries the tempo and nothing else
  let tempoBytes := ByteArray.mk #[0x00, 0xFF, 0x51, 0x03] ++ be f.tempo 3
  out := out ++ trackChunk { name := "tempo" } tempoBytes
  for t in f.tracks do
    out := out ++ trackChunk t ByteArray.empty
  return out

/-- The simplest file a note sequence can become: one voice, one note per
beat. Used by `lake exe velato --midi` and by the example generator. -/
def ofNotes (notes : Array Pitch) (program : UInt8 := 0) (division : Nat := 480) : File :=
  let evs : List NoteEvent := (notes.toList.zipIdx).map fun (p, i) =>
    { pitch := p, start := i * division, dur := division * 7 / 8 }
  { division := division
    tracks := [{ name := "velato", program := program, notes := evs }] }

end Langlib.Velato.Midi
