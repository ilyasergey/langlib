import Langlib.Languages.Velato.Midi

/-!
# Velato: hearing a program

A Velato program is music, so a runner that can only print its output is
missing half the point. This module synthesises a note sequence into a WAV
file — 16-bit PCM, 44.1 kHz, mono — with no dependency on anything outside
Lean. `lake exe velato --wav out.wav prog.vel` writes one, and
`scripts/velato-audio.sh` plays it with whatever the machine already has.

Writing a synthesiser rather than shelling out to one is the same decision
the raster backend in `Render.lean` makes, and for the same reason: a WAV
file is a header and a block of samples, so the alternative — requiring
FluidSynth, a SoundFont and a working audio toolchain before anyone can
listen to an example — costs far more than it saves. `--midi` is still
there for anyone who wants a real instrument.

## The instrument

Each note is a sum of a fundamental and five harmonics with amplitudes
falling as `1/n^1.6`, through a plucked envelope: a two-millisecond attack,
then exponential decay. That is roughly a plucked string or an electric
piano, and it was chosen because Velato's dense chords turn to mud under
anything with a slow attack or a strong second harmonic. Notes are summed
and the result is scaled once, at the end, by whatever keeps the loudest
sample inside range, so a thick chord neither clips nor forces the whole
piece to be quiet.
-/

namespace Langlib.Velato.Audio

open Langlib.Velato

/-- Concert pitch: the frequency of MIDI note 69, A4. -/
def a440 : Float := 440.0

/-- The frequency of a MIDI note in equal temperament. -/
def freqOf (p : Pitch) : Float :=
  a440 * Float.exp ((Float.ofNat p - 69.0) * 0.6931471805599453 / 12.0)

/-- Synthesis settings. -/
structure Settings where
  sampleRate : Nat := 44100
  /-- Seconds per note. -/
  noteLen : Float := 0.34
  /-- How long a note rings after the next one starts, as a multiple of
  `noteLen`; overlap is what makes a run of notes sound legato rather than
  like a row of clicks. -/
  ring : Float := 2.2
  /-- Seconds of silence after the last note. -/
  tail : Float := 0.6
deriving Inhabited

/-- The amplitude envelope of a plucked note at time `t` seconds after its
onset: a short linear attack, then an exponential decay. -/
def envelope (t : Float) : Float :=
  if t < 0.0 then 0.0
  else if t < 0.002 then t / 0.002
  else Float.exp (-(t - 0.002) * 2.6)

/-- One note's contribution at time `t` seconds after its onset. -/
def voice (freq t : Float) : Float := Id.run do
  let e := envelope t
  if e < 0.0005 then return 0.0
  let τ := 6.283185307179586
  -- a fundamental and five harmonics, thinning out as they climb
  let mut sum := 0.0
  for k in [1:7] do
    let n := Float.ofNat k
    let amp := 1.0 / (n * n.sqrt)
    sum := sum + amp * Float.sin (τ * freq * n * t)
  return e * sum * 0.32

/-- Render a note sequence to mono floating-point samples. -/
def renderNotes (notes : Array Pitch) (cfg : Settings := {}) : Array Float := Id.run do
  let sr := Float.ofNat cfg.sampleRate
  let step := cfg.noteLen
  let total := step * Float.ofNat notes.size + cfg.noteLen * cfg.ring + cfg.tail
  let n := (total * sr).toUInt64.toNat + 1
  let mut buf : Array Float := Array.replicate n 0.0
  let ringSamples := ((cfg.noteLen * cfg.ring) * sr).toUInt64.toNat
  for (p, i) in notes.toList.zipIdx do
    let f := freqOf p
    let onset := ((Float.ofNat i * step) * sr).toUInt64.toNat
    for j in [0:ringSamples] do
      let idx := onset + j
      if idx < n then
        let t := Float.ofNat j / sr
        buf := buf.set! idx (buf[idx]! + voice f t)
  return buf

/-- Little-endian bytes. -/
private def le (v width : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  let mut k := v
  for _ in [0:width] do
    out := out.push (UInt8.ofNat (k % 256))
    k := k / 256
  return out

/-- Wrap samples in a WAV container: 16-bit PCM, mono, normalised so the
loudest sample sits just under full scale. -/
def toWav (samples : Array Float) (sampleRate : Nat := 44100) : ByteArray := Id.run do
  -- one gain for the whole piece, so a dense chord does not clip and a
  -- sparse passage is not inaudible
  let mut peak := 0.0
  for s in samples do
    let a := if s < 0.0 then -s else s
    if a > peak then peak := a
  let gain := if peak < 0.0001 then 0.0 else 30000.0 / peak
  let mut data := ByteArray.empty
  for s in samples do
    let v := s * gain
    let v := if v > 32767.0 then 32767.0 else if v < -32767.0 then -32767.0 else v
    let iv : Int := if v < 0.0 then -((-v).toUInt64.toNat : Int) else ((v.toUInt64.toNat : Nat) : Int)
    -- two's complement, little-endian
    let u := if iv < 0 then (65536 + iv).toNat else iv.toNat
    data := data ++ le u 2
  let byteRate := sampleRate * 2
  let header :=
    "RIFF".toUTF8 ++ le (36 + data.size) 4 ++ "WAVE".toUTF8
      ++ "fmt ".toUTF8 ++ le 16 4 ++ le 1 2 ++ le 1 2
      ++ le sampleRate 4 ++ le byteRate 4 ++ le 2 2 ++ le 16 2
      ++ "data".toUTF8 ++ le data.size 4
  return header ++ data

/-- The whole pipeline: notes to a playable WAV file. -/
def notesToWav (notes : Array Pitch) (cfg : Settings := {}) : ByteArray :=
  toWav (renderNotes notes cfg) cfg.sampleRate

end Langlib.Velato.Audio
