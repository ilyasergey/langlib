import Langlib.Common.Runner
import Langlib.Languages.Velato.Semantics
import Langlib.Languages.Velato.Render
import Langlib.Languages.Velato.Audio

/-!
# Velato: standalone runner

```
lake exe velato [--fuel N] [--verbose] <file.vel | file.mid>
```

The runner accepts a program in either of Velato's two forms and tells them
apart by looking at the file: a Standard MIDI File starts with the four
bytes `MThd`, and anything else is read as langlib's text form, a list of
scientific pitch names.

Besides running a program it will show it, in every form a composer or a
reader might want:

```
--ast              print the program as structured pseudocode
--notes            print each note with its interval and its role
--sheet FILE       engrave as sheet music: .pdf, .svg, .png or .ppm
--midi FILE        write a Standard MIDI File
--wav FILE         synthesise audio (16-bit PCM, 44.1 kHz, mono)
--plain            engrave without the note-role labels
--scale N          multiply the raster size (PNG/PPM only; default 2)
```

`--sheet` picks its format from the extension. PNG goes out as a PPM
alongside a note that `scripts/ppm-to-png.py` converts it, because the PNG
encoder lives in that script rather than here; PDF and SVG are written
directly.
-/

namespace Langlib.Velato

open Langlib.Common

/-- The pure entry point the test harness and `Runner` use. -/
def runner : Runner where
  name := "velato"
  ext := "vel"
  run := run
  usageExtra :=
    [ "  a program may be a MIDI file (.mid) or langlib's text form (.vel):"
    , "  whitespace-separated pitch names such as 'C4 A4 G4 E4'"
    , "  --ast          print the program as structured pseudocode"
    , "  --notes        print each note with its interval and its role"
    , "  --sheet FILE   engrave as sheet music (.pdf, .svg, .ppm)"
    , "  --midi FILE    write a Standard MIDI File"
    , "  --wav FILE     synthesise audio (16-bit PCM, 44.1 kHz, mono)"
    , "  --plain        engrave without the note-role labels"
    , "  --scale N      multiply the raster size (.ppm only; default 2)" ]

/-- Read a program file as a note sequence, accepting either form. -/
def loadNotes (path : String) (bytes : ByteArray) : Except String (Array Pitch) :=
  if bytes.size ≥ 4 && bytes[0]! == 0x4D && bytes[1]! == 0x54
      && bytes[2]! == 0x68 && bytes[3]! == 0x64 then
    Midi.readNotes bytes
  else
    match String.fromUTF8? bytes with
    | some s => parseNoteText s
    | none => .error s!"'{path}' is neither a MIDI file nor UTF-8 text"

/-- The note-by-note listing `--notes` prints: index, pitch, the interval
from the command root in force there, and what the parser made of it. -/
def listing (notes : Array Pitch) (labels : Array String) : String := Id.run do
  let mut out := "  #  note   role\n"
  for (p, i) in notes.toList.zipIdx do
    let name := p.name
    let pad := "".pushn ' ' (6 - min 6 name.length)
    let idx := toString (i + 1)
    let ipad := "".pushn ' ' (3 - min 3 idx.length)
    out := out ++ s!"{ipad}{idx}  {name}{pad} {labels[i]!}\n"
  return out

end Langlib.Velato

open Langlib.Common Langlib.Velato in
def main (args : List String) : IO UInt32 := do
  -- pull off velato's own flags, then hand the rest to the shared runner
  let mut fuel := 200_000_000
  let mut file? : Option String := none
  let mut showAst := false
  let mut showNotes := false
  let mut sheet? : Option String := none
  let mut midi? : Option String := none
  let mut wav? : Option String := none
  let mut plain := false
  let mut scale := 2
  let mut verbose := false
  let mut rest := args
  repeat
    match rest with
    | [] => break
    | "--help" :: _ => IO.println runner.usage; return 0
    | "--ast" :: rs => showAst := true; rest := rs
    | "--notes" :: rs => showNotes := true; rest := rs
    | "--plain" :: rs => plain := true; rest := rs
    | "--verbose" :: rs => verbose := true; rest := rs
    | "--sheet" :: f :: rs => sheet? := some f; rest := rs
    | "--midi" :: f :: rs => midi? := some f; rest := rs
    | "--wav" :: f :: rs => wav? := some f; rest := rs
    | "--scale" :: n :: rs =>
      match n.toNat? with
      | some k => scale := max 1 k; rest := rs
      | none => IO.eprintln s!"velato: --scale expects a number, got '{n}'"; return 3
    | "--fuel" :: n :: rs =>
      match n.toNat? with
      | some k => fuel := k; rest := rs
      | none => IO.eprintln s!"velato: --fuel expects a number, got '{n}'"; return 3
    | a :: rs =>
      if a.startsWith "--" then
        IO.eprintln s!"velato: unknown flag '{a}'"
        IO.eprintln runner.usage
        return 3
      else if file?.isSome then
        IO.eprintln "velato: more than one input file"; return 3
      else
        file? := some a; rest := rs
  let some file := file? | IO.eprintln runner.usage; return 3
  let bytes ← try IO.FS.readBinFile file
    catch e => IO.eprintln s!"velato: cannot read '{file}': {e}"; return 3
  let notes ← match loadNotes file bytes with
    | .ok ns => pure ns
    | .error m => IO.eprintln s!"velato: {m}"; return 3
  let (prog, labels) ← match parseNotesAnnotated notes with
    | .ok r => pure r
    | .error m => IO.eprintln s!"velato: {m}"; return 3

  -- the things that only look at the program
  if showNotes then IO.print (listing notes labels)
  if showAst then IO.print prog.render

  if let some out := midi? then
    IO.FS.writeBinFile out (Midi.ofNotes notes).toBytes
    if verbose then IO.eprintln s!"velato: wrote {out}"
  if let some out := wav? then
    IO.FS.writeBinFile out (Audio.notesToWav notes)
    if verbose then IO.eprintln s!"velato: wrote {out}"
  if let some out := sheet? then
    let items : List Sheet.Item :=
      (notes.toList.zipIdx).map fun (p, i) =>
        { pitch := p, label := if plain then "" else (labels[i]!) }
    -- the title is the program's name, not the path it happened to sit at,
    -- so a rendered sheet is the same wherever the repository is checked out
    let base := (file.splitOn "/").getLast!
    let scene := Sheet.engrave items {} (title := base)
    if out.endsWith ".svg" then
      IO.FS.writeFile out scene.toSvg
    else if out.endsWith ".pdf" then
      IO.FS.writeBinFile out (scene.toPdf base)
    else
      IO.FS.writeFile out (scene.toImage scale).toPpm3
    if verbose then IO.eprintln s!"velato: wrote {out}"

  -- and then, unless we were only asked to look at it, run it
  if showAst || showNotes || sheet?.isSome || midi?.isSome || wav?.isSome then
    return 0
  let stdinStream ← IO.getStdin
  let stdin ← if ← stdinStream.isTty then pure ByteArray.empty
              else stdinStream.readBinToEnd
  let res := evalProg prog (Input.ofByteArray stdin) fuel
  let out ← IO.getStdout
  out.write res.output
  out.flush
  match res.exit with
  | .halted => return 0
  | .error msg => IO.eprintln s!"velato: runtime error: {msg}"; return 1
  | .outOfFuel =>
    IO.eprintln s!"velato: out of fuel after {fuel} steps (raise with --fuel)"
    return 2
