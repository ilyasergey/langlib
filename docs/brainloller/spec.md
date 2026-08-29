# brainloller

* **Author**: Lode Vandevenne
* **Year**: 2005
* **Canonical source**: https://esolangs.org/wiki/Brainloller (CC0)
* **In langlib**: `Langlib/Languages/Brainloller/`, runner
  `lake exe brainloller`, examples in `Langlib/Examples/Brainloller/`

## The idea

Brainloller is brainfuck, encoded one command per pixel. Where Piet makes
you *compute* with colour, Brainloller just spray-paints brainfuck onto a
bitmap: eight colours for the eight commands, two more to steer the
reading head, and every other colour is a comment. Vandevenne (also the
author of LodePNG, a man who clearly thinks in pixels) published it in
2005; the wiki page is CC0, so the design is free to implement.

## Decoding

| colour | RGB | means |
|--------|-----|-------|
| red | 255,0,0 | `>` |
| dark red | 128,0,0 | `<` |
| green | 0,255,0 | `+` |
| dark green | 0,128,0 | `-` |
| blue | 0,0,255 | `.` |
| dark blue | 0,0,128 | `,` |
| yellow | 255,255,0 | `[` |
| dark yellow | 128,128,0 | `]` |
| cyan | 0,255,255 | rotate the instruction pointer 90° clockwise |
| dark cyan | 0,128,128 | rotate it 90° counterclockwise |
| anything else | | no-op |

The instruction pointer starts on the top-left pixel heading east, reads
the pixel it stands on, then moves one pixel in its current heading.
Rotations take effect before the move. When the pointer walks off the
image, decoding ends and the collected brainfuck program runs. The
rotation colours exist so a long program can snake through a rectangle
instead of being one endless row.

## Semantic decisions in langlib

1. **Colours match exactly.** Only the ten RGB values above mean
   anything; all 16777206 others are no-ops (that is the spec, and it is
   also how Brainloller programs carry decorations).
2. **Execution is our brainfuck core**, `Langlib.Brainfuck.evalProg`,
   with all of its documented conventions (8-bit wrapping cells, tape
   unbounded to the right, error left of cell 0, EOF `unchanged` by
   default with `--eof zero|minus1` available): see
   `docs/brainfuck/spec.md`. Vandevenne's page says little more than
   "wrapping bytes", so we inherit rather than invent. Bracket mismatches
   in the decoded pixels are reported by the brainfuck parser.
3. **A pointer that never leaves the image is a parse error.** The
   pointer's state is (pixel, heading), so a walk longer than
   `4 * width * height` steps has repeated a state and will loop forever;
   we detect that instead of spinning.
4. **The encoder** (`Langlib.Brainloller.encode`, or
   `lake exe brainloller --encode out.ppm [--width N] file.b`) lays
   commands left to right, and with `--width N` wraps them into a
   serpentine: two clockwise turns (cyan) take the pointer down and back
   west at the right edge, two counterclockwise turns (dark cyan) turn it
   at the left edge, and black pixels pad the gaps. Decoding an encoded
   image yields exactly the command characters of the source (comments
   are dropped); round-trip tests pin this down.

## Trying it

The runner reads program files as text, so feed it ASCII PPM (P3);
convert anything else first, for example with
`magick prog.png -compress none prog.ppm`.

Hello world, as a 12 by 11 picture.

```
$ lake exe brainloller Langlib/Examples/Brainloller/hello.ppm
Hello World!
```

cat, which needs `--eof zero` for the same reason its brainfuck original
does.

```
$ echo -n meow | lake exe brainloller --eof zero Langlib/Examples/Brainloller/cat.ppm
meow
```

The encoder turns any brainfuck program into a picture. The width
controls how often the image snakes back on itself with rotation codels.

```
$ lake exe brainloller --encode /tmp/hello.ppm --width 12 Langlib/Examples/Brainfuck/hello.b
brainloller: wrote 12x12 image to /tmp/hello.ppm
```

That picture is a program, so run it.

```
$ lake exe brainloller /tmp/hello.ppm
Hello World!
```

Both shipped examples were produced by our own encoder from the brainfuck
examples, which makes them langlib originals of programs that were
already CC0 or folklore.

