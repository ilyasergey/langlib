# Compiling Turpentine to Brainloller

* **Status**: free, once the brainfuck backend lands.
* **Family**: TapeIR, via brainfuck.

## Also nothing to write

Brainloller is brainfuck encoded in pixel colours, and
`Langlib/Languages/Brainloller/` already contains both directions: a
decoder that produces a `Langlib.Brainfuck.Prog` and an encoder that turns
a brainfuck program into a PPM image. Compiling Turpentine to Brainloller
is therefore compiling it to brainfuck and calling the existing encoder,
with a width chosen for the aspect ratio you want.

The one decision is the image width, which controls how often the program
snakes back on itself using the rotation codels. Wide images are shorter
programs; narrow ones look better. Neither affects semantics.

## Fragment

Exactly the brainfuck backend's fragment. See
[docs/brainfuck/compiler.md](../brainfuck/compiler.md).

## Correctness

The brainfuck simulation theorem composed with the encoder-decoder
round-trip lemma, which the existing tests already exercise at several
widths.
