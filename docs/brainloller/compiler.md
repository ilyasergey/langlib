# Compiling Turpentine to Brainloller

* **Status**: free, once the brainfuck backend lands.
* **Family**: TapeIR, via brainfuck.

* **Implementation**: none yet; it would go in `Langlib/Turpentine/Compile/Brainloller.lean`, beside the [whitespace backend](../../Langlib/Turpentine/Compile/Whitespace.lean).

## Compile and run one, once this exists

Not yet implemented, so these commands do not work today. They are the
interface this page is a plan for, and they are what the other backends
already do (see `docs/whitespace/compiler.md` for a working example).

```
$ lake exe turpentine compile --to brainloller -o /tmp/hello.ppm Langlib/Examples/Turpentine/hello.turp
$ lake exe brainloller --eof zero /tmp/hello.ppm
Hello, Turpentine!
```

Or in one step, compiling in memory and running the result on the
brainloller interpreter:

```
$ lake exe turpentine exec --via brainloller Langlib/Examples/Turpentine/hello.turp
Hello, Turpentine!
```

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
