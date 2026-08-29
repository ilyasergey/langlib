# Compiling Turpentine to Ook!

* **Status**: free, once the brainfuck backend lands.
* **Family**: TapeIR, via brainfuck.

* **Implementation**: none yet; it would go in `Langlib/Turpentine/Compile/Ook.lean`, beside the [whitespace backend](../../Langlib/Turpentine/Compile/Whitespace.lean).

## Compile and run one, once this exists

Not yet implemented, so these commands do not work today. They are the
interface this page is a plan for, and they are what the other backends
already do (see `docs/whitespace/compiler.md` for a working example).

```
lake exe turpentine compile --to ook -o /tmp/hello.ook Langlib/Examples/Turpentine/hello.turp
```

Then run it:

```
lake exe ook --eof zero /tmp/hello.ook
```

Output:

```
Hello, Turpentine!
```

Or in one step, compiling in memory and running the result on the
ook interpreter:

```
lake exe turpentine exec --via ook Langlib/Examples/Turpentine/hello.turp
```

Output:

```
Hello, Turpentine!
```

## There is nothing to write

Ook! is brainfuck with the eight commands spelled as pairs of orangutan
noises. `Langlib/Languages/Ook/` does not have its own interpreter: it
parses into `Langlib.Brainfuck.Prog` and calls the brainfuck evaluator.
The compiler inherits the same shortcut. Compiling Turpentine to Ook! is
compiling it to brainfuck and then rendering the result with
`Langlib.Ook.render`, which is already implemented and already tested
(the round-trip suite in `Langlib/Tests/Ook.lean` checks
`parse . render = id`).

So this backend is a one-line composition, and its correctness proof is a
one-line composition too: the brainfuck simulation theorem composed with
the rendering isomorphism. That is the entire content of this page, and it
is the best argument in the library for why the compilers should be
organised into families with a shared IR.

## Fragment

Exactly the brainfuck backend's fragment. See
[docs/brainfuck/compiler.md](../brainfuck/compiler.md).

## Size warning

Ook! source is roughly nine times the size of the equivalent brainfuck,
since every command becomes two three-character words plus separators. A
compiled Turpentine program of any substance will be a large and very
silly file. This is not a defect.
