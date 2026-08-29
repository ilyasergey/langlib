# Malbolge Unshackled in LangLib

Ørjan Johansen's 2007 variant of Ben Olmstead's Malbolge, with the memory
bound taken out: values are 3-adic integers whose trit sequence is
eventually constant, so registers and memory are unbounded. That single
change makes the language Turing complete, where Malbolge — 59049 words of
59049 values — provably is not. The full specification, the differences
from Malbolge, and what the language leaves to the implementation are in
[docs/malbolge-unshackled/spec.md](../../../docs/malbolge-unshackled/spec.md).

## Modules

* `Syntax.lean`: trits, values and their normalisation, the crazy
  operation, the variable-width rotation, the successor used for both
  pointers, the mod-94 rule for values that are not naturals, the eight
  instructions, and the encryption table.
* `Parser.lean`: the loader. It fills the rest of memory with the crazy
  operation of the last two words, as Malbolge does, and reports the line
  and column of an illegal instruction.
* `Semantics.lean`: the pure, fuel-based reference evaluator.
* `Main.lean`: the standalone runner.

## Running

```
lake exe malbolge-unshackled [--fuel N] [--rot-width N] [--strict] file.mu
```

Two flags beyond the shared ones, both corresponding to freedoms of the
language rather than of the runner:

* `--rot-width N` sets the starting rotation width. The language promises
  only that it is at least 10 and that it grows when `j` widens `d`, so a
  correct program must work at every setting. Johansen's interpreter
  randomises it on every run for that reason; ours is deterministic so that
  a sweep can be done by hand, and the test suite runs `hello.mu` at two
  widths.
* `--strict` is Johansen's `-n`: reject source characters outside 33..126
  instead of loading them unchecked.

Exit codes: 0 halt, 2 out of fuel, 3 usage error, 4 parse error, 5 runtime
error. Many Unshackled programs never halt by design, so run those with a
modest `--fuel`.

## Examples ([Langlib/Examples/MalbolgeUnshackled/](../../Examples/MalbolgeUnshackled/))

Unshackled has no comment syntax — every source character is an
instruction — so attribution lives here.

| File | What it does | Origin |
|------|--------------|--------|
| `hello.mu` | prints `Hello, world!` and halts | provenance not recorded (see below) |
| `truth.mu` | truth machine: prints `0` and halts, or prints `1` forever | provenance not recorded |
| `cat.mu` | copies stdin to stdout, then never halts | provenance not recorded |
| `rotcrash.mu` | `'bO`: rotates a word, then dies because the rotated word has no encryption | LangLib original |

Usage, since the files cannot carry their own:

```
echo -n 0 | lake exe malbolge-unshackled Langlib/Examples/MalbolgeUnshackled/truth.mu
```

Nobody writes Unshackled by hand: these programs are search or compiler
output, as every Malbolge program is. The three here arrived with an
earlier, unfinished branch of this implementation and their authorship was
never recorded, which is a gap this table should not have — Malbolge's own
examples credit Cooke and Scheffer by name. They run correctly under this
interpreter, and the likely source is Johansen's own distribution; if you
know, put the credit here.

## Tests

Golden tests live in
[Langlib/Tests/MalbolgeUnshackled.lean](../../Tests/MalbolgeUnshackled.lean)
(run with `lake test` from the repository root): the three examples,
micro-programs for halt, output and input, the two Unshackled-specific
behaviours (end of input closes the output stream; a rotated or
crazy-operated word has no encryption), `hello.mu` at a second rotation
width, strict loading, and the loader's errors.
