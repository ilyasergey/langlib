# langlib

An open-source library of the semantics of esoteric and fun programming
languages, written in [Lean 4](https://lean-lang.org/).

Esoteric languages are not meant for realistic software. They exist to make a
point, to win a bet, to parody a committee, or simply to be difficult. Over the
last fifty years they have accumulated into a large body of design knowledge:
minimal instruction sets, string rewriting, stack machines on a torus,
self-modifying trit codes. This knowledge is scattered across personal pages,
wikis, and long-dead FTP servers. It is nice to have all these designs in one
place, written down precisely, and executable.

For each language, langlib provides:

* a **specification** in `docs/<langname>/`, summarising the language's
  history, semantics, and quirks, with credits to its authors;
* a **parser**, a **reference interpreter**, and a **standalone runner**
  written in Lean, under `Langlib/Languages/<Langname>/`;
* **examples** you can run for fun, and a **test suite**, including
  differential tests against non-Lean reference implementations where
  available.

On top of the interpreters, langlib develops **WTF** (Well-Typed Formalism, the
`.wtf` file extension), a small imperative language deeply embedded in Lean and
inspired by [Velvet](https://github.com/verse-lab/velvet), living under
`Langlib/WTF/`. WTF serves as a
human-readable front end: langlib builds compilers from WTF to the esoteric
languages, together with a verification pipeline for proving these compilers
correct. In the longer term the plan is to compile shallowly-embedded Velvet
programs to WTF, and from there to any esolang in the library, using relational
compilation.

## Building

Install [elan](https://github.com/leanprover/elan), then:

```
lake build          # build the libraries and runners
lake test           # run the test suite
```

## Languages

Currently implemented (see [docs/README.md](docs/README.md) for the full
status matrix, including compilers):

* [brainfuck](docs/brainfuck/spec.md) (Urban Müller, 1993)
* [fractran](docs/fractran/spec.md) (John Conway, 1987)
* [subleq](docs/subleq/spec.md) (folklore OISC, de-facto conventions by
  Oleg Mazonka)
* [whitespace](docs/whitespace/spec.md) (Edwin Brady & Chris Morris, 2003)
* [ook](docs/ook/spec.md) (David Morgan-Mar, 2001)
* [deadfish](docs/deadfish/spec.md) (Jonathan Todd Skinner, 2006)
* [WTF](docs/wtf/spec.md), the Well-Typed Formalism: the library's own
  human-readable front end

In progress: malbolge, thue, befunge93, piet, brainloller, and the
compilers from WTF to each target. The roadmap of languages still to be
implemented lives in
[docs/ROADMAP.md](docs/ROADMAP.md), and a survey of related efforts in
[docs/RELATED.md](docs/RELATED.md).

## Running programs

Each language ships a runner named after it. Programs read from stdin and
write to stdout, so pipe or redirect input, and the result is printed to
your terminal. One example per language, with what you should see:

Brainfuck says hello.

```
$ lake exe brainfuck Langlib/Examples/Brainfuck/hello.b
Hello World!
```

Brainfuck reverses a word, reading it from stdin.

```
$ echo -n stressed | lake exe brainfuck --eof zero Langlib/Examples/Brainfuck/rev.b
desserts
```

Erik Bosman's 505-byte brainfuck quine prints itself, so `diff` says nothing.

```
$ lake exe brainfuck Langlib/Examples/Brainfuck/quine.b | diff - Langlib/Examples/Brainfuck/quine.b
```

Whitespace says hello, using a program made entirely of spaces and tabs.

```
$ lake exe whitespace Langlib/Examples/Whitespace/hello.ws
Hello, World!
```

Ook! says hello, because brainfuck was not quite unreadable enough.

```
$ lake exe ook Langlib/Examples/Ook/hello.ook
Hello World!
```

Deadfish prints the ASCII codes of a greeting, one number per line, since
printing letters is beyond it.

```
$ lake exe deadfish Langlib/Examples/Deadfish/hello.df
72
101
108
...
```

Subleq counts down on a machine with exactly one instruction.

```
$ lake exe subleq Langlib/Examples/Subleq/countdown.sq
9876543210
```

FRACTRAN runs Conway's PRIMEGAME, which prints the primes as exponents of
two. It has no halting condition, so cap it with `--fuel`.

```
$ lake exe fractran --n 2 --out pow2 --fuel 2000000 Langlib/Examples/Fractran/primegame.ft
2
3
5
7
...
```

WTF, the readable front end, computes an integer square root.

```
$ echo 17 | lake exe wtf run Langlib/Examples/WTF/isqrt.wtf
4
```

WTF prints the primes up to 20, using the same trial division you would
write in any language.

```
$ echo 20 | lake exe wtf run Langlib/Examples/WTF/primes.wtf
2
3
5
7
11
13
17
19
```

Every runner accepts `--fuel N` (step budget), `--verbose` (report how the
run ended: halted, runtime error, or out of fuel), and `--help`. Exit codes:
0 halted, 1 runtime error, 2 out of fuel, 3 parse or usage error. Example
programs state their own usage in a comment where the language permits one;
each language's README under `Langlib/Languages/` has the full example
inventory.

## Contributing

Contributions of new languages, examples, tests, and proofs are welcome. See
[CONTRIBUTING.md](CONTRIBUTING.md) for how to add a language and what the
library expects from a submission.

## License

langlib is distributed under the Apache 2.0 license (see [LICENSE](LICENSE)).
The library only implements languages whose designs are in the public domain
or otherwise freely implementable; all example programs are either original,
in the public domain, or credited to their authors under permissive terms.
