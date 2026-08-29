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

On top of the interpreters sits **[Turpentine](docs/turpentine/spec.md)**
(`.turp`), a small readable imperative language that compiles to the
esoteric ones. It is named for
the solvent: a [Turing tarpit](https://en.wikipedia.org/wiki/Turing_tarpit)
is a language in which everything is possible and nothing is easy, and
turpentine dissolves tar. Write the program once with variables and loops,
and let the compiler suffer.

For each language, langlib provides:

* a **specification** in `docs/<langname>/`, summarising the language's
  history, semantics, and quirks, with credits to its authors;
* a **parser**, a **reference interpreter**, and a **standalone runner**
  written in Lean, under `Langlib/Languages/<Langname>/`;
* **examples** you can run for fun, and a **test suite**, including
  differential tests against non-Lean reference implementations where
  available;
* a **computational-class result**: a claim that the language is or is not
  Turing complete, and a machine-checked proof of it;
* where the language can host one, a **compiler from Turpentine**.

## Computability

Esolang folklore is full of claims nobody has checked. Every language here
gets a claim about its computational class and a machine-checked proof,
stated against the Turing machine and register machine from
[cslib](https://github.com/leanprover/cslib). Completeness is proved by
compiling a universal machine into the language; incompleteness by
bounding its state space. Status per language is in the
[status matrix](docs/README.md), the plan is
[Stage 8](docs/PLAN.md), and `scripts/axioms.lean` audits every result,
since a proof resting on `sorry` type-checks like a real one.

The components:

* [Langlib/Computability/Class.lean](Langlib/Computability/Class.lean) —
  `Esolang`, `TuringComplete` and `BoundedStorage`: one interface every
  result is an instance of.
* [Langlib/Computability/Whitespace.lean](Langlib/Computability/Whitespace.lean) —
  **Whitespace is proved Turing complete.** Axiom-clean.
* [Langlib/Computability/URM.lean](Langlib/Computability/URM.lean) — the
  register machine the proofs are stated against.
* [scripts/axioms.lean](scripts/axioms.lean) — the audit.
* [docs/README.md](docs/README.md) — status per language.

Precision here has already paid. [Befunge-93](docs/befunge93/spec.md) is
called incomplete because of its 80 by 25 playfield, but the real argument
is that the reference implementation gives it byte-sized cells, making it
a pushdown automaton. Our cells hold unbounded integers, so the language
we implement *is* complete. Same name, two languages.

## Verified compilers

Two strategies, and langlib keeps both. **Bespoke** compilers are written
by hand per target, accept the whole of Turpentine, and produce small
output: this is what `lake exe turpentine compile` runs today for
brainfuck, whitespace and subleq. **Via the URM**, a compiler comes free
from a completeness proof, because such a proof already contains a
verified compiler from a register machine; composing it with one
Turpentine-to-register-machine pass yields a correct-by-construction
compiler into every language proved complete.

Neither subsumes the other. Derived compilers are verified but enormous
and restricted to an I/O-free fragment; bespoke ones are practical but so
far unverified, and the derived one is the oracle that tests them. Both
are instances of one `TurpentineCompiler` interface, so agreement between
them is a theorem rather than a hope. The pipeline and its diagrams are in
[certified-compilation.md](docs/certified-compilation.md), the correctness
statements in [verification.md](docs/verification.md), and each target's
own decisions in `docs/<langname>/compiler.md`, for example
[whitespace](docs/whitespace/compiler.md),
[subleq](docs/subleq/compiler.md) and
[brainfuck](docs/brainfuck/compiler.md).

The components:

* [Langlib/Turpentine/Compile/](Langlib/Turpentine/Compile/) — the bespoke
  backends: [brainfuck](Langlib/Turpentine/Compile/Brainfuck.lean),
  [whitespace](Langlib/Turpentine/Compile/Whitespace.lean),
  [subleq](Langlib/Turpentine/Compile/Subleq.lean).
* [docs/certified-compilation.md](docs/certified-compilation.md) — the
  pipeline, the theorem that makes it compose, and the diagrams.
* [docs/verification.md](docs/verification.md) — what compiler correctness
  means here, including how `assert` compiles.
* Per target: `docs/<langname>/compiler.md`, for example
  [whitespace](docs/whitespace/compiler.md) and
  [brainfuck](docs/brainfuck/compiler.md).

Turpentine is deeply embedded in Lean and modelled on
[Velvet](https://github.com/verse-lab/velvet). The longer-term plan is to
compile shallowly-embedded Velvet to Turpentine, and from there to any
esolang here, by relational compilation.

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
* [befunge93](docs/befunge93/spec.md) (Chris Pressey, 1993)
* [malbolge](docs/malbolge/spec.md) (Ben Olmstead, 1998)
* [thue](docs/thue/spec.md) (John Colagioia, 2000)
* [piet](docs/piet/spec.md) (David Morgan-Mar, 2002), whose programs are
  abstract paintings
* [brainloller](docs/brainloller/spec.md) (Lode Vandevenne, 2005),
  brainfuck encoded in pixels
* [Turpentine](docs/turpentine/spec.md): the library's own human-readable
  front end, named for what dissolves a Turing tarpit

[whitespace](docs/whitespace/spec.md) is **proved Turing complete**, the
first entry in that column; the proof is in
[Langlib/Computability/Whitespace.lean](Langlib/Computability/Whitespace.lean).

Part-written and not yet wired in: Malbolge Unshackled, Unlambda and SKI.
The roadmap of languages still to be implemented lives in
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

Piet says hi, using a program that is an abstract painting.

```
$ lake exe piet Langlib/Examples/Piet/hi.ppm
Hi
```

Brainloller runs a brainfuck program encoded as coloured pixels.

```
$ lake exe brainloller Langlib/Examples/Brainloller/hello.ppm
Hello World!
```

Malbolge prints the hello world that a search program found in 2000,
because no human could write one. The capitalisation is not a typo.

```
$ lake exe malbolge Langlib/Examples/Malbolge/hello.mal
HEllO WORld
```

Turpentine, the readable front end, computes an integer square root.

```
$ echo 17 | lake exe turpentine run Langlib/Examples/Turpentine/isqrt.turp
4
```

Turpentine prints the primes up to 20, using the same trial division you would
write in any language.

```
$ echo 20 | lake exe turpentine run Langlib/Examples/Turpentine/primes.turp
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

## Documentation

* [docs/README.md](docs/README.md): the status matrix, one row per
  language, with computational class and compiler status.
* [docs/PLAN.md](docs/PLAN.md): the staged workplan.
* [docs/certified-compilation.md](docs/certified-compilation.md): verified
  compilation via the URM, with dependency diagrams.
* [docs/verification.md](docs/verification.md): what compiler correctness
  means here and how the proofs factor.
* [docs/TESTING.md](docs/TESTING.md): the two test layers, and what to
  install to run the differential tests.
* [docs/ROADMAP.md](docs/ROADMAP.md): candidate languages.
* [docs/RELATED.md](docs/RELATED.md): other people's formalisations.
* [docs/PROGRESS.md](docs/PROGRESS.md): dated log, newest first.
* Per language: `docs/<langname>/spec.md` and
  `docs/<langname>/compiler.md`.

## Contributing

Contributions of new languages, examples, tests, and proofs are welcome. See
[CONTRIBUTING.md](CONTRIBUTING.md) for how to add a language and what the
library expects from a submission.

## License

langlib is distributed under the Apache 2.0 license (see [LICENSE](LICENSE)).
The library only implements languages whose designs are in the public domain
or otherwise freely implementable; all example programs are either original,
in the public domain, or credited to their authors under permissive terms.
