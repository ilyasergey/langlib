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
  written in Lean, under `Langlib/<Langname>/`;
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

Each language ships a runner, for example:

```
lake exe brainfuck Langlib/Examples/brainfuck/hello.b
```

See the per-language READMEs under `Langlib/` for details.

## Languages

The current inhabitants of the library are documented in
[docs/README.md](docs/README.md). The roadmap of languages still to be
implemented lives in [docs/ROADMAP.md](docs/ROADMAP.md), and a survey of
related efforts in [docs/ALTERNATIVES.md](docs/ALTERNATIVES.md).

## Contributing

Contributions of new languages, examples, tests, and proofs are welcome. See
[CONTRIBUTING.md](CONTRIBUTING.md) for how to add a language and what the
library expects from a submission.

## License

langlib is distributed under the Apache 2.0 license (see [LICENSE](LICENSE)).
The library only implements languages whose designs are in the public domain
or otherwise freely implementable; all example programs are either original,
in the public domain, or credited to their authors under permissive terms.
