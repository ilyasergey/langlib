# LangLib: Esoteric Programming Languages, Formally

An open-source library of the semantics of esoteric and fun programming
languages, written in [Lean 4](https://lean-lang.org/).

Esoteric languages are not meant for realistic software. They exist to make
a point, to win a bet, to parody a committee, or simply to be difficult.
Over the last fifty years they have accumulated into a large body of design
knowledge: single-instruction machines, programs that are string-rewriting
rules, programs laid out on a grid that wraps at every edge, programs that
encrypt themselves as they run. This knowledge is scattered across personal
pages, wikis, and long-dead FTP servers, and a good deal of it is folklore:
claims repeated confidently and checked by nobody.

This project archives that knowledge in a form that cannot rot. Every
language gets a written specification, an executable reference semantics,
and machine-checked answers to the questions people actually argue about,
starting with what each language can compute. On top of that sits a
compiler from a language a human would willingly write in, whose
correctness is proved rather than tested.

For each language, LangLib provides:

* a **specification** in `docs/<langname>/`, summarising the language's
  history, semantics, and quirks, with credits to its authors;
* a **parser**, a **reference interpreter**, and a **standalone runner**
  written in Lean, under `Langlib/Languages/<Langname>/`;
* **examples** you can run for fun, and a **test suite**, including
  differential tests against non-Lean reference implementations where
  available;
* a **computational-class result**: a claim that the language is or is not
  Turing complete, and a machine-checked proof of it;
* if the language is Turing complete, a **compiler from
  [Turpentine](docs/turpentine/spec.md)** (`.turp`), the small readable
  imperative language that sits on top of the collection. It is named for
  the solvent: a [Turing tarpit](https://en.wikipedia.org/wiki/Turing_tarpit)
  is a language where everything is possible and nothing is easy, and
  turpentine dissolves tar. Two compilation schemes are possible, one
  hand-written and one derived from the completeness proof, and the
  library keeps both.

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
* [malbolge-unshackled](docs/malbolge-unshackled/spec.md) (Ørjan Johansen,
  2007), Malbolge with the memory bound taken out, which is what makes it
  Turing complete
* [unlambda](docs/unlambda/spec.md) (David Madore, 1999), a functional
  language with no variables and no lambdas
* [ski](docs/ski/spec.md) (Schönfinkel 1924, Curry 1930), not an esolang
  but the calculus Unlambda's completeness argument goes through
* [Turpentine](docs/turpentine/spec.md): the library's own human-readable
  front end, named for what dissolves a Turing tarpit

The roadmap of languages still to be implemented lives in
[docs/ROADMAP.md](docs/ROADMAP.md), and a survey of related efforts in
[docs/RELATED.md](docs/RELATED.md).

Where each one stands. The two middle columns answer different questions.
**Turing-complete (TC)** is the answer itself, as the literature or our own
spec page gives it. **TC claim mechanised** is whether that answer is backed
by a machine-checked theorem in this repository, and links it.

So `yes` in the second column means settled, whichever way the first column
came out: brainfuck is proved complete, malbolge is proved *not* complete
by way of a decided halting problem, and both are equally results. The
column never reads `no`, because no question here has been attempted and
lost; the unsettled ones say `open`, or `in progress` where the foundations
have landed and one step remains.

The last column names the Turpentine compilers a target has and links each
to its source. A **derived** one comes out of that language's completeness
proof, so it is *(certified)* already, but it does not support I/O: it
routes everything through a register machine, which has no way to read or
write, so the program takes no input and leaves its result in `answer`.
Its output is also enormous. A **bespoke** one is hand-written for that
target: it emits compact, readable code and supports the whole language.
*(trusted)* means tested rather than proved; *(certified on a fragment)*
means a correctness theorem covers part of what the compiler accepts, and
links it. Whitespace and subleq have one, over fragments the compiler
states as data by refusing everything outside them.
[Verified compilers](#verified-compilers) below explains why the library
keeps both kinds.

| Language | Turing-complete (TC) | TC claim mechanised | Turpentine compiler |
|----------|--------------------------|------------------------------|---------------------|
| [brainfuck](docs/brainfuck/spec.md) | yes | **[yes](Langlib/Computability/Brainfuck.lean#L2888)** | [derived](Langlib/Languages/Turpentine/Compile/Derived.lean#L120) (certified), and [bespoke](Langlib/Languages/Turpentine/Compile/Brainfuck.lean#L1317) (trusted) |
| [whitespace](docs/whitespace/spec.md) | yes | **[yes](Langlib/Computability/Whitespace.lean#L1117)** | [derived](Langlib/Languages/Turpentine/Compile/Derived.lean#L112) (certified), and [bespoke](Langlib/Languages/Turpentine/Compile/Whitespace.lean#L530) ([certified on a fragment](Langlib/Computability/BespokeWhitespace.lean#L3247)) |
| [subleq](docs/subleq/spec.md) | yes | **[yes](Langlib/Computability/Subleq.lean#L1201)** | [derived](Langlib/Languages/Turpentine/Compile/Derived.lean#L116) (certified), and [bespoke](Langlib/Languages/Turpentine/Compile/Subleq.lean#L1125) ([certified on a fragment](Langlib/Computability/BespokeSubleq.lean#L630)) |
| [fractran](docs/fractran/spec.md) | yes | **[yes](Langlib/Computability/Fractran.lean#L4471)** | [derived](Langlib/Languages/Turpentine/Compile/Derived.lean#L125) (certified); [bespoke planned](docs/fractran/compiler.md) |
| [piet](docs/piet/spec.md) | yes | **[yes](Langlib/Computability/Piet.lean#L3992)** | [derived](Langlib/Languages/Turpentine/Compile/Derived.lean#L137) (certified); [bespoke planned](docs/piet/compiler.md) |
| [thue](docs/thue/spec.md) | yes | **[yes](Langlib/Computability/Thue.lean#L4024)** | [derived](Langlib/Languages/Turpentine/Compile/Derived.lean#L131) (certified); [bespoke planned](docs/thue/compiler.md) |
| [ook](docs/ook/spec.md) | yes, via brainfuck | **[yes](Langlib/Computability/Ook.lean#L540)** | [derived](Langlib/Languages/Turpentine/Compile/Derived.lean#L143) (certified), and [bespoke](Langlib/Languages/Turpentine/Compile/Ook.lean#L49) (trusted) |
| [brainloller](docs/brainloller/spec.md) | yes, via brainfuck | **[yes](Langlib/Computability/Brainloller.lean#L329)**, bar the [pixel walk](docs/brainloller/compiler.md) | [derived](Langlib/Languages/Turpentine/Compile/Derived.lean#L148) (certified), and [bespoke](Langlib/Languages/Turpentine/Compile/Brainloller.lean#L57) (trusted) |
| [befunge93](docs/befunge93/spec.md) | [no with byte cells, yes with ours](docs/befunge93/spec.md#computational-class-and-why-our-deviations-matter) | **[yes](Langlib/Computability/Befunge93.lean#L343)**, for the byte core | [none: 2000 cells](docs/befunge93/compiler.md) |
| [malbolge](docs/malbolge/spec.md) | no, 59049 words | **[yes](Langlib/Computability/Malbolge.lean#L743)** | [none: bounded](docs/malbolge/compiler.md) |
| [deadfish](docs/deadfish/spec.md) | no, every program halts | **[yes](Langlib/Computability/Deadfish.lean#L89)** | [planned, output only](docs/deadfish/compiler.md) |
| [malbolge-unshackled](docs/malbolge-unshackled/spec.md) | yes | open | [planned](docs/malbolge-unshackled/compiler.md) |
| [unlambda](docs/unlambda/spec.md) | yes | open | [planned](docs/unlambda/compiler.md) |
| [ski](docs/ski/spec.md) | yes | open | [none: compile to unlambda](docs/ski/compiler.md) |
| [Turpentine](docs/turpentine/spec.md) | yes | open | [(it is the source)](docs/turpentine/spec.md) |

The full matrix, with per-stage columns and links to every theorem, is in
[docs/README.md](docs/README.md).

## Computability

Esolang folklore is full of claims nobody has checked. Every language here
gets a claim about its computational class and a machine-checked proof of
it. Completeness is proved by compiling a universal machine into the
language; incompleteness by bounding the machine's state space and deciding
its halting problem. Per-language status is in the
[status matrix](docs/README.md), and every result is audited by
[`scripts/axioms.lean`](scripts/axioms.lean), because a proof resting on
`sorry` type-checks exactly like a real one.

### The four definitions everything is stated with

`ProgLang` lives in
[`Common/Compilation.lean`](Langlib/Common/Compilation.lean) with the
compiler-correctness definitions; the other three live in
[`Common/Computability.lean`](Langlib/Common/Computability.lean). Both are
shared infrastructure rather than per-language files, so a claim means the
same thing for every language.

**The URM** is the yardstick, and it comes from
[cslib](https://github.com/leanprover/cslib) rather than being defined here,
so the claims are phrased in a vocabulary others already use. It is
Shepherdson and Sturgis's unlimited register machine: countably many
registers holding natural numbers, and four instructions — zero a register,
increment it, copy one to another, and jump if two are equal. That is
enough to compute every computable function, and it is small enough that
simulating it inside a toy language is a day's work rather than a career.
[Our additions](Langlib/Computability/URM.lean) are an executable
interpreter, which cslib's relational semantics deliberately is not, and
the lemmas tying the two together.

**`ProgLang L`** is what every language in the library supplies: a program
type, a parser, and a pure fuel-based interpreter. `L` is an empty tag type
that names the language, so `BoundedByteBefunge93` and `Befunge93` can be
two languages with two different answers.

**`TuringComplete L`** is the positive claim, and it is a *witness* rather
than a proposition: a compiler from URM programs into `L`, an encoding of
the machine's input, a decoding of its answer, and the proof that a
compiled program halts with the right answer whenever the machine does.
Writing that term down is what "we proved it complete" means here. It also
pays for itself, because a compiler from a register machine is exactly what
a certified Turpentine backend needs (see below).

**`BoundedStorage L`** is the negative claim: a configuration type, a bound
on it per program and input, an injection into `{0, …, bound - 1}`, and two
laws saying the machine is deterministic and that halting depends only on
the configuration. From those, `halting_decidable` derives once and for all
that halting is decidable — a run that has not halted within `bound` steps
has repeated a configuration and never will. A language with this witness
cannot be Turing complete.

**`BoundedRun L`** asks for the same laws only where the pigeonhole
argument uses them: at configurations a run actually reaches. That is the
weaker form, and every `BoundedStorage` gives one. It exists because a
language can have a state *type* that is wide (an unbounded array, an
output that grows, an input cursor whose range depends on the input) while
its reachable states are few, which is exactly Malbolge's situation.

[Befunge-93](docs/befunge93/spec.md) shows why this is worth doing. It is
usually called incomplete because of its 80 by 25 playfield, but the real
argument is that the reference implementation gives it byte-sized cells,
making it a pushdown automaton. Our cells hold unbounded integers, so the
language we implement *is* complete. Same name, two languages, and nobody
noticed until the claim had to be written down precisely enough to prove.

## Verified compilers

A Turpentine program reaches a target two ways, and the library keeps both.

**Bespoke** compilers are hand-written per target. They accept the whole of
Turpentine, produce compact output, and are what
`lake exe turpentine compile --to <lang>` runs today for
[brainfuck](Langlib/Languages/Turpentine/Compile/Brainfuck.lean),
[whitespace](Langlib/Languages/Turpentine/Compile/Whitespace.lean) and
[subleq](Langlib/Languages/Turpentine/Compile/Subleq.lean). None is verified yet;
verifying one is per-language proof work.

**Via the URM**, a compiler costs nothing to write. A `TuringComplete`
witness already contains a verified compiler from a register machine, so
composing it with one shared Turpentine-to-register-machine pass,
[`Compile/URM.lean`](Langlib/Languages/Turpentine/Compile/URM.lean), gives a
correct-by-construction compiler into any language proved complete. The
composition is proved once for an arbitrary target, so a new language costs
one line. The catch is that everything runs through a machine simulation:
the output is enormous, and the fragment is I/O-free.

Both are inhabitants of one `CertifiedCompiler` interface, which pays off
where a target has both: `agree` proves that any two verified compilers for
one target decode the same answer out of every program both accept. Until a
bespoke compiler is verified, the derived one is the strongest available
check on it.

### Two notions of correct

Answer preservation is not behaviour preservation, and the library says
which one it has proved.
[`CertifiedCompiler`](Langlib/Common/Compilation.lean#L96) is the
answer-only statement: the compiled program halts and prints something that
decodes to the number the source computed. That is exactly right for the
derived compilers, whose fragment has no I/O, and much too weak for a
backend that compiles `read` and `print`.
[`IOCertifiedCompiler`](Langlib/Common/Compilation.lean#L212) is the
behavioural one: a run's observable behaviour is the `Trace` of bytes it
consumed and emitted, in order, and the compiled program has to reproduce
the source's trace under an encoding the compiler declares up front, as
well as its answer.
[`toCertified`](Langlib/Common/Compilation.lean#L253) proves the second
implies the first, so upgrading a backend loses none of what was already
proved about it. Nothing is proved behaviourally yet; the candidates and
what each one needs are tabulated in
[certified-compilation.md](docs/certified-compilation.md).

Choose explicitly. `compile` and `exec` each take `--bespoke` or `--tc`,
refuse both at once, and name the scheme they used, so a build log says
which compiler made the artifact.

### Why the bespoke compilers stay

"We proved one, so throw the other away" is the obvious wrong conclusion.

*Some programs cannot go through a register machine at all.* A URM takes
its input before it runs and yields one number when it halts, so nothing
that interleaves reading and writing can be expressed however far the
certified fragment is widened. `cat.turp` will never compile that way.
That is a property of the model rather than a gap in the work.

*The output is not comparable.* Compiling `answer := 3` to brainfuck
through the register machine produces 64 kilobytes and runs in billions of
steps, because arithmetic becomes unary counting on a byte tape. The
bespoke brainfuck backend compiles real programs into something that
finishes.

*The fragment is still narrowing in.* Initialisers, `&&`, `||`, `/` and
`%` have landed; subtraction and arrays have not, and subtraction turned
out to be harder than planned (the obvious `Nat`-valued semantics bridges
the wrong way). Meanwhile the bespoke compilers accept the whole language
today.

*A verified bespoke compiler needs a stronger theorem than the derived one
has.* The certified statement observes a single number on runs that halt,
which is adequate only because that fragment has no I/O. A backend for the
whole language has to preserve a byte stream, consume input, and say what
happens when a program prints and then diverges. That is
[a larger obligation](docs/certified-compilation.md), not the same one at
higher effort.

The pipeline, the diagrams and the theorem that makes the composition work
are in [certified-compilation.md](docs/certified-compilation.md); what
correctness means here, including how `assert` compiles, is in
[verification.md](docs/verification.md); and each target's own decisions
are in `docs/<langname>/compiler.md`.

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

## Running programs

Each language ships a runner named after it. Programs read from stdin and
write to stdout, so pipe or redirect input, and the result is printed to
your terminal. One example per language, with what you should see:

Brainfuck says hello.

```
lake exe brainfuck Langlib/Examples/Brainfuck/hello.b
```

Output:

```
Hello World!
```

Brainfuck reverses a word, reading it from stdin.

```
echo -n stressed | lake exe brainfuck --eof zero Langlib/Examples/Brainfuck/rev.b
```

Output:

```
desserts
```

Erik Bosman's 505-byte brainfuck quine prints itself, so `diff` says nothing.

```
lake exe brainfuck Langlib/Examples/Brainfuck/quine.b | diff - Langlib/Examples/Brainfuck/quine.b
```

Whitespace says hello, using a program made entirely of spaces and tabs.

```
lake exe whitespace Langlib/Examples/Whitespace/hello.ws
```

Output:

```
Hello, World!
```

Ook! says hello, because brainfuck was not quite unreadable enough.

```
lake exe ook Langlib/Examples/Ook/hello.ook
```

Output:

```
Hello World!
```

Deadfish prints the ASCII codes of a greeting, one number per line, since
printing letters is beyond it.

```
lake exe deadfish Langlib/Examples/Deadfish/hello.df
```

Output:

```
72
101
108
...
```

Subleq counts down on a machine with exactly one instruction.

```
lake exe subleq Langlib/Examples/Subleq/countdown.sq
```

Output:

```
9876543210
```

FRACTRAN runs Conway's PRIMEGAME, which prints the primes as exponents of
two. It has no halting condition, so cap it with `--fuel`.

```
lake exe fractran --n 2 --out pow2 --fuel 2000000 Langlib/Examples/Fractran/primegame.ft
```

Output:

```
2
3
5
7
...
```

Piet says hi, using a program that is an abstract painting.

```
lake exe piet Langlib/Examples/Piet/hi.ppm
```

Output:

```
Hi
```

Brainloller runs a brainfuck program encoded as coloured pixels.

```
lake exe brainloller Langlib/Examples/Brainloller/hello.ppm
```

Output:

```
Hello World!
```

Malbolge prints the hello world that a search program found in 2000,
because no human could write one. The capitalisation is not a typo.

```
lake exe malbolge Langlib/Examples/Malbolge/hello.mal
```

Output:

```
HEllO WORld
```

Turpentine, the readable front end, computes an integer square root.

```
echo 17 | lake exe turpentine run Langlib/Examples/Turpentine/isqrt.turp
```

Output:

```
4
```

Turpentine prints the primes up to 20, using the same trial division you would
write in any language.

```
echo 20 | lake exe turpentine run Langlib/Examples/Turpentine/primes.turp
```

Output:

```
2
3
5
7
11
13
17
19
```

### Compiling Turpentine

Turpentine programs can be interpreted, compiled to an esolang, or
compiled and run in one step. Both compilers are available for each
target: `--bespoke` (hand-written, whole language, compact, unverified) and
`--tc` (derived from the target's Turing-completeness proof, correct
by construction, larger, and restricted to an I/O-free fragment). Passing
neither uses the bespoke one; passing both is an error.

Interpret it.

```
echo 17 | lake exe turpentine run Langlib/Examples/Turpentine/isqrt.turp
```

Output:

```
4
```

Compile and run in one step, using the hand-written backend.

```
echo 17 | lake exe turpentine exec --via whitespace --bespoke Langlib/Examples/Turpentine/isqrt.turp
```

Output:

```
4
```

Emit the target program instead, and note that the message says which
compiler produced it.

```
lake exe turpentine compile --to subleq --bespoke -o /tmp/isqrt.sq Langlib/Examples/Turpentine/isqrt.turp
```

Output:

```
turpentine: wrote 22615 bytes to /tmp/isqrt.sq [bespoke, hand-written and unverified]
```

That file is an ordinary subleq program, so run it with subleq's own
runner.

```
echo 17 | lake exe subleq /tmp/isqrt.sq
```

Output:

```
4
```

The certified compiler needs a program in its fragment: no I/O, no
subtraction, and the result left in a variable called `answer`. Arrays are
in, since the dispatch-chain work landed.
`sumsq.turp` is written that way, and sums the squares below 5.

```
lake exe turpentine exec --via whitespace --tc Langlib/Examples/Turpentine/sumsq.turp
```

Output:

```
30
```

Outside that fragment it says which construct is the problem rather than
emitting something it cannot justify.

```
echo 17 | lake exe turpentine exec --via whitespace --tc Langlib/Examples/Turpentine/isqrt.turp
```

Output:

```
turpentine exec: the certified URM fragment needs a variable named 'answer' to hold the answer: a URM has no output, so register 0 at halt is all there is
```

Every mode, including emitting to stdout and what the two schemes cost, is
in [certified-compilation.md](docs/certified-compilation.md).

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

LangLib is distributed under the Apache 2.0 license (see [LICENSE](LICENSE)).
The library only implements languages whose designs are in the public domain
or otherwise freely implementable; all example programs are either original,
in the public domain, or credited to their authors under permissive terms.
