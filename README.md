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
* where the language can host one — Turing complete, or, like Malbolge,
  merely roomy enough — a **compiler from
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

* [brainfuck](docs/brainfuck/spec.md) (Urban Müller, 1993), eight
  one-character commands on a tape of bytes
* [fractran](docs/fractran/spec.md) (John Conway, 1987), whose programs are
  lists of fractions
* [subleq](docs/subleq/spec.md) (folklore, de-facto spec by
  Oleg Mazonka), one instruction: subtract, branch if the result is ≤ 0
* [whitespace](docs/whitespace/spec.md) (Edwin Brady & Chris Morris, 2003),
  where only spaces, tabs and newlines are code
* [ook](docs/ook/spec.md) (David Morgan-Mar, 2001), brainfuck for orangutans
* [deadfish](docs/deadfish/spec.md) (Jonathan Todd Skinner, 2006), four
  commands, one accumulator, no loops
* [befunge93](docs/befunge93/spec.md) (Chris Pressey, 1993), a stack machine
  whose pointer roams a wrapping grid
* [malbolge](docs/malbolge/spec.md) (Ben Olmstead, 1998), designed to be as
  hard to program as possible
* [thue](docs/thue/spec.md) (John Colagioia, 2000), whose programs are
  string-rewriting rules
* [piet](docs/piet/spec.md) (David Morgan-Mar, 2002), whose programs are
  abstract paintings
* [brainloller](docs/brainloller/spec.md) (Lode Vandevenne, 2005),
  brainfuck encoded in pixels
* [malbolge-unshackled](docs/malbolge-unshackled/spec.md) (Ørjan Johansen,
  2007), Malbolge with the memory bound taken out, which is what makes it
  Turing complete
* [unlambda](docs/unlambda/spec.md) (David Madore, 1999), a functional
  language with no variables and no lambdas
* [velato](docs/velato/spec.md) (Daniel Temkin, 2009), whose programs are
  MIDI files: the pitches and their order are the code
* [ski](docs/ski/spec.md) (Schönfinkel 1924, Curry 1930), not an esolang
  but the combinator calculus underneath Unlambda, and the other half of
  the library's functional route to universality
* [Turpentine](docs/turpentine/spec.md): the library's own human-readable
  front end, named for what dissolves a Turing tarpit

## Current status

| Language | Turing-complete (TC) | TC claim mechanised | Turpentine compiler |
|----------|--------------------------|------------------------------|---------------------|
| [brainfuck](docs/brainfuck/spec.md) | yes | **[yes](docs/brainfuck/computability.md)** | [derived](Langlib/Languages/Turpentine/Compile/Derived.lean#L103) (certified), and [bespoke](docs/brainfuck/compiler.md) (trusted) |
| [whitespace](docs/whitespace/spec.md) | yes | **[yes](docs/whitespace/computability.md)** | [derived](Langlib/Languages/Turpentine/Compile/Derived.lean#L95) (certified), and [bespoke](docs/whitespace/compiler.md) ([certified on a fragment, behaviourally](docs/whitespace/compiler.md)) |
| [subleq](docs/subleq/spec.md) | yes | **[yes](docs/subleq/computability.md)** | [derived](Langlib/Languages/Turpentine/Compile/Derived.lean#L99) (certified), and [bespoke](docs/subleq/compiler.md) ([certified on a fragment](docs/subleq/compiler.md)) |
| [fractran](docs/fractran/spec.md) | yes | **[yes](docs/fractran/computability.md)** | [derived](Langlib/Languages/Turpentine/Compile/Derived.lean#L108) (certified), and [bespoke](docs/fractran/compiler.md) (trusted) |
| [piet](docs/piet/spec.md) | yes | **[yes](docs/piet/computability.md)** | [derived](Langlib/Languages/Turpentine/Compile/Derived.lean#L120) (certified), and [bespoke](docs/piet/compiler.md) (trusted) |
| [thue](docs/thue/spec.md) | yes | **[yes](docs/thue/computability.md)** | [derived](Langlib/Languages/Turpentine/Compile/Derived.lean#L114) (certified); [bespoke planned](docs/thue/compiler.md) |
| [ook](docs/ook/spec.md) | yes, via brainfuck | **[yes](docs/ook/computability.md)** | [derived](Langlib/Languages/Turpentine/Compile/Derived.lean#L126) (certified), and [bespoke](docs/ook/compiler.md) (trusted) |
| [brainloller](docs/brainloller/spec.md) | yes, via brainfuck | **[yes](docs/brainloller/computability.md)**, bar the [pixel walk](docs/brainloller/computability.md) | [derived](Langlib/Languages/Turpentine/Compile/Derived.lean#L131) (certified), and [bespoke](docs/brainloller/compiler.md) (trusted) |
| [befunge93](docs/befunge93/spec.md) | [no with byte cells, yes with ours](docs/befunge93/spec.md#computational-class-and-why-our-deviations-matter) | **[yes](docs/befunge93/computability.md)**, for the byte core | [none: 2000 cells](docs/befunge93/compiler.md) |
| [malbolge](docs/malbolge/spec.md) | no, 59049 words | **[yes](docs/malbolge/computability.md)** | [bespoke](docs/malbolge/compiler.md) (trusted, input-free programs whose output fits); no derived one ever — not Turing complete |
| [deadfish](docs/deadfish/spec.md) | no, every program halts | **[yes](docs/deadfish/computability.md)** | [planned, output only](docs/deadfish/compiler.md) |
| [malbolge-unshackled](docs/malbolge-unshackled/spec.md) | yes | [open](docs/malbolge-unshackled/computability.md) | [bespoke](docs/malbolge-unshackled/compiler.md) (trusted, input-free fragment); no derived one while the TC claim is open |
| [unlambda](docs/unlambda/spec.md) | yes | **[yes](docs/unlambda/computability.md)** | [derived](Langlib/Languages/Turpentine/Compile/Derived.lean#L137) (certified), and [bespoke](docs/unlambda/compiler.md) (trusted) |
| [ski](docs/ski/spec.md) | yes | **[yes](docs/ski/computability.md)** | [derived](Langlib/Languages/Turpentine/Compile/Derived.lean#L144) (certified); [bespoke: compile to unlambda instead](docs/ski/compiler.md) |
| [velato](docs/velato/spec.md) | [yes, with unbounded ints](docs/velato/spec.md#computational-class) | **[yes](docs/velato/computability.md)** | [derived](Langlib/Languages/Turpentine/Compile/Derived.lean#L158) (certified), and [bespoke](docs/velato/compiler.md) ([certified on a fragment, behaviourally, input included](docs/velato/compiler.md)) |
| [Turpentine](docs/turpentine/spec.md) | yes | open | [(it is the source)](docs/turpentine/spec.md) |


* **Turing-complete (TC)** states the computational-class claim;
  **TC claim mechanised** says whether it has been proved here. Its links
  lead to the language's `computability.md`; **open** means no proof yet.
* **Derived** compilers come from completeness proofs and are certified.
  They accept an I/O-free fragment whose result is stored in `answer`;
  their generated programs are large.
* **Bespoke** compilers are hand-written for each target, with compact output
  and broader language support. Their links lead to `compiler.md`, which
  describes the supported fragment, implementation and proofs.
* **Trusted** means tested but unproved. **Certified on a fragment** means
  correctness is proved for part of the accepted language.
  **Behaviourally** additionally means preserving completed I/O traces;
  **input included** means the proof covers runtime reads too.
* **Planned** means the compiler is not implemented; **none** means no
  backend is planned for that target.

See [the full status matrix](docs/README.md) for per-stage details and
[verified compilers](#verified-compilers) below for the correctness contracts.

## What a language is

One definition carries the whole library: running a program, proving a
compiler correct, and claiming a language is or is not Turing complete are
all stated against it.

**[`ProgLang L`](Langlib/Common/Compilation.lean#L96)** is what every
language here supplies.

```lean
class ProgLang (L : Type) where
  Prog  : Type                              -- abstract syntax
  parse : String → Except String Prog
  run   : Prog → Input → Nat → RunResult    -- program, input, fuel
```

`L` is an empty tag type that *names* the language rather than being its
program type, so `Befunge93` and `BoundedByteBefunge93` can be two
languages with two different answers.
[`Input`](Langlib/Common/Io.lean#L79) and
[`RunResult`](Langlib/Common/Io.lean#L329) are the shared
execution model: a byte stream with a read cursor, and the bytes a run
emitted together with how it ended. The `Nat` is **fuel**, a step budget,
which is what makes `run` a total function even of a program that never
terminates — it returns `outOfFuel` instead of diverging.

**[`LawfulProgLang L`](Langlib/Common/Compilation.lean#L125)** requires
that a completed run return the same result with any larger fuel budget.
This keeps fuel a step budget: once a correctness proof establishes a
result, every sufficiently large run produces it. All language instances
satisfy this law, which compiler certificates and `TuringComplete` require.
Both classes live in
[`Langlib/Common/Compilation.lean`](Langlib/Common/Compilation.lean).

## Computability

Esoteric-language folklore is full of claims nobody has checked. Every
language here gets a claim about its computational class and a
machine-checked proof of it. Per-language status is in the
[status matrix](docs/README.md), with detailed
[computability accounts in each language’s documentation](docs/README.md#computability-accounts).
Every result is audited by
[`scripts/axioms.lean`](scripts/axioms.lean), because a proof resting on
`sorry` type-checks exactly like a real one.

### The yardstick: the URM

An **unlimited register machine** (URM), as Shepherdson and Sturgis defined
it: countably many registers holding natural numbers, and four instructions
— zero a register, increment it, copy one register to another, and jump to
an instruction when two registers hold the same value. That is enough to
compute every computable function, and small enough that simulating it
inside a toy language is a day's work rather than a career.

LangLib does not define it. It comes from
[cslib](https://github.com/leanprover/cslib), Lean's library of
computer-science formalisations, so the claims are phrased in a vocabulary
other people already use: [`Instr` and `Program`][cslib-defs], the step
relation [`Step`][cslib-step], and [`HaltsWithResult`][cslib-halts], which
says a program run on an input vector halts with a given number in
register 0.

[cslib-defs]: https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Defs.lean#L44
[cslib-step]: https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Execution.lean#L59
[cslib-halts]: https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Execution.lean#L186

[Our additions](Langlib/Computability/Common/URM.lean) are an *executable*
interpreter — [`step`](Langlib/Computability/Common/URM.lean#L61) and
[`run`](Langlib/Computability/Common/URM.lean#L72) — which cslib's relational
semantics deliberately is not, plus the lemmas
([`step_eq_some_iff_Step`](Langlib/Computability/Common/URM.lean#L111),
[`steps_run`](Langlib/Computability/Common/URM.lean#L142),
[`haltsWithResult_of_haltsIn`](Langlib/Computability/Common/URM.lean#L188)) tying
the two together, so differential tests can run a URM program while every
theorem is still stated against cslib's relation.

### The computability claims

These live in
[`Langlib/Common/Computability.lean`](Langlib/Common/Computability.lean),
shared infrastructure rather than per-language files, so a claim means the
same thing for every language.

**[`TuringComplete L`](Langlib/Common/Computability.lean#L115)** packages a
runnable URM compiler and output decoder. It compiles a program together
with its input vector into a closed target computation, run on `Input.empty`.
It requires
answer preservation for halting sources and `.outOfFuel` at every finite
target budget for divergent sources.

All eleven witnesses satisfy both obligations. With interpreter lawfulness,
they give halting/result equivalence, valid outputs, and runtime-error
freedom. See [the proof routes](docs/divergence-preservation.md).
The URM input vector is embedded in the compiled artifact; the completeness
contract has no runtime input encoding parameter. [How input is represented](docs/certified-compilation.md#why-the-derived-contract-is-closed)
explains the derived and streaming cases.
[`computes_of_turingComplete`](Langlib/Common/Computability.lean#L284)
relates the claim to cslib's URM-computable functions.

**[`BoundedStorage L`](Langlib/Common/Computability.lean#L336)** is the
negative claim: a configuration type, a bound on it per program and input,
an injection into `{0, …, bound - 1}`, and two laws saying the machine is
deterministic and that halting depends only on the configuration. From
those, [`halting_decidable`](Langlib/Common/Computability.lean#L495)
follows once and for all — a run that has not halted within `bound` steps
has repeated a configuration and never will. A language with this witness
has no *computable* `TuringComplete` witness: with an effective compiler,
`TuringComplete.halts_iff` would reduce undecidable URM halting to decidable
target halting. This is a meta-theorem rather than a Lean corollary because
the effectiveness of arbitrary Lean functions is not formalized here; see
[the docstring](Langlib/Common/Computability.lean).

**[`BoundedRun L`](Langlib/Common/Computability.lean#L368)** asks for the
same laws only where the pigeonhole argument uses them: at configurations a
run actually reaches. Every `BoundedStorage` gives one. It exists because a
language can have a state *type* that is wide (an unbounded array, an
output that grows, an input cursor whose range depends on the input) while
its reachable states are few, which is exactly Malbolge's situation.

[Befunge-93](docs/befunge93/spec.md) shows why this is worth doing. It is
usually called incomplete because of its 80 by 25 playfield, but the real
argument is that the reference implementation gives it byte-sized cells,
making it a pushdown automaton — a stack machine, strictly weaker than a
Turing machine. Our cells hold unbounded integers, so the language we
implement *is* complete. Same name, two languages, and nobody
noticed until the claim had to be written down precisely enough to prove.

## Verified compilers

Turpentine offers two compilation routes:

* **Bespoke** backends produce compact code and support as much of
  Turpentine as each target can host, including I/O where available.
  They are the default. [Subleq](docs/subleq/compiler.md),
  [Whitespace](docs/whitespace/compiler.md) and [Velato](docs/velato/compiler.md)
  have correctness proofs for specific fragments; the matrix links to
  each backend's documentation.
* **Derived** backends compose the verified
  [Turpentine-to-URM pass](Langlib/Languages/Turpentine/Compile/URM.lean)
  with a target's `TuringComplete` witness. The composition is proved once
  for every target. It produces large programs and accepts an I/O-free
  fragment, so bespoke backends remain useful for practical execution and
  broader source-language support.

`compile` and `exec` accept `--bespoke` or `--tc` and report which scheme
produced the program.

### Two notions of correct

* **[`CertifiedCompilerNoIO`](Langlib/Common/Compilation.lean#L151)**
  preserves the decoded answer of a closed computation. The target runs
  on empty input. This is the derived compilers' contract.
* **[`CertifiedCompiler`](Langlib/Common/Compilation.lean#L329)** also
  preserves completed I/O traces under explicit input and trace encodings.
  It quantifies over runtime input. [Whitespace](docs/whitespace/compiler.md)
  satisfies it for an output-only fragment; [Velato](docs/velato/compiler.md)
  covers reads too, on NUL-free input streams.

Both require **divergence preservation**: a divergent source computation
exhausts every finite target fuel budget, without halting or failing.
[`agree`](Langlib/Common/Compilation.lean#L181) shows that two closed
certificates for one target decode the same answer on computations both
accept.

See [certified compilation](docs/certified-compilation.md) for the pipeline
and fragment boundaries, and [verification](docs/verification.md) for the
full contracts and their relationship.

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

Malbolge Unshackled runs a program nobody wrote: `compiled/primes.mu` is
what the bespoke backend emits for a Turpentine source, checked into the
tree and run here on Unshackled's own interpreter.

```
lake exe malbolge-unshackled --fuel 100000 Langlib/Examples/MalbolgeUnshackled/compiled/primes.mu
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
23
29
```

Velato greets the world. Its source is a MIDI file, or -- as here, so that a
repository can review it -- the same pitches written out as note names.

```
lake exe velato Langlib/Examples/Velato/hello.vel
```

Output:

```
Hello, World!
```

Velato shows what each note was doing, which is how you find out whether the
piece you wrote says what you meant. This is velato.net's own worked
example, and the labels come from the parser rather than from a second guess
at the grammar.

```
lake exe velato --notes Langlib/Examples/Velato/print-h.vel
```

Output:

```
  #  note   role
  1  C4     root
  2  A4     cmd
  3  G4     print
  4  E4     value
  5  F4     char
  6  A4     7
  7  D#4    2
  8  G4     end num
```

Velato engraves a program as sheet music, and will also write it as a MIDI
file or synthesise it to audio; `scripts/velato-audio.sh` plays the result.

```
lake exe velato --sheet /tmp/primes.pdf Langlib/Examples/Velato/primes.vel
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

One target's compiled program is a *picture*. The Piet backend lays the
program out as corridors of colour wired together with white, and emits a
PPM.

```
lake exe turpentine compile --to piet --bespoke -o /tmp/tri.ppm Langlib/Examples/Turpentine/suite/triangle.turp
```

Output:

```
turpentine: wrote 43779 bytes to /tmp/tri.ppm [bespoke, hand-written and unverified]
```

That is an 88 x 42 codel image, and it runs like any other Piet program.

```
lake exe piet /tmp/tri.ppm
```

Output:

```
*
**
***
****
*****
```

Another target has no machine in it at all. The Unlambda backend turns a
program into a *term*: a statement is a function from a state to the next
one, `while` is a fixed point, and the binders come out by bracket
abstraction. A greeting is short enough to read.

```
cat Langlib/Examples/Unlambda/compiled/hello.unl
```

Output (the program starts with three backquotes, so this block is fenced
with four):

````
# compiled by turpentine, bespoke backend to unlambda: 63 builtins.
```s`k``s``s``s``s``s``s``s``s``s``s``s``s``s``s``s``s``s``s``s`k.H`k.e`k.l`k.l`k.o`k.,`k. `k.T`k.u`k.r`k.p`k.e`k.n`k.t`k.i`k.n`k.e`k.!`kri`kii
````

That file is what `turpentine compile --to unlambda` emitted for
`hello.turp`, and it runs on Unlambda's own interpreter.

```
lake exe unlambda Langlib/Examples/Unlambda/compiled/hello.unl
```

Output:

```
Hello, Turpentine!
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
turpentine: the certified compiler accepts only the I/O-free fragment
  (no input or output, no subtraction, and the result in a
  variable named 'answer'); arrays, division and modulo are
  supported, and the message above names what was rejected.
turpentine: retry with --bespoke to compile the whole language.
turpentine: nothing was run
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
* [docs/conformance.md](docs/conformance.md): the conformance suite —
  twenty programs, one expected output each, run on every language that
  can host them, compiled *and* hand-written.
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

## Miscellanea

A survey of related efforts is in [docs/RELATED.md](docs/RELATED.md).

## License

LangLib is distributed under the Apache 2.0 license (see [LICENSE](LICENSE)).
The library only implements languages whose designs are in the public domain
or otherwise freely implementable; all example programs are either original,
in the public domain, or credited to their authors under permissive terms.
