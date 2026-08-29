# LangLib documentation

## Status matrix

| Language | Spec | Parser | Interpreter | Examples + tests | Runner | Turing complete | TC (dis)proved | Correct via TC | Hosts full Turpentine | Bespoke compiler | Bespoke correct |
| ---------- | ------ | -------- | ------------- | ------------------ | -------- | ----------------- | ----------- | ---------------- | ----------------------- | ------------------ | ----------------- |
| [brainfuck](brainfuck/spec.md) | yes | yes | yes | yes | `brainfuck` | yes | [**yes**](../Langlib/Computability/Brainfuck.lean#L2888) | [**yes**](../Langlib/Computability/Derived.lean#L110) | yes | [yes, scalars](brainfuck/compiler.md) | planned |
| [whitespace](whitespace/spec.md) | yes | yes | yes | yes | `whitespace` | yes | [**yes**](../Langlib/Computability/Whitespace.lean#L1117) | [**yes**](../Langlib/Computability/Derived.lean#L102) | yes | [yes](whitespace/compiler.md) | planned |
| [subleq](subleq/spec.md) | yes | yes | yes | yes | `subleq` | yes | [**yes**](../Langlib/Computability/Subleq.lean#L1201) | [**yes**](../Langlib/Computability/Derived.lean#L106) | yes | [yes](subleq/compiler.md) | planned |
| [befunge93](befunge93/spec.md) | yes | yes | yes | yes | `befunge93` | [depends on value width](befunge93/spec.md#computational-class-and-why-our-deviations-matter) | [**no**, byte core](../Langlib/Computability/Befunge93.lean#L326) | n/a | no, 2000 code cells | [no](befunge93/compiler.md) | n/a |
| [malbolge](malbolge/spec.md) | yes | yes | yes | yes | `malbolge` | [no, bounded storage](malbolge/spec.md) | wip; [finite control counted](../Langlib/Computability/Malbolge.lean#L80) | n/a | no, bounded storage | [no](malbolge/compiler.md) | n/a |
| malbolge-unshackled | wip | wip | wip | wip | `malbolge-unshackled` | yes | open | planned | expected yes | planned | planned |
| [fractran](fractran/spec.md) | yes | yes | yes | yes | `fractran` | yes | open | planned | no I/O at all | [planned](fractran/compiler.md) | planned |
| [thue](thue/spec.md) | yes | yes | yes | yes | `thue` | yes | open | planned | expected, unary output | [planned](thue/compiler.md) | planned |
| [piet](piet/spec.md) | yes | yes | yes | yes | `piet` | yes | open | planned | expected yes | [planned](piet/compiler.md) | planned |
| [ook](ook/spec.md) | yes | yes | yes | yes | `ook` | yes (via brainfuck) | open | planned | yes, via brainfuck | [planned, free via brainfuck](ook/compiler.md) | planned |
| [brainloller](brainloller/spec.md) | yes | yes | yes | yes | `brainloller` | yes (via brainfuck) | open | planned | yes, via brainfuck | [planned, free via brainfuck](brainloller/compiler.md) | planned |
| [deadfish](deadfish/spec.md) | yes | yes | yes | yes | `deadfish` | [no, finite state](deadfish/spec.md) | [**no**, halting decidable](../Langlib/Computability/Deadfish.lean#L89) | n/a | no, output only | [planned, output-only](deadfish/compiler.md) | planned |
| unlambda / SKI | wip | wip | wip | wip | `unlambda` | yes | open | planned | expected yes | planned | planned |
| [Turpentine](turpentine/spec.md) (front end) | yes | yes | yes | yes | `turpentine` | yes | open | (source) | (source) | (source) | (source) |
| [URM](#the-urm) (yardstick) | [here](#the-urm) | n/a | [yes](../Langlib/Computability/URM.lean) | yes | n/a | yes | (yardstick) | (the route itself) | no I/O at all | [yes, certified fragment](../Langlib/Turpentine/Compile/URM.lean) | [**yes**](../Langlib/Turpentine/Compile/URM.lean#L2989) |

## Reading the table

Legend: `yes` done, `wip` in progress, `-` not started, `n/a` not
applicable, and, in the completeness column only, `open` for a question
nobody has settled here either way. Per-language specifications live in
`docs/<langname>/spec.md`, and compiler notes, once a Turpentine compiler
exists or is planned for a language, in `docs/<langname>/compiler.md`.

### Hosts full Turpentine

Whether the target can express the whole source language, or something is
structurally missing. This is about the *target*, not about how much work
we have done: `no I/O at all` for fractran is a fact about FRACTRAN, and
no amount of compiler engineering changes it.

A `no` here bounds what any compiler into that language can be. Bounded
storage caps program size (befunge93's 2000 code cells, malbolge's 59049
words); deadfish has no input and no loops, so it takes only straight-line
output; fractran has no I/O, so results come out as a final state to be
factorised rather than printed.

Note that this column and the compiler columns on either side of it answer
different questions. A language can host full Turpentine and still have no compiler
written, and a language whose bespoke compiler accepts everything may
still have only a fragment compiled by the certified route, because that
route is limited by the register machine rather than by the target.

### Running a language

The **Runner** column gives each language's executable name:

```
lake exe <runner> [--fuel N] [--verbose] <file>
```

Input comes from stdin, output goes to stdout, and every runner takes
`--help`. Some add their own flags, documented on the language's spec page.

Turpentine, second from the bottom, is the source language rather than a
target, so its runner also compiles:

```
lake exe turpentine run <file.turp>                          # interpret
lake exe turpentine check <file.turp>                        # type-check only
lake exe turpentine compile --to <lang> [--bespoke|--tc] [-o out] <file.turp>
lake exe turpentine exec --via <lang> [--bespoke|--tc] <file.turp>
```

`exec` compiles in memory and immediately runs the result on that
language's own interpreter, so its output should match `run` exactly.
Worked examples of every mode, with real output, are in
[certified-compilation.md](certified-compilation.md).

### Turpentine, and why it is in the table

Most rows are esoteric languages: someone else's joke, implemented here
with a specification, an interpreter and a computational-class claim. The
last two are not. **Turpentine** is LangLib's own language, a
small readable imperative one, and it is the *source* the others are
compilation targets for. Write a program once in Turpentine and compile it
to brainfuck, whitespace or subleq rather than writing brainfuck by hand.

It appears in the same table because it is held to the same standard: it
has a [spec](turpentine/spec.md), a parser, an interpreter, examples and
tests, and it gets a computational-class claim like everything else. What
differs is the compiler columns, which read "(source)" for it, since a
compiler *from* Turpentine to itself is not a thing.

### The URM

The universal model everything here is measured against: finitely many
registers holding arbitrary naturals, and four instructions (zero,
increment, copy, jump-if-equal). Small enough that simulating it is
tractable, and enough to compute every partial computable function
(Shepherdson and Sturgis, 1963).

We take it from [cslib](https://github.com/leanprover/cslib) rather than
defining our own, so the claims are stated in a vocabulary others already
trust. Our [additions](../Langlib/Computability/URM.lean) are an executable
fuel-driven interpreter, which cslib's relational semantics deliberately is
not, and the lemmas that tie the two together. A **Turing complete** claim
above means the language simulates any URM program; a compiler **via TC**
composes that simulation with the shared
[Turpentine-to-URM pass](../Langlib/Turpentine/Compile/URM.lean).

The URM has a row of its own because it is a compilation target like the
others, and the one whose compiler is already verified. Its cells read
oddly on purpose:

* **Spec** and **Runner**: cslib defines the machine and this section
  summarises it, so there is no `docs/urm/spec.md`; there is no `lake exe
  urm` either, since the URM is reached through the compiler rather than
  run from the command line.
* **Parser**: `n/a`. URM programs are lists of four constructors, with no
  concrete syntax to parse.
* **TC (dis)proved**: `(yardstick)`. Every other proof in the table is a
  simulation *of* this machine, so proving it complete against itself would
  be circular; its universality is Shepherdson and Sturgis's theorem, and
  we take it as the definition of the standard.
* **Bespoke correct**: `yes`, and the only `yes` in that column. The
  Turpentine-to-URM pass is hand-written for this target and
  [proved correct](../Langlib/Turpentine/Compile/URM.lean#L2989), which is
  precisely what makes every derived compiler correct.
* **Correct via TC**: `(the route itself)`. The derived scheme *is* this
  pass composed with a completeness witness, so there is nothing separate
  to derive for the URM.

**And it is not an adequate target.** The URM earns its row as the machine
every proof passes through, not as somewhere to send a program you want to
run. It has no I/O at all: input is a register vector fixed before the run,
output is one natural number in register 0, and neither is a stream, so a
program cannot prompt, echo, or print anything before it halts. A run that
never halts produces nothing to look at, and a run that halts produces a
number that still has to be interpreted by whoever reads it. The whole
`answer` convention, and the I/O-free fragment that follows from it, exists
to work around exactly this.

That is why the certified route is not the end of the story. A verified
compiler *through* the URM inherits the URM's poverty: it can prove a
program computes the right number, and it cannot say anything about a
program that talks to a user. Reaching a target people actually run, with
input and output that arrive in order, needs a hand-written backend and the
stronger theorem sketched in
[certified-compilation.md](certified-compilation.md) section 3b.

### Completeness: the claim, and the verdict

**TC** is Turing completeness: whether the language can compute everything
a Turing machine can. It gets two columns on purpose, because the gap
between what is said about these languages and what has been checked is the
whole point of this library.

* **Turing complete** is the claim: what the literature or our spec page
  argues, linked whenever the answer is not a plain yes. Prose can be
  wrong, and two of ours were: [befunge93](befunge93/spec.md) and
  [malbolge](malbolge/spec.md).
* **TC (dis)proved** is whether a machine-checked theorem settles it, and
  the column says so in either direction, because a proof that a language
  *cannot* compute everything is as much a result as a proof that it can.
  Every entry is audited by
  [scripts/axioms.lean](../scripts/axioms.lean).
  * `yes` links to a simulation: a compiler from the URM into the language,
    and the proof that it runs any URM program faithfully.
  * `no` links to a bound: a theorem about the machine's state space that
    a complete language could not satisfy. [Deadfish](deadfish/spec.md)
    halts on `length + 1` units of fuel for *every* program, so its halting
    problem is decided outright, and the bounded byte
    [befunge93](befunge93/spec.md) core is a finite-state machine with a
    `BoundedStorage` witness, which decides halting the same way.
  * `wip` is a bound that is partly counted. [Malbolge](malbolge/spec.md)'s
    finite control is counted exactly, for each input length, but the
    `BoundedStorage` interface cannot yet package its input-dependent
    cursor, so the language is not through the same gate as the two above.
  * `open` means nobody here has settled it in either direction, whatever
    the literature believes.

Two cautions on the negative side. First, a `no` is a *bound*, not a term
of type `¬ TuringComplete L`: the library states incompleteness by
exhibiting the finite state space and deciding halting, which is the usable
form and the one `Class.lean` supports, and no negated completeness
statement is claimed anywhere. Second, read the
[befunge93](befunge93/spec.md) link narrowly. It is about a deliberately
restricted core with byte cells, a 16-deep stack and no I/O, which is
neither `bef.c` nor the unbounded-integer semantics our interpreter runs;
the *claim* column keeps that language's answer at "depends on value
width" for exactly this reason.

When either kind of theorem lands, the `open` becomes a `yes` or a `no`
linking into `Langlib/Computability/`, and the claim in the column beside
it stops being the last word on the subject.

### Why two kinds of compiler

A Turpentine program can reach a target two ways, and the library keeps
both because neither subsumes the other.

A **bespoke** compiler is written by hand for that target. It accepts the
whole language, produces compact output, and is what
`lake exe turpentine compile --to <lang>` actually runs. It is also
unverified until somebody does the per-language proof work.

A compiler **via TC** costs nothing to write: a Turing-completeness proof
already contains a verified compiler from a register machine, so composing
it with one shared Turpentine-to-register-machine pass yields a
correct-by-construction compiler into any language proved complete (see
[certified-compilation.md](certified-compilation.md)). The catch is that it
runs everything through a machine simulation, so its output is enormous and
its fragment is I/O-free.

So: bespoke compilers are for running programs, derived ones are for
proving things, and until a bespoke compiler is verified the derived one is
the strongest check on it. Both are instances of a single
`TurpentineCompiler` interface, so a language with both gets `agree` for
free: the two provably produce the same observable behaviour on programs
both accept.

The three columns follow from that, in the order the table puts them.

* **Correct via TC**: whether the derived compiler exists for this
  language. It compiles a *fragment* of Turpentine, not the whole
  language: no I/O, no subtraction, no arrays, and the result in a
  variable named `answer`. Division, modulo, `&&`, `||` and initialisers
  are in, and the fragment is still being widened (see
  [certified-compilation.md](certified-compilation.md) sections 4 and 4b);
  the `-tc` examples in `Langlib/Examples/Turpentine/` are written against
  it, and all but the three that need arrays compile today. A `yes` links to that language's compiler, and *the correctness
  theorem is its `correct` field*, since a `TurpentineCompiler` bundles the
  compiler with its proof.

  The general theorem is
  [`derived`](../Langlib/Computability/Derived.lean#L84): given any
  `TuringComplete L` it returns a `TurpentineCompiler L`, proved once for
  an arbitrary target. Per-language instances are one line each, for
  example
  [`derivedWhitespace`](../Langlib/Computability/Derived.lean#L102),
  [`derivedSubleq`](../Langlib/Computability/Derived.lean#L106) and
  [`derivedBrainfuck`](../Langlib/Computability/Derived.lean#L110). It rests
  on
  [`compileToURM_correct`](../Langlib/Turpentine/Compile/URM.lean#L2989)
  for the shared Turpentine-to-URM pass, and
  [`agree`](../Langlib/Computability/Derived.lean#L120) says any two
  verified compilers for one target produce the same answers.

* **Bespoke compiler**: whether a hand-written backend exists, and for
  what fragment.
* **Bespoke correct**: whether *that* backend has a machine-checked
  correctness theorem. Real per-language proof work, and a strictly harder
  statement than the derived route's, because a bespoke backend compiles
  the I/O-bearing language (see
  [certified-compilation.md](certified-compilation.md) section 3b).

`planned` in either correctness column means no theorem exists here yet,
whatever the tests say; when one lands the cell links to it. `n/a` means
there is nothing to prove: either no compiler is planned for that target,
or the language is not Turing complete, so no derived compiler can exist
for it.

Note the pattern in the compiler column: **a language cannot host a full
compiler unless it is Turing complete.** A bounded-storage language can
only ever accept a fragment, bounded by its storage rather than by our
effort, so a backend for one is a demonstration and not a tool. We do not
plan compilers for [malbolge](malbolge/compiler.md) (59049 words for code
and data together) or [befunge93](befunge93/compiler.md) (2000 playfield
cells, shared between code and its only storage); each page explains the
decision. [deadfish](deadfish/compiler.md) is the exception we keep,
because its fragment is a straight line of prints and the joke is worth
the afternoon it costs.

Where the bound is what stops us, the fix is to compile to the unbounded
relative instead: Malbolge Unshackled rather than Malbolge, and
Befunge-98 rather than Befunge-93.

Lean code lives in `Langlib/Languages/<Langname>/` (the front end in
`Langlib/Turpentine/`), examples in `Langlib/Examples/<Langname>/`, golden tests
in `Langlib/Tests/<Langname>.lean`.

Every language has a `docs/<langname>/compiler.md`: for the backends that
exist it describes what was built, and for the rest it is a concrete plan
(or, where we decided against a backend, the argument for that decision). Planned targets and their sequencing live in
`PLAN.md` (Stage 4);
`n/a` entries are explained in the language's spec page.

## Project documents

* [PLAN.md](PLAN.md): the staged workplan (agents: keep it current).
* [PROGRESS.md](PROGRESS.md): dated progress log.
* [TESTING.md](TESTING.md): the two test layers, and what to install for
  differential testing per language.
* [ROADMAP.md](ROADMAP.md): candidate languages and instructions for adding
  one.
* [RELATED.md](RELATED.md): related efforts elsewhere.
* [agent-brief-completeness.md](agent-brief-completeness.md): a reusable
  prompt for proving a language Turing complete and thereby obtaining its
  verified compiler. Copy the block, replace the language name, hand it to
  an agent.
* [certified-compilation.md](certified-compilation.md): the plan for
  verified compilers via the URM, with the dependency graph and the
  argument for keeping the hand-written backends alongside them.
* [verification.md](verification.md): the compiler verification pipeline,
  including the split between derived compilers (correct by construction,
  obtained from a completeness proof) and effective ones (hand-written,
  practical, separately verified).
