# LangLib documentation

## Status matrix

| Language | Spec | Parser | Interpreter | Examples + tests | Runner | Turing complete | TC proved / disproved | Correct via TC | Hosts full Turpentine | Bespoke compiler | Bespoke correct |
| ---------- | ------ | -------- | ------------- | ------------------ | -------- | ----------------- | ----------- | ---------------- | ----------------------- | ------------------ | ----------------- |
| [brainfuck](brainfuck/spec.md) | yes | yes | yes | yes | `brainfuck` | yes | [**yes**](../Langlib/Computability/Brainfuck.lean#L2888) | [**yes**](../Langlib/Languages/Turpentine/Compile/Derived.lean#L120) | yes | [yes](../Langlib/Languages/Turpentine/Compile/Brainfuck.lean#L1317), [notes](brainfuck/compiler.md) | wip |
| [whitespace](whitespace/spec.md) | yes | yes | yes | yes | `whitespace` | yes | [**yes**](../Langlib/Computability/Whitespace.lean#L1117) | [**yes**](../Langlib/Languages/Turpentine/Compile/Derived.lean#L112) | yes | [yes](../Langlib/Languages/Turpentine/Compile/Whitespace.lean#L530), [notes](whitespace/compiler.md) | [**yes**, scalar fragment](../Langlib/Computability/BespokeWhitespace.lean#L3247) |
| [subleq](subleq/spec.md) | yes | yes | yes | yes | `subleq` | yes | [**yes**](../Langlib/Computability/Subleq.lean#L1201) | [**yes**](../Langlib/Languages/Turpentine/Compile/Derived.lean#L116) | yes | [yes](../Langlib/Languages/Turpentine/Compile/Subleq.lean#L1125), [notes](subleq/compiler.md) | [**yes**, two shapes](../Langlib/Computability/BespokeSubleq.lean#L630) |
| [befunge93](befunge93/spec.md) | yes | yes | yes | yes | `befunge93` | [depends on value width](befunge93/spec.md#computational-class-and-why-our-deviations-matter) | [yes, byte core](../Langlib/Computability/Befunge93.lean#L326) | n/a | no, 2000 code cells | [no](befunge93/compiler.md) | n/a |
| [malbolge](malbolge/spec.md) | yes | yes | yes | yes | `malbolge` | [yes, bounded storage](malbolge/spec.md) | [**no**, halting decidable](../Langlib/Computability/Malbolge.lean#L743) | n/a | no, bounded storage | [yes](malbolge/compiler.md) | n/a |
| [malbolge-unshackled](malbolge-unshackled/spec.md) | yes | yes | yes | yes | `malbolge-unshackled` | yes | open | [planned](malbolge-unshackled/compiler.md) | expected yes | [planned](malbolge-unshackled/compiler.md) | [planned](malbolge-unshackled/compiler.md) |
| [fractran](fractran/spec.md) | yes | yes | yes | yes | `fractran` | yes | [**yes**](../Langlib/Computability/Fractran.lean#L4471) | [**yes**](../Langlib/Languages/Turpentine/Compile/Derived.lean#L125) | no I/O at all | [planned](fractran/compiler.md) | [planned](fractran/compiler.md) |
| [thue](thue/spec.md) | yes | yes | yes | yes | `thue` | yes | [**yes**](../Langlib/Computability/Thue.lean#L4024) | [**yes**](../Langlib/Languages/Turpentine/Compile/Derived.lean#L131) | expected, unary output | [planned](thue/compiler.md) | [planned](thue/compiler.md) |
| [piet](piet/spec.md) | yes | yes | yes | yes | `piet` | yes | [**yes**](../Langlib/Computability/Piet.lean#L3992) | [**yes**](../Langlib/Languages/Turpentine/Compile/Derived.lean#L137) | expected yes | [planned](piet/compiler.md) | [planned](piet/compiler.md) |
| [ook](ook/spec.md) | yes | yes | yes | yes | `ook` | yes (via brainfuck) | [**yes**](../Langlib/Computability/Ook.lean#L540) | [**yes**](../Langlib/Languages/Turpentine/Compile/Derived.lean#L143) | yes, via brainfuck | [yes](../Langlib/Languages/Turpentine/Compile/Ook.lean#L49), [notes](ook/compiler.md) | [planned](ook/compiler.md) |
| [brainloller](brainloller/spec.md) | yes | yes | yes | yes | `brainloller` | yes (via brainfuck) | [**yes**](../Langlib/Computability/Brainloller.lean#L329), bar the [pixel walk](brainloller/compiler.md) | [**yes**](../Langlib/Languages/Turpentine/Compile/Derived.lean#L148) | yes, via brainfuck | [yes](../Langlib/Languages/Turpentine/Compile/Brainloller.lean#L57), [notes](brainloller/compiler.md) | [planned](brainloller/compiler.md) |
| [deadfish](deadfish/spec.md) | yes | yes | yes | yes | `deadfish` | [yes, every program halts](deadfish/spec.md) | [**no**, halting decidable](../Langlib/Computability/Deadfish.lean#L89) | n/a | no, output only | [planned, output-only](deadfish/compiler.md) | [planned](deadfish/compiler.md) |
| [unlambda](unlambda/spec.md) | yes | yes | yes | yes | `unlambda` | yes | open | [planned](unlambda/compiler.md) | expected yes | [planned](unlambda/compiler.md) | [planned](unlambda/compiler.md) |
| [ski](ski/spec.md) | yes | yes | yes | yes | `ski` | yes | open | n/a, no output instruction | no, no I/O | [no](ski/compiler.md) | n/a |
| [Turpentine](turpentine/spec.md) (front end) | yes | yes | yes | yes | `turpentine` | yes | open | (source) | (source) | (source) | (source) |
| [URM](#the-urm) (yardstick) | [here](#the-urm) | n/a | [yes](../Langlib/Computability/URM.lean) | yes | n/a | yes | (yardstick) | (the route itself) | no I/O at all | [yes, certified fragment](../Langlib/Languages/Turpentine/Compile/URM.lean) | [**yes**](../Langlib/Languages/Turpentine/Compile/URM.lean#L3985) |

## Reading the table

Legend: `yes` done, `wip` in progress, `-` not started, `n/a` not
applicable, and, in the completeness column only, `open` for a question
nobody has proven here either way. Per-language specifications live in
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
[Turpentine-to-URM pass](../Langlib/Languages/Turpentine/Compile/URM.lean).

The URM has a row of its own because it is a compilation target like the
others, and the one whose compiler is already verified. Its cells read
oddly on purpose:

* **Spec** and **Runner**: cslib defines the machine and this section
  summarises it, so there is no `docs/urm/spec.md`; there is no `lake exe
  urm` either, since the URM is reached through the compiler rather than
  run from the command line.
* **Parser**: `n/a`. URM programs are lists of four constructors, with no
  concrete syntax to parse.
* **TC proved / disproved**: `(yardstick)`. Every other proof in the table is a
  simulation *of* this machine, so proving it complete against itself would
  be circular; its universality is Shepherdson and Sturgis's theorem, and
  we take it as the definition of the standard.
* **Bespoke correct**: `yes`. The Turpentine-to-URM pass is hand-written
  for this target and
  [proved correct](../Langlib/Languages/Turpentine/Compile/URM.lean#L3985), which is
  precisely what makes every derived compiler correct. It was the only
  `yes` in that column until subleq's landed.
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
stronger theorem of
[certified-compilation.md](certified-compilation.md) section 1.2.

### Completeness: the claim, and the verdict

**TC** is Turing completeness: whether the language can compute everything
a Turing machine can. It gets two columns on purpose, because the gap
between what is said about these languages and what has been checked is the
whole point of this library.

* **Turing complete** is the claim: what the literature or our spec page
  argues, linked whenever the answer is not a plain yes. Prose can be
  wrong, and two of ours were: [befunge93](befunge93/spec.md) and
  [malbolge](malbolge/spec.md).
* **TC proved / disproved** is whether a machine-checked theorem settles it
  here, and *which way it came out*, because a proof that a language
  *cannot* compute everything is as much a result as a proof that it can.
  Note that this differs from the summary table in
  [README.md](../README.md), whose narrower `TC proven here` column asks
  only whether the question is settled and so reads `yes` for a disproof
  too; here `yes` and `no` name the answer.
  Every entry is audited by
  [scripts/axioms.lean](../scripts/axioms.lean).
  * `yes` links to a simulation: a compiler from the URM into the language,
    and the proof that it runs any URM program faithfully.
  * `no` links to a result a complete language could not have: a decided
    halting problem. The three get there differently.
    [Deadfish](deadfish/spec.md) halts on `length + 1` units of fuel for
    *every* program, which decides halting directly, and it is also the
    language that provably has *no* `BoundedStorage` witness, since its
    runs grow with the program. The bounded byte
    [befunge93](befunge93/spec.md) core has finitely many configurations by
    construction, packaged as a `BoundedStorage`, so a run that has not
    halted by the bound never will.
    [Malbolge](computability-malbolge.md) is the hard one, because its
    state type is wide (an unbounded array, an unbounded output, a cursor
    whose range depends on the input) while its *reachable* states are
    few: the proof carries an invariant through every instruction, drops
    the output that no instruction reads, and shows the 59049-word control
    determines the run. Its witness is a `BoundedRun`, the reachable-only
    form of `BoundedStorage`.
  * `wip` is a proof under way with the load-bearing step still missing.
    [Fractran](computability-fractran.md) has a runnable URM-to-FRACTRAN
    compiler and its prime-exponent arithmetic proved, but no whole-program
    simulation; [piet](computability-piet.md) compiles straight-line URM
    programs and still owes image-level control flow, which is where
    backward jumps live.
  * `open` means nobody here has proven it in either direction, whatever
    the literature believes. The claims themselves are in the languages'
    spec pages; the roadmap for closing them is
    [PLAN.md](PLAN.md) Stage 8, and the reusable brief for doing one is
    [agent-brief-completeness.md](agent-brief-completeness.md).

Two cautions on the negative side. First, a `no` is a *bound*, not a term
of type `¬ TuringComplete L`: the library states incompleteness by
exhibiting the finite state space and deciding halting, which is the usable
form and the one `Langlib/Common/Computability.lean` supports, and no
negated completeness statement is claimed anywhere. Second, read the
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
the strongest check on it.

Neither replaces the other, and three facts keep it that way.

* **The register machine cannot interleave.** It takes its input before it
  runs and yields one number at halt, so a program that reads and writes in
  turn cannot be compiled that way at all. `cat.turp` has no certified
  version and never will; `cat-tc.turp` exists only to say so. This is a
  property of the model, not an unfinished feature.
* **The output is not of comparable size.** `answer := 3` through the
  certified route becomes 64 kilobytes of brainfuck that runs for billions
  of steps, because arithmetic turns into unary counting on a byte tape.
  The bespoke backend compiles the same thing into something that
  finishes. Neither compiler is wrong; they are answering different
  questions.
* **The fragment is real but partial.** Initialisers, `&&`, `||`, `/` and
  `%` have landed. Subtraction and arrays have not, and subtraction proved
  harder than planned: the recommended `Nat`-valued reference semantics
  bridges the wrong way, since `answer := (2 - 5) + 10` halts with `7` in
  the reference and has no `Nat` run at all. See
  [certified-compilation.md](certified-compilation.md) section 2.4.

The honest summary is that a proof buys certainty about a fragment, and a
hand-written compiler buys a program you can actually run. The library
wants both, and the `agree` theorem is what stops them drifting apart. Both
are inhabitants of a single `TurpentineCompiler` interface, so a language
with both gets `agree` for free: on every program both accept, the two
provably decode the same answer. Not the same *behaviour* — that is a
stronger claim, and the interface for it is
[`IOCertifiedCompiler`](../Langlib/Common/Compilation.lean#L212), which
nothing inhabits yet.

The three columns follow from that, in the order the table puts them.

* **Correct via TC**: whether the derived compiler exists for this
  language. It compiles a *fragment* of Turpentine, not the whole
  language: no I/O, no subtraction, and the result in a variable named
  `answer`. Division, modulo, `&&`, `||`, initialisers and now arrays
  (declarations, `a[i]` on both sides, and `len`) are in, and the fragment
  is still being widened (see
  [certified-compilation.md](certified-compilation.md) sections 2.3 and 2.4);
  the `-tc` examples in `Langlib/Examples/Turpentine/` are written against
  it, and eleven of the twelve compile today, `sort-tc` being the one that
  still needs subtraction. A `yes` links to that language's compiler, and *the correctness
  theorem is its `correct` field*, since a `TurpentineCompiler` bundles the
  compiler with its proof.

  The general theorem is
  [`derived`](../Langlib/Languages/Turpentine/Compile/Derived.lean#L94): given any
  `TuringComplete L` it returns a `TurpentineCompiler L`, proved once for
  an arbitrary target. Per-language instances are one line each, for
  example
  [`derivedWhitespace`](../Langlib/Languages/Turpentine/Compile/Derived.lean#L112),
  [`derivedSubleq`](../Langlib/Languages/Turpentine/Compile/Derived.lean#L116),
  [`derivedBrainfuck`](../Langlib/Languages/Turpentine/Compile/Derived.lean#L120),
  [`derivedFractran`](../Langlib/Languages/Turpentine/Compile/Derived.lean#L125),
  [`derivedThue`](../Langlib/Languages/Turpentine/Compile/Derived.lean#L131) and
  [`derivedPiet`](../Langlib/Languages/Turpentine/Compile/Derived.lean#L137). It rests
  on
  [`compileToURM_correct`](../Langlib/Languages/Turpentine/Compile/URM.lean#L3985)
  for the shared Turpentine-to-URM pass, and
  [`agree`](../Langlib/Languages/Turpentine/Compile/Derived.lean#L159) says any two
  verified compilers for one target produce the same answers.

  A `TurpentineCompiler` is
  [`CertifiedCompiler`](../Langlib/Common/Compilation.lean#L96) — the
  library's generic notion of correct compilation, in the source, the
  answer type and the target — at Turpentine's own specification. Answers,
  not behaviour: the stronger
  [`IOCertifiedCompiler`](../Langlib/Common/Compilation.lean#L212) also
  demands the compiled program reproduce the source's trace of I/O events,
  and [implies](../Langlib/Common/Compilation.lean#L253) this column when
  it lands. Nothing inhabits it yet.

* **Bespoke compiler**: whether a hand-written backend exists, and for
  what fragment.
* **Bespoke correct**: whether *that* backend has a machine-checked
  correctness theorem. Real per-language proof work, and the eventual
  statement is harder than the derived route's, because a bespoke backend
  compiles the I/O-bearing language (see
  [certified-compilation.md](certified-compilation.md) section 1.2).

  The first one has landed:
  [`bespokeSubleq`](../Langlib/Computability/BespokeSubleq.lean#L630) is a
  second `TurpentineCompiler SubleqLang` beside the derived one, so
  [`agree`](../Langlib/Languages/Turpentine/Compile/Derived.lean#L159) applies and "the
  derived compiler is an oracle for the hand-written one" is a corollary
  rather than a testing practice. Its fragment is two program shapes, which
  is small, and honestly so: `docs/subleq/compiler.md` lists what is
  refused.
  [`bespokeWhitespace`](../Langlib/Computability/BespokeWhitespace.lean#L3247)
  followed, over a much larger fragment: scalar `int`/`bool`, the whole
  expression language including subtraction and negative literals, `if`,
  `while` and `assert`, leaving out `/`, `%`, arrays and I/O. That fragment
  is *incomparable* with the certified URM one, since a register holds a
  `Nat` and cannot subtract, so the two compilers check each other only on
  the intersection.

  **The theorems that exist today do not reach that yet, and the gap is
  I/O.** Both routes are proved against one specification,
  [`TurpentineHaltsWith`](../Langlib/Languages/Turpentine/Compile/URM.lean), which
  fixes the source's input to the empty stream and observes only the final
  value of `answer`. `TurpentineCompiler.correct` then asks that the
  compiled program's output *decode* to that number, so output bytes carry
  a single answer rather than being observed as themselves, and input is
  not related at all. A bespoke proof is therefore currently harder only
  in compiling a real backend instead of a simulation, not in what it
  observes.

  [verification.md](verification.md), the Stage 6 design, prescribes the
  stronger statement: observable behaviour is the byte stream plus the
  exit, over a supplied input. Reaching it means generalising the
  interface, since `encodeInput` is a constant field today and would have
  to become a function of the supplied stream. It cannot be done inside
  the shared structure alone, because a derived compiler could never
  satisfy it: the URM it routes through has no I/O at all, which is what
  the **Hosts full Turpentine** column records for the URM row.

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
`Langlib/Languages/Turpentine/`), examples in `Langlib/Examples/<Langname>/`, golden tests
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
