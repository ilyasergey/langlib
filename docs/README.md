# LangLib documentation

Per-language specifications live in `docs/<langname>/spec.md`; compiler notes
(once a Turpentine compiler exists for the language) in `docs/<langname>/compiler.md`.

## Turpentine, and why it is in the table

Most rows below are esoteric languages: someone else's joke, implemented
here with a specification, an interpreter and a computational-class claim.
The last row is different. **Turpentine** is LangLib's own language, a
small readable imperative one, and it is the *source* the others are
compilation targets for. Write a program once in Turpentine and compile it
to brainfuck, whitespace or subleq rather than writing brainfuck by hand.

It appears in the same table because it is held to the same standard: it
has a [spec](turpentine/spec.md), a parser, an interpreter, examples and
tests, and it gets a computational-class claim like everything else. What
differs is the compiler columns, which read "(source)" for it, since a
compiler *from* Turpentine to itself is not a thing.

## The URM

The universal model everything here is measured against: finitely many
registers holding arbitrary naturals, and four instructions (zero,
increment, copy, jump-if-equal). Small enough that simulating it is
tractable, and enough to compute every partial computable function
(Shepherdson and Sturgis, 1963).

We take it from [cslib](https://github.com/leanprover/cslib) rather than
defining our own, so the claims are stated in a vocabulary others already
trust; our [additions](../Langlib/Computability/URM.lean) are only helper
lemmas. A **Turing complete** claim below means the language simulates any
URM program; a compiler **via TC** composes that simulation with the shared
[Turpentine-to-URM pass](../Langlib/Turpentine/Compile/URM.lean).

## Status matrix

The **Runner** column gives each language's executable name. Run a program
with:

```
lake exe <runner> [--fuel N] [--verbose] <file>
```

Input comes from stdin, output goes to stdout, and every runner takes
`--help`. Some add their own flags, documented on the language's spec page.


Legend: `yes` done, `wip` in progress, `-` not started, `n/a` not applicable
(with the reason in the language's spec page).

**TC** is Turing completeness: whether the language can compute
everything a Turing machine can. It gets two columns on purpose, because
the difference between them is the whole point of this library:

* **Turing complete** is the claim: what the literature says, or what our
  own spec page argues, with a link to the argument in every case where
  the answer is anything but a plain yes. It is prose, and prose can be
  wrong. We have already found two claims that were, one about
  [befunge93](befunge93/spec.md) and one about
  [malbolge](malbolge/spec.md).
* **TC proved** is whether a machine-checked theorem exists in this
  repository. The claim is stated in cslib's vocabulary by
  `computes_of_turingComplete`: a complete language computes every
  URM-computable partial function wherever it is defined. `no` means nobody has proved it here yet, whatever the
  literature believes. `yes` links to the theorem.

A `yes` there means a completeness proof exists in this repository: a
compiler from cslib's unlimited register machine into the language, plus a
proof that the compilation simulates, audited by
[scripts/axioms.lean](../scripts/axioms.lean) to confirm it rests on
nothing but Lean's three standard axioms. Most rows read `no`, which is
the honest state: the interpreters and compilers came first, and Stage 8
of [PLAN.md](PLAN.md) is where that column keeps changing. Every language
claimed Turing complete is also a language Turpentine should compile to.

| Language | Spec | Parser | Interpreter | Examples + tests | Runner | Turing complete | TC proved | Bespoke compiler | Bespoke correct | Correct via TC |
|----------|------|--------|-------------|------------------|--------|-----------------|-----------|------------------|-----------------|----------------|
| [brainfuck](brainfuck/spec.md) | yes | yes | yes | yes | `brainfuck` | yes | wip | [yes, scalars](brainfuck/compiler.md) | planned | planned |
| [whitespace](whitespace/spec.md) | yes | yes | yes | yes | `whitespace` | yes | [**yes**](../Langlib/Computability/Whitespace.lean#L1117) | [yes](whitespace/compiler.md) | planned | [**yes**](../Langlib/Computability/Derived.lean#L101) |
| [subleq](subleq/spec.md) | yes | yes | yes | yes | `subleq` | yes | [**yes**](../Langlib/Computability/Subleq.lean#L1201) | [yes](subleq/compiler.md) | planned | [**yes**](../Langlib/Computability/Derived.lean#L105) |
| [befunge93](befunge93/spec.md) | yes | yes | yes | yes | `befunge93` | [depends on value width](befunge93/spec.md#computational-class-and-why-our-deviations-matter) | no | [no](befunge93/compiler.md) | n/a | n/a |
| [malbolge](malbolge/spec.md) | yes | yes | yes | yes | `malbolge` | [no, bounded storage](malbolge/spec.md) | no | [no](malbolge/compiler.md) | n/a | n/a |
| malbolge-unshackled | wip | wip | wip | wip | `malbolge-unshackled` | yes | no | planned | planned | planned |
| [fractran](fractran/spec.md) | yes | yes | yes | yes | `fractran` | yes | no | [planned](fractran/compiler.md) | planned | planned |
| [thue](thue/spec.md) | yes | yes | yes | yes | `thue` | yes | no | [planned](thue/compiler.md) | planned | planned |
| [piet](piet/spec.md) | yes | yes | yes | yes | `piet` | yes | no | [planned](piet/compiler.md) | planned | planned |
| [ook](ook/spec.md) | yes | yes | yes | yes | `ook` | yes (via brainfuck) | no | [planned, free via brainfuck](ook/compiler.md) | planned | planned |
| [brainloller](brainloller/spec.md) | yes | yes | yes | yes | `brainloller` | yes (via brainfuck) | no | [planned, free via brainfuck](brainloller/compiler.md) | planned | planned |
| [deadfish](deadfish/spec.md) | yes | yes | yes | yes | `deadfish` | [no, finite state](deadfish/spec.md) | no | [planned, output-only](deadfish/compiler.md) | planned | n/a |
| unlambda / SKI | wip | wip | wip | wip | `unlambda` | yes | no | planned | planned | planned |
| [Turpentine](turpentine/spec.md) (front end) | yes | yes | yes | yes | `turpentine` | yes | no | (source) | (source) | (source) |

When a proof lands, its `no` becomes a `yes` linking to the theorem in
`computability.md`, and the claim in the known column stops being the last
word on the subject.

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

The three columns follow from that.

* **Bespoke compiler**: whether a hand-written backend exists, and for
  what fragment.
* **Bespoke correct**: whether *that* backend has a machine-checked
  correctness theorem. Real per-language proof work.
* **Correct via TC**: whether the derived compiler exists for this
  language. A `yes` links to that language's compiler, and *the correctness
  theorem is its `correct` field*, since a `TurpentineCompiler` bundles the
  compiler with its proof.

  The general theorem is
  [`derived`](../Langlib/Computability/Derived.lean#L83): given any
  `TuringComplete L` it returns a `TurpentineCompiler L`, proved once for
  an arbitrary target. Per-language instances are one line each, for
  example
  [`derivedWhitespace`](../Langlib/Computability/Derived.lean#L101) and
  [`derivedSubleq`](../Langlib/Computability/Derived.lean#L105). It rests
  on
  [`compileToURM_correct`](../Langlib/Turpentine/Compile/URM.lean#L2075)
  for the shared Turpentine-to-URM pass, and
  [`agree`](../Langlib/Computability/Derived.lean#L115) says any two
  verified compilers for one target produce the same answers.

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
