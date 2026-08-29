# langlib documentation

Per-language specifications live in `docs/<langname>/spec.md`; compiler notes
(once a Turpentine compiler exists for the language) in `docs/<langname>/compiler.md`.

## Turpentine, and why it is in the table

Most rows below are esoteric languages: someone else's joke, implemented
here with a specification, an interpreter and a computational-class claim.
The last row is different. **Turpentine** is langlib's own language, a
small readable imperative one, and it is the *source* the others are
compilation targets for. Write a program once in Turpentine and compile it
to brainfuck, whitespace or subleq rather than writing brainfuck by hand.

It appears in the same table because it is held to the same standard: it
has a [spec](turpentine/spec.md), a parser, an interpreter, examples and
tests, and it gets a computational-class claim like everything else. What
differs is the compiler columns, which read "(source)" for it, since a
compiler *from* Turpentine to itself is not a thing.

## Status matrix

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

One entry in the proved column now reads `yes`:
[whitespace](../Langlib/Computability/Whitespace.lean) is machine-checked
Turing complete, by compiling cslib's unlimited register machine into it
and proving the compilation simulates. `#print axioms` on the result
reports only `propext`, `Classical.choice` and `Quot.sound`, so nothing is
resting on a `sorry`. The rest still read `no`, which is the honest state:
the interpreters and compilers came first, and Stage 8 of
[PLAN.md](PLAN.md) is where that column keeps changing. Every language
claimed Turing complete is also a language Turpentine should compile to.

| Language | Spec | Parser | Interpreter | Examples + tests | Runner | Turing complete | TC proved | Turpentine compiler | Correctness proved |
|----------|------|--------|-------------|------------------|--------|-----------------|-----------|---------------------|-------------------|
| [brainfuck](brainfuck/spec.md) | yes | yes | yes | yes | `lake exe brainfuck` | yes | no | [bespoke, scalars](brainfuck/compiler.md) | no |
| [whitespace](whitespace/spec.md) | yes | yes | yes | yes | `lake exe whitespace` | yes | [**yes**](../Langlib/Computability/Whitespace.lean#L1117) | [bespoke](whitespace/compiler.md) | no (via TC in progress) |
| [subleq](subleq/spec.md) | yes | yes | yes | yes | `lake exe subleq` | yes | no | [bespoke](subleq/compiler.md) | no |
| [befunge93](befunge93/spec.md) | yes | yes | yes | yes | `lake exe befunge93` | [depends on value width](befunge93/spec.md#computational-class-and-why-our-deviations-matter) | no | [not planned](befunge93/compiler.md) | n/a |
| [malbolge](malbolge/spec.md) | yes | yes | yes | yes | `lake exe malbolge` | [no, bounded storage](malbolge/spec.md) | no | [not planned](malbolge/compiler.md) | n/a |
| malbolge-unshackled | wip | wip | wip | wip | `lake exe malbolge-unshackled` | yes | no | planned, via TC | no |
| [fractran](fractran/spec.md) | yes | yes | yes | yes | `lake exe fractran` | yes | no | [planned, via TC](fractran/compiler.md) | no |
| [thue](thue/spec.md) | yes | yes | yes | yes | `lake exe thue` | yes | no | [planned, via TC](thue/compiler.md) | no |
| [piet](piet/spec.md) | yes | yes | yes | yes | `lake exe piet` | yes | no | [planned, via TC](piet/compiler.md) | no |
| [ook](ook/spec.md) | yes | yes | yes | yes | `lake exe ook` | yes (via brainfuck) | no | [bespoke, free via brainfuck](ook/compiler.md) | no |
| [brainloller](brainloller/spec.md) | yes | yes | yes | yes | `lake exe brainloller` | yes (via brainfuck) | no | [bespoke, free via brainfuck](brainloller/compiler.md) | no |
| [deadfish](deadfish/spec.md) | yes | yes | yes | yes | `lake exe deadfish` | [no, finite state](deadfish/spec.md) | no | [bespoke, output-only](deadfish/compiler.md) | no |
| unlambda / SKI | wip | wip | wip | wip | `lake exe unlambda` | yes | no | planned, bespoke | no |
| [Turpentine](turpentine/spec.md) (front end) | yes | yes | yes | yes | `lake exe turpentine` | yes | no | (source) | (source) |

When a proof lands, its `no` becomes a `yes` linking to the theorem in
`computability.md`, and the claim in the known column stops being the last
word on the subject.

### Reading the two compiler columns

A language can have a compiler by two routes, and the columns say which.

* **Turpentine compiler** is what exists and what kind:
  * **bespoke** means hand-written for that target, accepting the whole
    language (or a named fragment) and producing compact output. This is
    what `lake exe turpentine compile --to <lang>` runs.
  * **via TC** means it comes free from a Turing-completeness proof, by
    composing that proof's compiler with one Turpentine-to-register-machine
    pass. Nobody writes a backend; the completeness proof is the backend.
    See [certified-compilation.md](certified-compilation.md).
  * A language can eventually have both, and several will. Derived
    compilers are verified but enormous and restricted to an I/O-free
    fragment; bespoke ones are practical. Neither subsumes the other.
* **Correctness proved** is whether a machine-checked correctness theorem
  exists for that compiler, and by which route. `no` means it does not,
  whatever the tests say. When one lands the cell links straight to the
  theorem, and names the route, so `yes, via TC` and `yes, bespoke` are
  different claims about different artifacts:
  * *via TC* means the theorem is an instance of the single
    `derived_correct`, which is proved once and holds for every language
    proved complete. Cheap per language, once the pipeline exists.
  * *bespoke* means somebody proved that particular hand-written backend
    correct against the Turpentine semantics, which is real per-language
    work.

Both routes land in the same interface, `TurpentineCompiler L`, so a
language with both gets `agree` for free: the two compilers provably
produce the same observable behaviour on programs both accept.

Nothing reads `yes` in that column today. Whitespace is closest: its
completeness proof is done, so the moment `compileToURM` is proved, its
cell becomes `yes, via TC` without any further backend work.

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
* [certified-compilation.md](certified-compilation.md): the plan for
  verified compilers via the URM, with the dependency graph and the
  argument for keeping the hand-written backends alongside them.
* [verification.md](verification.md): the compiler verification pipeline,
  including the split between derived compilers (correct by construction,
  obtained from a completeness proof) and effective ones (hand-written,
  practical, separately verified).
