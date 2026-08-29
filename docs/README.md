# langlib documentation

Per-language specifications live in `docs/<langname>/spec.md`; compiler notes
(once a Turpentine compiler exists for the language) in `docs/<langname>/compiler.md`.

## Status matrix

Legend: `yes` done, `wip` in progress, `-` not started, `n/a` not applicable
(with the reason in the language's spec page).

**TC** is Turing completeness: whether the language can compute
everything a Turing machine can. It gets two columns on purpose, because
the difference between them is the whole point of this library:

* **TC known** is the claim: what the literature says, or what our own
  spec page argues. It is prose, and prose can be wrong. We have already
  found two claims that were, one about
  [befunge93](befunge93/spec.md) and one about
  [malbolge](malbolge/spec.md).
* **TC proved** is whether a machine-checked theorem exists in this
  repository. `no` means nobody has proved it here yet, whatever the
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

| Language | Spec | Parser | Interpreter | Examples + tests | Runner | TC known | TC proved | Turpentine compiler | Verified compiler |
|----------|------|--------|-------------|------------------|--------|----------|-----------|---------------------|-------------------|
| [brainfuck](brainfuck/spec.md) | yes | yes | yes | yes | `lake exe brainfuck` | yes | no | [yes, scalars](brainfuck/compiler.md) | - |
| [whitespace](whitespace/spec.md) | yes | yes | yes | yes | `lake exe whitespace` | yes | [**yes**](../Langlib/Computability/Whitespace.lean) | [yes](whitespace/compiler.md) | - |
| [subleq](subleq/spec.md) | yes | yes | yes | yes | `lake exe subleq` | yes | no | [yes](subleq/compiler.md) | - |
| [befunge93](befunge93/spec.md) | yes | yes | yes | yes | `lake exe befunge93` | [depends on cell width](befunge93/spec.md) | no | [not planned](befunge93/compiler.md) | n/a |
| [malbolge](malbolge/spec.md) | yes | yes | yes | yes | `lake exe malbolge` | no (bounded storage) | no | [not planned](malbolge/compiler.md) | n/a |
| malbolge-unshackled | wip | wip | wip | wip | `lake exe malbolge-unshackled` | yes | no | planned (unbounded, so a full compiler is possible) | - |
| [fractran](fractran/spec.md) | yes | yes | yes | yes | `lake exe fractran` | yes | no | [planned](fractran/compiler.md) | - |
| [thue](thue/spec.md) | yes | yes | yes | yes | `lake exe thue` | yes | no | [planned](thue/compiler.md) | - |
| [piet](piet/spec.md) | yes | yes | yes | yes | `lake exe piet` | yes | no | [planned](piet/compiler.md) | - |
| [ook](ook/spec.md) | yes | yes | yes | yes | `lake exe ook` | yes (via brainfuck) | no | [free via brainfuck](ook/compiler.md) | - |
| [brainloller](brainloller/spec.md) | yes | yes | yes | yes | `lake exe brainloller` | yes (via brainfuck) | no | [free via brainfuck](brainloller/compiler.md) | - |
| [deadfish](deadfish/spec.md) | yes | yes | yes | yes | `lake exe deadfish` | no (finite state) | no | [output-only fragment](deadfish/compiler.md) | - |
| unlambda / SKI | wip | wip | wip | wip | `lake exe unlambda` | yes | no | planned | - |
| [Turpentine](turpentine/spec.md) (front end) | yes | yes | yes | yes | `lake exe turpentine` | yes | no | (source) | (source) |

When a proof lands, its `no` becomes a `yes` linking to the theorem in
`computability.md`, and the claim in the known column stops being the last
word on the subject.

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
