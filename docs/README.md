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

Every entry in the proved column currently reads `no`. That is the honest
state: the interpreters and compilers came first, and Stage 8 of
[PLAN.md](PLAN.md) is where that column starts changing. Every language
claimed Turing complete is also a language Turpentine should compile to.

| Language | Spec | Parser | Interpreter | Examples + tests | Runner | TC known | TC proved | Turpentine compiler | Verified compiler |
|----------|------|--------|-------------|------------------|--------|----------|-----------|---------------------|-------------------|
| [brainfuck](brainfuck/spec.md) | yes | yes | yes | yes | `lake exe brainfuck` | yes | no | [wip](brainfuck/compiler.md) | - |
| [whitespace](whitespace/spec.md) | yes | yes | yes | yes | `lake exe whitespace` | yes | no | [yes](whitespace/compiler.md) | - |
| [subleq](subleq/spec.md) | yes | yes | yes | yes | `lake exe subleq` | yes | no | [yes](subleq/compiler.md) | - |
| [befunge93](befunge93/spec.md) | yes | yes | yes | yes | `lake exe befunge93` | [depends on cell width](befunge93/spec.md) | no | [fragment only](befunge93/compiler.md) | - |
| [malbolge](malbolge/spec.md) | yes | yes | yes | yes | `lake exe malbolge` | no (bounded storage) | no | [bounded fragment](malbolge/compiler.md) | - |
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
compiler unless it is Turing complete.** Bounded-storage languages get a
fragment and nothing more, and the fragment is bounded by their storage,
not by our effort. [malbolge](malbolge/spec.md) has 59049 words for code
and data together, so a compiled program must fit in that;
[befunge93](befunge93/spec.md) has 2000 playfield cells for its code;
[deadfish](deadfish/spec.md) has no loops at all, so it takes only
straight-line output. Each of those compiler pages states its own bound.

Lean code lives in `Langlib/Languages/<Langname>/` (the front end in
`Langlib/Turpentine/`), examples in `Langlib/Examples/<Langname>/`, golden tests
in `Langlib/Tests/<Langname>.lean`.

Every language has a `docs/<langname>/compiler.md`: for the backends that
exist it describes what was built, and for the rest it is a concrete plan
(or, for befunge93, an argument for why a general backend is the wrong
thing to build). Planned targets and their sequencing live in
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
* [verification.md](verification.md): the compiler verification pipeline,
  including the split between derived compilers (correct by construction,
  obtained from a completeness proof) and effective ones (hand-written,
  practical, separately verified).
