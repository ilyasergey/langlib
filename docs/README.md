# langlib documentation

Per-language specifications live in `docs/<langname>/spec.md`; compiler notes
(once a Turpentine compiler exists for the language) in `docs/<langname>/compiler.md`.

## Status matrix

Legend: `yes` done, `wip` in progress, `-` not started, `n/a` not applicable
(with the reason in the language's spec page). The "Turing complete" column
records the *claim*; `proved` means there is a machine-checked proof, and a
bare `yes`/`no` means the claim is the standard one and the proof is
planned (see [PLAN.md](PLAN.md), Stage 8). Every language claimed Turing
complete is a language Turpentine should eventually compile to.

| Language | Spec | Parser | Interpreter | Examples + tests | Runner | Turing complete | Turpentine compiler | Verified compiler |
|----------|------|--------|-------------|------------------|--------|-----------------|---------------------|-------------------|
| [brainfuck](brainfuck/spec.md) | yes | yes | yes | yes | `lake exe brainfuck` | yes | [wip](brainfuck/compiler.md) | - |
| [whitespace](whitespace/spec.md) | yes | yes | yes | yes | `lake exe whitespace` | wip | [yes](whitespace/compiler.md) | - |
| [subleq](subleq/spec.md) | yes | yes | yes | yes | `lake exe subleq` | yes | [yes](subleq/compiler.md) | - |
| [befunge93](befunge93/spec.md) | yes | yes | yes | yes | `lake exe befunge93` | see spec (depends on cell width) | [fragment only](befunge93/compiler.md) | - |
| [malbolge](malbolge/spec.md) | yes | yes | yes | yes | `lake exe malbolge` | no (bounded storage) | [planned](malbolge/compiler.md) | - |
| [fractran](fractran/spec.md) | yes | yes | yes | yes | `lake exe fractran` | yes | [planned](fractran/compiler.md) | - |
| [thue](thue/spec.md) | yes | yes | yes | yes | `lake exe thue` | yes | [planned](thue/compiler.md) | - |
| [piet](piet/spec.md) | yes | yes | yes | yes | `lake exe piet` | yes | [planned](piet/compiler.md) | - |
| [ook](ook/spec.md) | yes | yes | yes | yes | `lake exe ook` | yes (via brainfuck) | [free via brainfuck](ook/compiler.md) | - |
| [brainloller](brainloller/spec.md) | yes | yes | yes | yes | `lake exe brainloller` | yes (via brainfuck) | [free via brainfuck](brainloller/compiler.md) | - |
| [deadfish](deadfish/spec.md) | yes | yes | yes | yes | `lake exe deadfish` | no (finite state) | [output-only fragment](deadfish/compiler.md) | - |
| unlambda / SKI | - | - | - | - | - | yes | n/a | n/a |
| [Turpentine](turpentine/spec.md) (front end) | yes | yes | yes | yes | `lake exe turpentine` | wip | (source) | (source) |

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
