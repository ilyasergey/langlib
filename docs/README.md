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
| [brainfuck](brainfuck/spec.md) | yes | yes | yes | yes | `lake exe brainfuck` | yes | wip | - |
| [whitespace](whitespace/spec.md) | yes | yes | yes | yes | `lake exe whitespace` | wip | [yes](whitespace/compiler.md) | - |
| [subleq](subleq/spec.md) | yes | yes | yes | yes | `lake exe subleq` | yes | [yes](subleq/compiler.md) | - |
| [befunge93](befunge93/spec.md) | yes | yes | yes | yes | `lake exe befunge93` | no (bounded playfield) | - | - |
| [malbolge](malbolge/spec.md) | yes | yes | yes | yes | `lake exe malbolge` | open question | n/a | n/a |
| [fractran](fractran/spec.md) | yes | yes | yes | yes | `lake exe fractran` | yes | - | - |
| [thue](thue/spec.md) | yes | yes | yes | yes | `lake exe thue` | yes | - | - |
| [piet](piet/spec.md) | yes | yes | yes | yes | `lake exe piet` | yes | - | - |
| [ook](ook/spec.md) | yes | yes | yes | yes | `lake exe ook` | yes (via brainfuck) | - | - |
| [brainloller](brainloller/spec.md) | yes | yes | yes | yes | `lake exe brainloller` | yes (via brainfuck) | - | - |
| [deadfish](deadfish/spec.md) | yes | yes | yes | yes | `lake exe deadfish` | no (finite state) | - (output-only fragment) | - |
| unlambda / SKI | - | - | - | - | - | yes | n/a | n/a |
| [Turpentine](turpentine/spec.md) (front end) | yes | yes | yes | yes | `lake exe turpentine` | wip | (source) | (source) |

Lean code lives in `Langlib/Languages/<Langname>/` (the front end in
`Langlib/Turpentine/`), examples in `Langlib/Examples/<Langname>/`, golden tests
in `Langlib/Tests/<Langname>.lean`.

Planned Turpentine compiler targets and their status live in `PLAN.md` (Stage 4);
`n/a` entries are explained in the language's spec page (e.g. compiling to
malbolge is an open research problem).

## Project documents

* [PLAN.md](PLAN.md): the staged workplan (agents: keep it current).
* [PROGRESS.md](PROGRESS.md): dated progress log.
* [TESTING.md](TESTING.md): the two test layers, and what to install for
  differential testing per language.
* [ROADMAP.md](ROADMAP.md): candidate languages and instructions for adding
  one.
* [RELATED.md](RELATED.md): related efforts elsewhere.
* verification.md (Stage 6): the compiler verification pipeline design.
