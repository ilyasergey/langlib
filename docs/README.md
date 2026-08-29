# langlib documentation

Per-language specifications live in `docs/<langname>/spec.md`; compiler notes
(once a WTF compiler exists for the language) in `docs/<langname>/compiler.md`.

## Status matrix

Legend: `yes` done, `wip` in progress, `-` not started, `n/a` not planned
(with the reason in the language's spec page).

| Language | Spec | Parser | Interpreter | Examples + tests | Runner | WTF compiler | Verified compiler |
|----------|------|--------|-------------|------------------|--------|--------------|-------------------|
| [brainfuck](brainfuck/spec.md) | yes | yes | yes | yes | `lake exe brainfuck` | - | - |
| [fractran](fractran/spec.md) | yes | yes | yes | yes | `lake exe fractran` | n/a | n/a |
| [subleq](subleq/spec.md) | yes | yes | yes | yes | `lake exe subleq` | - | - |
| [WTF](wtf/spec.md) (front end) | yes | yes | yes | yes | `lake exe wtf` | (source) | (source) |
| [whitespace](whitespace/spec.md) | yes | yes | yes | yes | `lake exe whitespace` | - | - |
| [malbolge](malbolge/spec.md) | wip | wip | wip | wip | `lake exe malbolge` | n/a | n/a |
| [ook](ook/spec.md) | yes | yes | yes | yes | `lake exe ook` | - | - |
| [deadfish](deadfish/spec.md) | yes | yes | yes | yes | `lake exe deadfish` | - | - |
| [thue](thue/spec.md) | wip | wip | wip | wip | `lake exe thue` | n/a | n/a |
| [befunge93](befunge93/spec.md) | yes | yes | yes | yes | `lake exe befunge93` | - | - |
| [piet](piet/spec.md) | wip | wip | wip | wip | `lake exe piet` | - | - |
| [brainloller](brainloller/spec.md) | wip | wip | wip | wip | `lake exe brainloller` | - | - |

Lean code lives in `Langlib/Languages/<Langname>/` (the front end in
`Langlib/WTF/`), examples in `Langlib/Examples/<Langname>/`, golden tests
in `Langlib/Tests/<Langname>.lean`.

Planned WTF compiler targets and their status live in `PLAN.md` (Stage 4);
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
