# langlib documentation

Per-language specifications live in `docs/<langname>/spec.md`; compiler notes
(once a WTF compiler exists for the language) in `docs/<langname>/compiler.md`.

## Languages

| Language | Spec | Lean code | Runner |
|----------|------|-----------|--------|
| brainfuck | [spec](brainfuck/spec.md) | `Langlib/Brainfuck/` | `lake exe brainfuck` |
| ook | [spec](ook/spec.md) | `Langlib/Ook/` | `lake exe ook` |
| deadfish | [spec](deadfish/spec.md) | `Langlib/Deadfish/` | `lake exe deadfish` |
| whitespace | [spec](whitespace/spec.md) | `Langlib/Whitespace/` | `lake exe whitespace` |
| befunge93 | [spec](befunge93/spec.md) | `Langlib/Befunge93/` | `lake exe befunge93` |
| subleq | [spec](subleq/spec.md) | `Langlib/Subleq/` | `lake exe subleq` |
| thue | [spec](thue/spec.md) | `Langlib/Thue/` | `lake exe thue` |
| fractran | [spec](fractran/spec.md) | `Langlib/Fractran/` | `lake exe fractran` |
| malbolge | [spec](malbolge/spec.md) | `Langlib/Malbolge/` | `lake exe malbolge` |

## Project documents

* [PLAN.md](PLAN.md): the staged workplan (agents: keep it current).
* [PROGRESS.md](PROGRESS.md): dated progress log.
* [ROADMAP.md](ROADMAP.md): candidate languages and instructions for adding
  one.
* [ALTERNATIVES.md](ALTERNATIVES.md): related efforts elsewhere.
* verification.md (Stage 6): the compiler verification pipeline design.
