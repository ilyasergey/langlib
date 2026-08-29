# Progress log

Newest first. Add a dated entry for every substantial batch of work.

## 2026-08-29 (later)

* Layout revision per project owner: everything lives under `Langlib/`
  (no separate `Esolang` folder); example/test subfolders are capitalised;
  the front end is spelled WTF. `docs/ALTERNATIVES.md` renamed to
  `docs/RELATED.md`; the dead wolflo/esolang-semantics link replaced by the
  live parent repo (ellisonch/esolang-semantics).
* Plan additions: Piet and Brainloller confirmed as a graphical second
  wave; "Java Generics are Turing Complete" (arXiv:1605.05274) added to the
  roadmap; Brainfuck/Whitespace/Malbolge confirmed as must-haves.
* Stage 2 started: shared infrastructure (`Langlib/Common/`: pure
  fuel-based execution model, input stream, runner scaffolding, golden-test
  harness) and the brainfuck exemplar (AST, parser with positioned bracket
  errors, zipper-tape semantics with three EOF conventions, runner
  `lake exe brainfuck`, 9 examples, 21 golden tests, spec page
  `docs/brainfuck/spec.md`, differential-test script skeleton).

## 2026-08-29

* Stage 0: repository scaffolded. Lake project on Lean 4.33.1, single
  library `Langlib` (esolangs, `Common`, `WTF`, `Tests`, `Examples` all
  under the `Langlib/` folder), test driver stub. README, CLAUDE.md (project
  policies), CONTRIBUTING, Apache 2.0 LICENSE, .gitignore, docs skeleton
  (PLAN, PROGRESS, ROADMAP, RELATED). Initial language set chosen
  (see PLAN Stage 1).
