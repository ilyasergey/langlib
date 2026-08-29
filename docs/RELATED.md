# Alternatives and related work

langlib is not the first attempt to collect esoteric languages or to give
them formal semantics. This page lists the efforts we know about, what they
cover, and how langlib differs. If you know of another one, please add it.

## The encyclopedia

* **Esolang, the esoteric languages wiki**: https://esolangs.org/

  The community hub since 2005: thousands of language articles, example
  programs, and theory pages (Turing-completeness proofs, translations
  between languages). It is the reference catalogue and the first place to
  look when choosing what to implement next. Esolangs.org documents
  languages in prose; langlib complements it with machine-checked semantics
  and runnable interpreters in one codebase. Wiki content is released under
  CC0, which makes it a good research source, though our specs are written
  independently.

## Formal semantics collections

* **esolang-semantics** (Chucky Ellison):
  https://github.com/ellisonch/esolang-semantics

  The closest analog to langlib: a collection of esoteric language semantics
  written in the K framework, including several of the same languages. K
  gives executable semantics from a rewriting-based definition; langlib
  instead uses a proof assistant, so the same artifact that runs programs
  can be the subject of correctness proofs for compilers.

* **k-brainfuck-semantics** (wolflo):
  https://github.com/wolflo/k-brainfuck-semantics

  Brainfuck alone, in K, together with `kprove` specifications verifying
  properties of individual brainfuck programs; its README links the parent
  collection above.

## Verified brainfuck compilers

* **bfcoq** (thaliaarchi): https://github.com/thaliaarchi/bfcoq

  A verified brainfuck compiler in Coq (now Rocq). Part of the same
  author's broader esolang-formalisation work.

* **Brainfuck in Coq** (reynir): https://github.com/reynir/Brainfuck

  Brainfuck formalized in Coq, with a verified compiler from a small
  arithmetic language to brainfuck. Close in spirit to our Turpentine-to-brainfuck
  pipeline, at a smaller scale.

* **BrainCoqulus** (Harvard CS260r project, 2017):
  https://read.seas.harvard.edu/~kohler/class/cs260r-17/projects/braincoqulus.pdf

  A verified compiler from the lambda calculus to brainfuck, in Coq. The
  paper is a useful map of the proof-engineering pain involved in targeting
  brainfuck; it motivates our choice to route verification through a small
  imperative front end (Turpentine) rather than a functional one.

## How langlib differs

Existing formalisations are either single-language (the Coq projects) or
semantics-only (the K collections). langlib aims at the union: many
languages, one shared execution model, documented specs with history, plus a
common front-end language with compilers to each target and a shared
verification pipeline, all in Lean 4.
