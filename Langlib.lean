import Langlib.Common
import Langlib.Languages.Befunge93
import Langlib.Languages.Brainfuck
import Langlib.Languages.Deadfish
import Langlib.Languages.Fractran
import Langlib.Languages.Ook
import Langlib.Languages.Subleq
import Langlib.Languages.Whitespace
import Langlib.WTF

/-!
# Langlib

An open-source library of the semantics of esoteric and fun programming
languages, with a human-readable front end (WTF) and compilers from it.

* `Langlib.<Langname>`: one module tree per esoteric language (AST, parser,
  pure reference interpreter, standalone runner).
* `Langlib.Common`: shared infrastructure (I/O model, execution outcomes,
  parser helpers, test harness).
* `Langlib.WTF`: the Well-Typed Formalism front-end language and its
  compilers to the esolangs.
* `Langlib.Tests`: the test suite (`lake test`).

Language modules are imported here as they land (see `docs/PLAN.md`).
-/
