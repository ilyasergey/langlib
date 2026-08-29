import Langlib.Turpentine.Syntax
import Langlib.Turpentine.Parser
import Langlib.Turpentine.Typecheck
import Langlib.Turpentine.Semantics
import Langlib.Turpentine.Compile.Brainfuck
import Langlib.Turpentine.Compile.Subleq
import Langlib.Turpentine.Compile.Whitespace

/-!
# Turpentine

The human-readable front end of langlib (`.turp` files): a small imperative
language, deeply embedded in Lean, inspired by Velvet
(https://github.com/verse-lab/velvet).

The name is the joke. Alan Perlis warned of the "Turing tar-pit in which
everything is possible but nothing of interest is easy", which describes
most of this library; turpentine is what dissolves tar. Write the program
once in a language with variables and loops, and let the compilers suffer.

Turpentine programs type-check, run on a pure fuel-based reference
interpreter, and compile to the esoteric languages under
`Langlib/Languages/` (Stage 4 of `docs/PLAN.md`).

See `docs/turpentine/spec.md` for the language reference and
`Langlib/Turpentine/README.md` for usage.
-/
