import Langlib.Languages.Turpentine.Syntax
import Langlib.Languages.Turpentine.Parser
import Langlib.Languages.Turpentine.Typecheck
import Langlib.Languages.Turpentine.Semantics
import Langlib.Languages.Turpentine.Trace
import Langlib.Languages.Turpentine.Compile.Brainfuck
import Langlib.Languages.Turpentine.Compile.MalbolgeUnshackled
import Langlib.Languages.Turpentine.Compile.Subleq
import Langlib.Languages.Turpentine.Compile.Whitespace

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
`Langlib/Languages/Turpentine/README.md` for usage.
-/
