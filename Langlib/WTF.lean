import Langlib.WTF.Syntax
import Langlib.WTF.Parser
import Langlib.WTF.Typecheck
import Langlib.WTF.Semantics

/-!
# WTF: the Well-Typed Formalism

The human-readable front end of langlib (`.wtf` files): a small imperative
language, deeply embedded in Lean, inspired by Velvet
(https://github.com/verse-lab/velvet). WTF programs type-check, run on a
pure fuel-based reference interpreter, and compile to the esoteric
languages under `Langlib/Languages/` (Stage 4 of `docs/PLAN.md`).

See `docs/wtf/spec.md` for the language reference and
`Langlib/WTF/README.md` for usage.
-/
