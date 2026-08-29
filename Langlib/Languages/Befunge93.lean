import Langlib.Languages.Befunge93.Syntax
import Langlib.Languages.Befunge93.Parser
import Langlib.Languages.Befunge93.Semantics

/-!
# Befunge-93

Chris Pressey's 1993 language: a program counter walking an 80x25 torus of
self-modifiable characters, designed to be as hard to compile as possible.
See `docs/befunge93/spec.md` for the specification and
`Langlib/Languages/Befunge93/README.md` for usage.
-/
