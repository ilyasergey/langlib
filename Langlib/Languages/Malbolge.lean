import Langlib.Languages.Malbolge.Syntax
import Langlib.Languages.Malbolge.Parser
import Langlib.Languages.Malbolge.Semantics
import Langlib.Languages.Malbolge.Stability

/-!
# Malbolge

Ben Olmstead's 1998 language, named after Dante's eighth circle of Hell and
designed to be nearly impossible to program: a ternary machine whose
instructions depend on their address, encrypt themselves after every use,
and were chosen to mean as little as possible. The first program was found
by a search procedure two years after the language shipped. See
`docs/malbolge/spec.md` for the specification and
`Langlib/Languages/Malbolge/README.md` for usage.
-/
