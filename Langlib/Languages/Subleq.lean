import Langlib.Languages.Subleq.Syntax
import Langlib.Languages.Subleq.Parser
import Langlib.Languages.Subleq.Semantics
import Langlib.Languages.Subleq.Trace
import Langlib.Languages.Subleq.Stability

/-!
# Subleq

The classic one-instruction set computer: subtract and branch if less than
or equal to zero, over an unbounded memory of signed integers. See
`docs/subleq/spec.md` for the specification and
`Langlib/Languages/Subleq/README.md` for usage.
-/
