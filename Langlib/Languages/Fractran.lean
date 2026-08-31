import Langlib.Languages.Fractran.Syntax
import Langlib.Languages.Fractran.Parser
import Langlib.Languages.Fractran.Semantics
import Langlib.Languages.Fractran.Stability

/-!
# FRACTRAN

John H. Conway's 1987 language: a program is a list of positive fractions,
the state is a positive integer, and a step multiplies by the first fraction
that keeps the state integral. See `docs/fractran/spec.md` for the
specification and `Langlib/Languages/Fractran/README.md` for usage.
-/
