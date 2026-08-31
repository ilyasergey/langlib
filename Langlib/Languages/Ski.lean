import Langlib.Languages.Ski.Syntax
import Langlib.Languages.Ski.Parser
import Langlib.Languages.Ski.Semantics
import Langlib.Languages.Ski.Stability

/-!
# SKI combinator calculus

Schönfinkel (1924) and Curry (1930): three constants, one operation, and
every computable function. The library keeps it next to Unlambda, whose
core it is, because it is the language the functional route to Turing
completeness is stated about. See `docs/ski/spec.md`.
-/
