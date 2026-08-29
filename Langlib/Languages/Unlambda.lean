import Langlib.Languages.Unlambda.Syntax
import Langlib.Languages.Unlambda.Parser
import Langlib.Languages.Unlambda.Semantics

/-!
# Unlambda

David Madore's 1999 language: the lambda calculus with the lambda removed,
leaving prefix application, the S and K combinators, a printing function,
call/cc and a delay special form. See `docs/unlambda/spec.md` for the
specification and `Langlib/Languages/Unlambda/README.md` for usage.

Its companion is `Langlib.Languages.Ski`, the pure combinator calculus that
Unlambda's Turing-completeness argument goes through.
-/
