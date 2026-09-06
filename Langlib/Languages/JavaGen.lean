import Langlib.Languages.JavaGen.Syntax
import Langlib.Languages.JavaGen.Validation
import Langlib.Languages.JavaGen.Parser
import Langlib.Languages.JavaGen.Semantics
import Langlib.Languages.JavaGen.Stability
import Langlib.Languages.JavaGen.Java
import Langlib.Languages.JavaGen.Answer
import Langlib.Languages.JavaGen.AnswerStability

/-! # JavaGen

Unary contravariant subtyping as a fuel-based programming language, following
Grigore (2017). See `docs/javagen/spec.md`. Java export has differential tests;
the universal compiler and its answer/divergence proofs are pending.
-/
