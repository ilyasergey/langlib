import Langlib.Languages.MalbolgeUnshackled.Syntax
import Langlib.Languages.MalbolgeUnshackled.Parser
import Langlib.Languages.MalbolgeUnshackled.Semantics

/-!
# Malbolge Unshackled

Ørjan Johansen's 2007 variant of Malbolge, with the ten-trit ceiling taken
out: values are 3-adic integers whose trit sequence is eventually constant,
so memory and registers are unbounded and the language is Turing complete
where Malbolge is not. See `docs/malbolge-unshackled/spec.md` for the
specification and `Langlib/Languages/MalbolgeUnshackled/README.md` for
usage.
-/
