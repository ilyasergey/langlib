import Langlib.Languages.Ook.Syntax
import Langlib.Languages.Ook.Parser
import Langlib.Languages.Ook.Semantics

/-!
# Ook!

David Morgan-Mar's 2001 language for orang-utans: brainfuck's eight commands
spelled as pairs of `Ook.`, `Ook?`, `Ook!`. Parsing produces a brainfuck
program and evaluation delegates to the brainfuck core. See
`docs/ook/spec.md` for the specification and `Langlib/Languages/Ook/README.md`
for usage.
-/
