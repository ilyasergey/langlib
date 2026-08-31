import Langlib.Languages.Whitespace.Syntax
import Langlib.Languages.Whitespace.Parser
import Langlib.Languages.Whitespace.Semantics
import Langlib.Languages.Whitespace.Trace
import Langlib.Languages.Whitespace.Stability
import Langlib.Languages.Whitespace.Faithful

/-!
# Whitespace

Edwin Brady and Chris Morris's 2003 language: a stack machine with a heap
and subroutines, written entirely in spaces, tabs, and linefeeds. See
`docs/whitespace/spec.md` for the specification and
`Langlib/Languages/Whitespace/README.md` for usage.

`Whitespace/Trace.lean` proves that the interpreter's report of its own I/O
events is honest, which is what lets whitespace be reasoned about
behaviourally rather than only by its final answer.
-/
