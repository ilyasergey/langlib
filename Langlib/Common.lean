import Langlib.Common.Compilation
import Langlib.Common.Image
import Langlib.Common.Io
import Langlib.Common.Runner
import Langlib.Common.TestHarness

/-!
# Langlib.Common

Shared infrastructure for all languages in the library: the pure execution
model (`Input`, `RunResult`, `Exit`, `Trace`), the notion of a language and
of a correct compiler (`ProgLang`, `CertifiedCompiler`,
`IOCertifiedCompiler`), standalone-runner scaffolding (`Runner`), the
golden-test harness (`Suite`), and an RGB image type with a PPM reader for
the graphical languages (`Image`).

`Langlib/Common/Computability.lean` — Turing completeness and bounded
storage — is deliberately *not* imported here. It is the only module in
`Langlib/Common/` that needs cslib, and with it Mathlib; keeping it out of
this roll-up is what lets the interpreters and the hand-written compilers
import `Langlib.Common` and stay light. The files that reason about
computational power import it by name.
-/
