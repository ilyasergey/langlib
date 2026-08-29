import Langlib.Common.Image
import Langlib.Common.Io
import Langlib.Common.Runner
import Langlib.Common.TestHarness

/-!
# Langlib.Common

Shared infrastructure for all languages in the library: the pure execution
model (`Input`, `RunResult`, `Exit`), standalone-runner scaffolding
(`Runner`), the golden-test harness (`Suite`), and an RGB image type with
a PPM reader for the graphical languages (`Image`).
-/
