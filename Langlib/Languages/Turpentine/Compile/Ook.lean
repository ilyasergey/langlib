import Langlib.Languages.Turpentine.Compile.Brainfuck
import Langlib.Languages.Ook

/-!
# Turpentine to Ook!

Ook! is brainfuck with the eight commands spelled as pairs of the words
`Ook.`, `Ook?`, `Ook!`. The correspondence is exact, so
`Langlib.Ook.Prog` is a definitional abbreviation for
`Langlib.Brainfuck.Prog`, and this backend is the brainfuck backend
composed with `Langlib.Ook.render`.

That means the supported fragment, the tape layout, the 16-bit two's
complement number representation and every trap are the brainfuck
backend's; see `docs/brainfuck/compiler.md` for what the code generator
actually does and `docs/ook/compiler.md` for this page's own notes.

## What this file adds over the brainfuck backend

* `compile` is `Langlib.Turpentine.Compile.Brainfuck.compile` at a
  different type ascription. Nothing is regenerated.
* `compileSource` renders through `Langlib.Ook.render` instead of
  `Langlib.Brainfuck.Prog.render`, and drops the brainfuck backend's
  prose header: brainfuck's header is a loop that never runs, and Ook!
  has no comment syntax at all, so there is nowhere to put it. Every
  token in the output file is load-bearing.
* `Langlib.Computability.Ook` proves
  `Langlib.Ook.parse (Langlib.Ook.render p) = .ok p`, so the text this
  file writes really does parse back to the program it compiled.

## Size

Every brainfuck command becomes two words of four characters plus a
separator, so an Ook! file is close to ten times the size of the
brainfuck it came from. `docs/ook/compiler.md` has measured numbers for
the examples.
-/

namespace Langlib.Turpentine.Compile.Ook

open Langlib.Turpentine

/-- Compile a Turpentine program to an Ook! program.

`Langlib.Ook.Prog` *is* `Langlib.Brainfuck.Prog`: Ook! differs from
brainfuck only in concrete syntax, so there is no separate abstract
syntax and no separate code generator. Errors are the brainfuck
backend's, and name the construct outside the supported fragment. -/
def compile (p : Program) : Except String Langlib.Ook.Prog :=
  Langlib.Turpentine.Compile.Brainfuck.compile p

/-- Turpentine source text to Ook! source text.

The output is exactly what `Langlib.Ook.parse` accepts: whitespace
separated `Ook.` / `Ook?` / `Ook!` words, sixteen to a line. Ook! has no
comments, so unlike the brainfuck backend there is no header. -/
def compileSource (src : String) : Except String String := do
  let prog ← parse src
  let ook ← compile prog
  return Langlib.Ook.render ook

/-- Compile and run, for the differential tests: the compiled program is
handed to the brainfuck core through the Ook! front end, so a test's
expected output is a claim about the generated *text*, not only about the
generated syntax tree.

The EOF convention is the one the generated code is written for
(`lake exe ook --eof zero`). -/
def runCompiled (src : String) (input : Langlib.Common.Input) (fuel : Nat) :
    Except String Langlib.Common.RunResult := do
  let text ← compileSource src
  Langlib.Ook.run { eof := .zero } text input fuel

end Langlib.Turpentine.Compile.Ook
