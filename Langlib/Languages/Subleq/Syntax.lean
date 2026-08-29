/-!
# Subleq: abstract syntax

Subleq (SUBtract and branch if Less than or EQual to zero) is a
one-instruction machine, so there is no instruction AST to speak of: a
program *is* its initial memory image, a sequence of signed integer words.
Code, data, and operands all live in the same array, and programs routinely
rewrite their own operands.

The assembler surface syntax (labels, `?`, offsets) lives in
`Parser.lean`; it elaborates away completely. See `docs/subleq/spec.md`
for the language specification and the exact semantic choices.
-/

namespace Langlib.Subleq

/-- A subleq program: the initial memory image. `mem[pc]`, `mem[pc+1]`,
`mem[pc+2]` are the `A`, `B`, `C` operands of the instruction at `pc`.
Addresses at or beyond the image read as 0 at run time. -/
abbrev Prog := Array Int

/-- Render a program as raw assembler text (space-separated decimals, three
words per line). Used in tests and by the future Turpentine compiler's
pretty-printer; the output re-assembles to the same image. -/
def Prog.render (p : Prog) : String :=
  String.intercalate "\n" <|
    (List.range ((p.size + 2) / 3)).map fun i =>
      String.intercalate " " <|
        ((p.toList.drop (3 * i)).take 3).map toString

end Langlib.Subleq
