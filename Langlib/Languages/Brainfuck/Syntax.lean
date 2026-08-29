/-!
# Brainfuck: abstract syntax

Brainfuck (Urban Müller, 1993) has eight commands. Six are primitive; the
bracket pair `[` `]` forms a loop. We parse brackets into a tree, so the AST
has seven constructors and matched brackets by construction.

See `docs/brainfuck/spec.md` for the language specification and the exact
semantics choices.
-/

namespace Langlib.Brainfuck

/-- One brainfuck command. Loop bodies are nested programs, so bracket
matching is a parse-time concern, not a run-time one. -/
inductive Op where
  /-- `+` : increment the current cell (mod 256). -/
  | inc
  /-- `-` : decrement the current cell (mod 256). -/
  | dec
  /-- `>` : move the data pointer one cell to the right. -/
  | right
  /-- `<` : move the data pointer one cell to the left. -/
  | left
  /-- `.` : output the current cell as one byte. -/
  | output
  /-- `,` : read one byte of input into the current cell. -/
  | input
  /-- `[ body ]` : while the current cell is nonzero, run `body`. -/
  | loop (body : List Op)
deriving Repr, BEq, Inhabited

/-- A brainfuck program is a sequence of commands. -/
abbrev Prog := List Op

/-- Render a program back to concrete syntax (used in tests and by the
WTF compiler's pretty-printer). -/
partial def Op.render : Op → String
  | .inc => "+"
  | .dec => "-"
  | .right => ">"
  | .left => "<"
  | .output => "."
  | .input => ","
  | .loop body => "[" ++ String.join (body.map Op.render) ++ "]"

def Prog.render (p : Prog) : String :=
  String.join (p.map Op.render)

end Langlib.Brainfuck
