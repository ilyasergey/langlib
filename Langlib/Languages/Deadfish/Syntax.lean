/-!
# Deadfish: abstract syntax

Deadfish (Jonathan Todd Skinner, 2006) has four commands operating on a
single integer accumulator, plus a fifth pseudo-command we make explicit:
every character that is not `i`, `d`, `s`, `o` prints a bare newline in the
original C interpreter, so the AST records unknown characters as `noise`
rather than discarding them. Consequently every string is a syntactically
valid Deadfish program.

See `docs/deadfish/spec.md` for the language specification and the exact
semantic decisions.
-/

namespace Langlib.Deadfish

/-- One Deadfish command. -/
inductive Cmd where
  /-- `i` : increment the accumulator. -/
  | inc
  /-- `d` : decrement the accumulator. -/
  | dec
  /-- `s` : square the accumulator. -/
  | square
  /-- `o` : output the accumulator in decimal, followed by a newline. -/
  | output
  /-- Any other character: prints a bare newline ("errors are not
  acknowledged: the shell simply adds a newline character"). -/
  | noise
deriving Repr, BEq, Inhabited

/-- A Deadfish program is a sequence of commands. It has no loops, so every
program terminates; the language is famously not Turing complete. -/
abbrev Prog := List Cmd

/-- Render a command back to concrete syntax (`noise` as a space). -/
def Cmd.render : Cmd → Char
  | .inc => 'i'
  | .dec => 'd'
  | .square => 's'
  | .output => 'o'
  | .noise => ' '

def Prog.render (p : Prog) : String :=
  String.ofList (p.map Cmd.render)

end Langlib.Deadfish
