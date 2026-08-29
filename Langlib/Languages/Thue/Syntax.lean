/-!
# Thue: abstract syntax

Thue (John Colagioia, 2000) is a nondeterministic string-rewriting language.
A program is a list of rewrite rules `lhs::=rhs` followed by an initial
state string; execution replaces occurrences of left-hand sides until no
rule matches. Two right-hand-side forms are special: `:::` reads a line of
input, and a rhs beginning with `~` writes the rest of itself to output.

See `docs/thue/spec.md` for the language specification and the exact
semantics choices.
-/

namespace Langlib.Thue

/-- The right-hand side of a rule, classified at parse time. -/
inductive Rhs where
  /-- Replace the matched lhs by this string (possibly empty). -/
  | str (s : String)
  /-- `:::` : replace the matched lhs by one line read from input. -/
  | input
  /-- `~text` : erase the matched lhs and write `text` and a newline to
  output. -/
  | output (s : String)
deriving Repr, BEq, Inhabited

/-- One rewrite rule. The parser guarantees `lhs` is nonempty (an empty or
whitespace-only lhs terminates the rules section instead). -/
structure Rule where
  lhs : String
  rhs : Rhs
deriving Repr, BEq, Inhabited

/-- A Thue program: the rulebase and the initial state string. -/
structure Prog where
  rules : List Rule
  initial : String
deriving Repr, BEq, Inhabited

/-- Render a rhs back to concrete syntax. -/
def Rhs.render : Rhs → String
  | .str s => s
  | .input => ":::"
  | .output s => "~" ++ s

/-- Render a rule back to concrete syntax. -/
def Rule.render (r : Rule) : String :=
  r.lhs ++ "::=" ++ r.rhs.render

end Langlib.Thue
