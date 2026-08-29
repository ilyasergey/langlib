/-!
# SKI combinator calculus: abstract syntax

The whole language: three constants and application. `S`, `K` and `I` are
Schönfinkel's and Curry's combinators, and a term is a binary tree whose
leaves are those three.

See `docs/ski/spec.md` for the specification, and
`Langlib/Languages/Unlambda/` for the esoteric surface syntax of the same
calculus.
-/

namespace Langlib.Ski

/-- An SKI term. -/
inductive Term where
  /-- `S`: `S x y z` reduces to `x z (y z)`. -/
  | S
  /-- `K`: `K x y` reduces to `x`. -/
  | K
  /-- `I`: `I x` reduces to `x`. Definable as `S K K`, kept for legibility. -/
  | I
  /-- Application, written by juxtaposition and associating to the left. -/
  | app (fn arg : Term)
deriving Repr, BEq, Inhabited

/-- An SKI program is a term. -/
abbrev Prog := Term

namespace Term

/-- Render a term in the customary applicative notation, with the minimum
number of parentheses: application associates to the left, so only an
argument that is itself an application needs brackets. -/
def render : Term → String
  | .S => "S"
  | .K => "K"
  | .I => "I"
  | .app f a =>
    let arg := match a with
      | .app _ _ => "(" ++ render a ++ ")"
      | _ => render a
    render f ++ arg

/-- Render a term as an Unlambda program: application is a prefix backquote
and the combinators are lower case. This is the whole of the translation
from SKI into Unlambda, and it is the reason the two languages live next to
each other in the library. -/
def toUnlambda : Term → String
  | .S => "s"
  | .K => "k"
  | .I => "i"
  | .app f a => "`" ++ toUnlambda f ++ toUnlambda a

/-- The number of combinators in a term. -/
def size : Term → Nat
  | .app f a => size f + size a
  | _ => 1

end Term

end Langlib.Ski
