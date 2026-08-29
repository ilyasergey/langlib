/-!
# FRACTRAN: abstract syntax

FRACTRAN (John H. Conway, 1987) has no commands at all: a program is a
finite list of positive fractions. The "abstract syntax" is therefore just
`List Frac`, where a `Frac` is a numerator/denominator pair of naturals.

The parser produces fractions in lowest terms with positive numerator and
denominator; the semantics relies on that invariant (see
`Langlib/Languages/Fractran/Semantics.lean` and `docs/fractran/spec.md`).
-/

namespace Langlib.Fractran

/-- A fraction `num/den` over the naturals. The parser guarantees
`num > 0`, `den > 0`, and `Nat.gcd num den = 1` (lowest terms); build
fractions with `Frac.reduced` to keep that invariant. -/
structure Frac where
  num : Nat
  den : Nat
deriving Repr, BEq, Inhabited

namespace Frac

/-- Build `a/b` in lowest terms. For `a, b > 0` the gcd is positive, so the
divisions are exact; the `g == 0` guard only fires on the degenerate `0/0`,
which the parser rejects anyway. -/
def reduced (a b : Nat) : Frac :=
  let g := Nat.gcd a b
  if g == 0 then ⟨a, b⟩ else ⟨a / g, b / g⟩

def render (f : Frac) : String := s!"{f.num}/{f.den}"

end Frac

/-- A FRACTRAN program: the ordered list of fractions. Order matters; each
step applies the *first* applicable fraction. -/
abbrev Prog := List Frac

/-- Render a program back to concrete syntax (space-separated fractions). -/
def Prog.render (p : Prog) : String :=
  String.intercalate " " (p.map Frac.render)

end Langlib.Fractran
