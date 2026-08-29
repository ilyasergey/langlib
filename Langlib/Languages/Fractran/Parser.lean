import Langlib.Languages.Fractran.Syntax

/-!
# FRACTRAN: parser

Concrete syntax: a program file is a whitespace-separated list of fractions
`a/b` where `a` and `b` are positive decimal integers. A bare integer `a`
is accepted as shorthand for `a/1` (Conway's own listings write the final
fraction of PRIMEGAME as 55). `#` starts a comment that runs to the end of
the line.

Parse errors (all reported with a line number): a token that is not a
fraction, a zero numerator, a zero denominator. Zero is rejected because
Conway's definition uses *positive* rationals: a zero numerator would send
the state to 0 and a zero denominator is not a rational at all.

Fractions are reduced to lowest terms here, so the semantics can test
divisibility against the denominator alone.
-/

namespace Langlib.Fractran

private def parseNat (tok : String) (lineNo : Nat) (part : String) :
    Except String Nat :=
  match tok.toNat? with
  | some n => .ok n
  | none => .error s!"line {lineNo}: bad fraction: {part} '{tok}' is not a decimal integer"

private def parseToken (tok : String) (lineNo : Nat) : Except String Frac := do
  let (a, b) ← match tok.splitOn "/" with
    | [a] => pure (← parseNat a lineNo "term", 1)
    | [a, b] => pure (← parseNat a lineNo "numerator", ← parseNat b lineNo "denominator")
    | _ => throw s!"line {lineNo}: bad fraction '{tok}' (expected a/b or a bare integer)"
  if a == 0 then
    throw s!"line {lineNo}: fraction '{tok}' has zero numerator (fractions must be positive)"
  if b == 0 then
    throw s!"line {lineNo}: fraction '{tok}' has zero denominator"
  return Frac.reduced a b

/-- Parse FRACTRAN source into a `Prog`: strip `#` comments per line, split
the rest on whitespace, parse each token as a fraction in lowest terms. -/
def parse (src : String) : Except String Prog := do
  let mut prog : List Frac := []
  let mut lineNo := 1
  for line in src.splitOn "\n" do
    let code := match line.splitOn "#" with
      | [] => ""
      | c :: _ => c
    let toks := (code.split (fun c => c.isWhitespace)).toList.map (·.toString)
    for tok in toks do
      if !tok.isEmpty then
        prog := (← parseToken tok lineNo) :: prog
    lineNo := lineNo + 1
  return prog.reverse

end Langlib.Fractran
