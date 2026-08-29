import Langlib.Languages.Ski.Syntax

/-!
# SKI: parser

Applicative notation: `SKK` is `(S K) K`, brackets group, whitespace
separates nothing in particular and may be omitted. Either case is accepted
for the three letters, and `#` starts a comment that runs to end of line.

The parser keeps one accumulator per bracket depth, so there is no
recursion over the input and no fuel: at each atom the top accumulator
either takes the atom as its whole term or applies its term to it.
-/

namespace Langlib.Ski

private structure Pos where
  line : Nat := 1
  col : Nat := 1

private def Pos.show (p : Pos) : String := s!"{p.line}:{p.col}"

private def Pos.advance (p : Pos) (c : Char) : Pos :=
  if c == '\n' then { line := p.line + 1, col := 1 }
  else { p with col := p.col + 1 }

/-- One bracket level: where it was opened, and the term built so far. -/
private abbrev Level := Pos × Option Term

/-- Apply the accumulated term of a level to a new atom. -/
private def Level.push (l : Level) (t : Term) : Level :=
  match l.2 with
  | none => (l.1, some t)
  | some f => (l.1, some (.app f t))

/-- Parse SKI source into a `Prog`. -/
def parse (src : String) : Except String Prog := do
  let mut levels : List Level := [({}, none)]
  let mut pos : Pos := {}
  let mut inComment := false
  for c in src.toList do
    if inComment then
      if c == '\n' then inComment := false
    else if c == '#' then
      inComment := true
    else if c == ' ' || c == '\t' || c == '\n' || c == '\r' then
      pure ()
    else
      let atom? : Option Term :=
        match c with
        | 'S' | 's' => some .S
        | 'K' | 'k' => some .K
        | 'I' | 'i' => some .I
        | _ => none
      match atom? with
      | some t =>
        match levels with
        | [] => throw s!"internal: no level at {pos.show}"
        | l :: rest => levels := l.push t :: rest
      | none =>
        if c == '(' then
          levels := (pos, none) :: levels
        else if c == ')' then
          match levels with
          | [] | [_] => throw s!"unmatched ')' at {pos.show}"
          | (openPos, inner) :: outer :: rest =>
            match inner with
            | none => throw s!"empty parentheses opened at {openPos.show}"
            | some t => levels := outer.push t :: rest
        else
          throw s!"unrecognised character '{c}' at {pos.show}"
    pos := pos.advance c
  match levels with
  | [(_, some t)] => return t
  | [(_, none)] => throw "empty program: an SKI program is one term"
  | _ =>
    match levels.head? with
    | some (openPos, _) => throw s!"unclosed '(' at {openPos.show}"
    | none => throw "internal: empty level stack"

end Langlib.Ski
