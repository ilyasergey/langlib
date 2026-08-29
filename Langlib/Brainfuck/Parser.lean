import Langlib.Brainfuck.Syntax

/-!
# Brainfuck: parser

Everything except the eight command characters is a comment. The only way a
brainfuck program can fail to parse is bracket mismatch; we report the line
and column of the offending bracket.
-/

namespace Langlib.Brainfuck

private structure Pos where
  line : Nat := 1
  col : Nat := 1

private def Pos.show (p : Pos) : String := s!"{p.line}:{p.col}"

private def Pos.advance (p : Pos) (c : Char) : Pos :=
  if c == '\n' then { line := p.line + 1, col := 1 }
  else { p with col := p.col + 1 }

/-- Parse brainfuck source into a `Prog`. Fails only on unbalanced
brackets. -/
def parse (src : String) : Except String Prog := do
  -- `stack` holds the programs under construction, innermost first, each
  -- with the position of its opening bracket; ops are accumulated reversed.
  let mut cur : List Op := []
  let mut stack : List (Pos × List Op) := []
  let mut pos : Pos := {}
  for c in src.toList do
    match c with
    | '+' => cur := .inc :: cur
    | '-' => cur := .dec :: cur
    | '>' => cur := .right :: cur
    | '<' => cur := .left :: cur
    | '.' => cur := .output :: cur
    | ',' => cur := .input :: cur
    | '[' =>
      stack := (pos, cur) :: stack
      cur := []
    | ']' =>
      match stack with
      | [] => throw s!"unmatched ']' at {pos.show}"
      | (_, outer) :: rest =>
        cur := .loop cur.reverse :: outer
        stack := rest
    | _ => pure ()
    pos := pos.advance c
  match stack with
  | [] => return cur.reverse
  | (openPos, _) :: _ => throw s!"unmatched '[' at {openPos.show}"

end Langlib.Brainfuck
