import Langlib.Languages.Brainfuck.Parser
import Langlib.Languages.Ook.Syntax

/-!
# Ook!: parser and translators

Ook! source is a whitespace-separated sequence of the words `Ook.`, `Ook?`,
`Ook!`, read two at a time; each pair is one brainfuck command. Parsing
produces a `Langlib.Brainfuck.Prog` directly.

Unlike brainfuck, where everything unknown is a comment, Ook! has no
comments (Morgan-Mar: the code "serves perfectly well to describe in detail
what it does", provided you are an orang-utan). Parse errors, each reported
with the offending token's position:

* a word that is not one of the three Ook! words;
* an odd number of words (Morgan-Mar: "Programs must thus contain an even
  number of Ooks");
* the pair `Ook? Ook?` (give the Memory Pointer a banana), which specifies
  no machine behaviour;
* unmatched `Ook! Ook?` / `Ook? Ook!` loop pairs.
-/

namespace Langlib.Ook

open Langlib.Brainfuck (Op)

private structure Pos where
  line : Nat := 1
  col : Nat := 1

private def Pos.show (p : Pos) : String := s!"{p.line}:{p.col}"

private def Pos.advance (p : Pos) (c : Char) : Pos :=
  if c == '\n' then { line := p.line + 1, col := 1 }
  else { p with col := p.col + 1 }

/-- One token: an Ook! word with the position of its first character and
its 1-based index in the token sequence. -/
private structure Tok where
  word : Word
  pos : Pos
  idx : Nat

private def classify (w : String) (pos : Pos) : Except String Word :=
  match w with
  | "Ook." => .ok .dot
  | "Ook?" => .ok .quest
  | "Ook!" => .ok .bang
  | _ => throw s!"'{w}' at {pos.show} is not an Ook! word (expected Ook. Ook? or Ook!)"

/-- Split the source into Ook! words. Words are separated by whitespace
(line breaks are ignored, per the language page); any other word is a parse
error. -/
private def tokenize (src : String) : Except String (Array Tok) := do
  let mut toks : Array Tok := #[]
  let mut cur : String := ""
  let mut curPos : Pos := {}
  let mut pos : Pos := {}
  for c in src.toList do
    if c.isWhitespace then
      if !cur.isEmpty then
        toks := toks.push { word := ← classify cur curPos, pos := curPos, idx := toks.size + 1 }
        cur := ""
    else
      if cur.isEmpty then curPos := pos
      cur := cur.push c
    pos := pos.advance c
  if !cur.isEmpty then
    toks := toks.push { word := ← classify cur curPos, pos := curPos, idx := toks.size + 1 }
  return toks

/-- Group an even-length token list into consecutive pairs. -/
private def pairUp : List Tok → List (Tok × Tok)
  | a :: b :: rest => (a, b) :: pairUp rest
  | _ => []

/-- Parse Ook! source into a brainfuck program. -/
def parse (src : String) : Except String Prog := do
  let toks ← tokenize src
  if toks.size % 2 == 1 then
    match toks.back? with
    | some last =>
      throw s!"odd number of Ook words ({toks.size}): '{last.word.render}' at \
        {last.pos.show} (token {last.idx}) has no partner"
    | none => unreachable!
  -- As in the brainfuck parser: `cur` accumulates the current (innermost)
  -- program reversed; `stack` holds the enclosing programs, each with the
  -- token that opened it.
  let mut cur : List Op := []
  let mut stack : List (Tok × List Op) := []
  for (a, b) in pairUp toks.toList do
    match a.word, b.word with
    | .dot, .quest => cur := .right :: cur
    | .quest, .dot => cur := .left :: cur
    | .dot, .dot => cur := .inc :: cur
    | .bang, .bang => cur := .dec :: cur
    | .bang, .dot => cur := .output :: cur
    | .dot, .bang => cur := .input :: cur
    | .bang, .quest =>
      stack := (a, cur) :: stack
      cur := []
    | .quest, .bang =>
      match stack with
      | [] => throw s!"unmatched 'Ook? Ook!' at {a.pos.show} (token {a.idx})"
      | (_, outer) :: rest =>
        cur := .loop cur.reverse :: outer
        stack := rest
    | .quest, .quest =>
      throw s!"'Ook? Ook?' at {a.pos.show} (token {a.idx}): giving the \
        Memory Pointer a banana has no defined effect; see docs/ook/spec.md"
  match stack with
  | [] => return cur.reverse
  | (openTok, _) :: _ =>
    throw s!"unmatched 'Ook! Ook?' at {openTok.pos.show} (token {openTok.idx})"

/-- Translate brainfuck source to Ook! source (used to generate our `.ook`
examples from the brainfuck ones). -/
def ofBrainfuck (bf : String) : Except String String :=
  return render (← Langlib.Brainfuck.parse bf)

/-- Translate Ook! source to brainfuck source. -/
def toBrainfuck (ook : String) : Except String String :=
  return Langlib.Brainfuck.Prog.render (← parse ook)

end Langlib.Ook
