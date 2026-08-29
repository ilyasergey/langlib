import Std.Data.HashMap
import Langlib.Languages.Subleq.Syntax

/-!
# Subleq: assembler

Raw subleq is a list of numbers; nobody writes that by hand twice. This
module implements the thin assembler format documented in
`docs/subleq/spec.md`:

* a source file is a whitespace-separated sequence of word tokens; the
  assembled program is exactly those words in order (no instruction
  grouping, no operand-count shorthand);
* comments run from `#` or `;` to end of line;
* tokens are integer literals (`72`, `-1`), label definitions (`name:`),
  label references (`name`), and `?` (the address of the cell the token
  itself occupies), the last two optionally with a `+N`/`-N` offset.

Errors (bad token, undefined label, duplicate label) carry line and
column.
-/

namespace Langlib.Subleq

private structure Pos where
  line : Nat := 1
  col : Nat := 1

private def Pos.show (p : Pos) : String := s!"{p.line}:{p.col}"

private def Pos.advance (p : Pos) (c : Char) : Pos :=
  if c == '\n' then { line := p.line + 1, col := 1 }
  else { p with col := p.col + 1 }

/-- Raw tokens: `name:` versus everything else (classified later). -/
private inductive RawTok where
  | labelDef (name : String)
  | word (text : String)

/-- A word token, classified: a literal, or a reference (`name` or `?`)
plus offset. -/
private inductive Item where
  | lit (v : Int)
  | ref (name : String) (off : Int)
deriving Inhabited

private def isIdentStart (c : Char) : Bool := c.isAlpha || c == '_'
private def isIdentChar (c : Char) : Bool := c.isAlphanum || c == '_'

private def isIdent (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => isIdentStart c && cs.all isIdentChar

/-- Split source text into raw tokens with positions. A `:` closes the
token before it as a label definition, so `msg:72` is `msg:` then `72`. -/
private def tokenize (src : String) : Except String (Array (Pos × RawTok)) := do
  let mut toks : Array (Pos × RawTok) := #[]
  let mut cur := ""
  let mut curPos : Pos := {}
  let mut pos : Pos := {}
  let mut inComment := false
  for c in src.toList do
    if inComment then
      if c == '\n' then inComment := false
    else if c == '#' || c == ';' then
      if cur ≠ "" then toks := toks.push (curPos, .word cur); cur := ""
      inComment := true
    else if c == ':' then
      if cur == "" then throw s!"{pos.show}: ':' without a label name"
      toks := toks.push (curPos, .labelDef cur)
      cur := ""
    else if c.isWhitespace then
      if cur ≠ "" then toks := toks.push (curPos, .word cur); cur := ""
    else
      if cur == "" then curPos := pos
      cur := cur.push c
    pos := pos.advance c
  if cur ≠ "" then toks := toks.push (curPos, .word cur)
  return toks

/-- Classify one word token; `none` means a malformed token. -/
private def parseWord (s : String) : Option Item :=
  match s.toInt? with
  | some v => some (.lit v)
  | none =>
    let cs := s.toList
    let (base, rest) :=
      match cs with
      | '?' :: rest => ("?", rest)
      | _ =>
        let b := cs.takeWhile isIdentChar
        (String.ofList b, cs.drop b.length)
    if base != "?" && !isIdent base then none
    else
      let offset : List Char → Option Int := fun ds =>
        if ds.isEmpty || !ds.all Char.isDigit then none
        else (String.ofList ds).toNat?.map Int.ofNat
      match rest with
      | [] => some (.ref base 0)
      | '+' :: ds => (offset ds).map (.ref base ·)
      | '-' :: ds => (offset ds).map (fun n => .ref base (-n))
      | _ => none

/-- Assemble source text into a memory image. Two passes: collect label
addresses and classify words, then resolve references. -/
def assemble (src : String) : Except String Prog := do
  let toks ← tokenize src
  let mut labels : Std.HashMap String Nat := {}
  let mut words : Array (Pos × Item) := #[]
  for (pos, t) in toks do
    match t with
    | .labelDef name =>
      if !isIdent name then
        throw s!"{pos.show}: invalid label name '{name}'"
      if labels.contains name then
        throw s!"{pos.show}: duplicate label '{name}'"
      labels := labels.insert name words.size
    | .word s =>
      match parseWord s with
      | some item => words := words.push (pos, item)
      | none => throw s!"{pos.show}: bad token '{s}'"
  let mut out : Prog := #[]
  let mut addr : Nat := 0
  for (pos, item) in words do
    match item with
    | .lit v => out := out.push v
    | .ref "?" off => out := out.push ((addr : Int) + off)
    | .ref name off =>
      match labels[name]? with
      | some a => out := out.push ((a : Int) + off)
      | none => throw s!"{pos.show}: undefined label '{name}'"
    addr := addr + 1
  return out

end Langlib.Subleq
