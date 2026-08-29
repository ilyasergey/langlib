import Langlib.Languages.Whitespace.Syntax

/-!
# Whitespace: parser

Tokenisation keeps exactly space (0x20), tab (0x09), and LF (0x0A); every
other character, carriage return included, is a comment. Parsing then reads
IMP-prefixed instructions, following `wspace` 0.3's grammar. Errors report
the source line and column of the offending instruction and show the tokens
as `[Space]`/`[Tab]`/`[LF]`, since showing the characters themselves would
be a little too faithful to the language.
-/

namespace Langlib.Whitespace

/-- The three meaningful characters. -/
private inductive Tok where
  | s -- space
  | t -- tab
  | l -- linefeed
deriving BEq

private def Tok.pretty : Tok → String
  | .s => "[Space]"
  | .t => "[Tab]"
  | .l => "[LF]"

/-- A token together with the source position of its character. -/
private structure TokP where
  tok : Tok
  line : Nat
  col : Nat

private def TokP.posStr (t : TokP) : String := s!"{t.line}:{t.col}"

/-- Keep the whitespace, drop the rest. -/
private def tokenize (src : String) : List TokP := Id.run do
  let mut out : List TokP := []
  let mut line := 1
  let mut col := 1
  for c in src.toList do
    match c with
    | ' ' => out := ⟨.s, line, col⟩ :: out
    | '\t' => out := ⟨.t, line, col⟩ :: out
    | '\n' => out := ⟨.l, line, col⟩ :: out
    | _ => pure ()
    if c == '\n' then
      line := line + 1
      col := 1
    else
      col := col + 1
  return out.reverse

/-- Show the first few remaining tokens, for "unrecognised instruction"
messages. -/
private def preview (ts : List TokP) : String :=
  let shown := ts.take 4 |>.map (fun t => t.tok.pretty) |> String.join
  if ts.length > 4 then shown ++ "..."
  else if ts.length < 4 then shown ++ "[end of program]"
  else shown

/-- Parse a number literal: sign token, binary digits, `[LF]` terminator.
`at_` is the position of the instruction that needs the number. -/
private def parseNum (at_ : String) (ts : List TokP) :
    Except String (Int × List TokP) := do
  match ts with
  | [] => throw s!"number after instruction at {at_} is unterminated at end of program"
  | ⟨.l, _, _⟩ :: _ =>
    throw s!"number after instruction at {at_} is missing its sign token"
  | sign :: rest =>
    let neg := sign.tok == .t
    -- Accumulate the magnitude, most significant digit first.
    let rec go (acc : Nat) : List TokP → Except String (Nat × List TokP)
      | [] => throw s!"number after instruction at {at_} is unterminated at end of program"
      | ⟨.l, _, _⟩ :: rest => .ok (acc, rest)
      | ⟨.t, _, _⟩ :: rest => go (2 * acc + 1) rest
      | ⟨.s, _, _⟩ :: rest => go (2 * acc) rest
    let (mag, rest) ← go 0 rest
    let n : Int := if neg then -(mag : Int) else (mag : Int)
    return (n, rest)

/-- Parse a label: `[Space]`/`[Tab]` tokens up to the `[LF]` terminator. -/
private def parseLabel (at_ : String) : List TokP → Except String (Label × List TokP)
  | [] => throw s!"label after instruction at {at_} is unterminated at end of program"
  | ⟨.l, _, _⟩ :: rest => .ok ("", rest)
  | ⟨tk, _, _⟩ :: rest => do
    let (l, rest) ← parseLabel at_ rest
    return (String.singleton (if tk == .t then 'T' else 'S') ++ l, rest)

/-- Parse one instruction stream. `fuel` is a termination measure only:
every instruction consumes at least two tokens, so `ts.length` suffices and
the zero case is unreachable on real input. -/
private def parseGo : Nat → List TokP → Except String (List Instr)
  | 0, [] => .ok []
  | 0, t :: _ => throw s!"internal parser error at {t.posStr}"
  | _ + 1, [] => .ok []
  | fuel + 1, ts@(first :: _) => do
    let at_ := first.posStr
    let cont (i : Instr) (rest : List TokP) : Except String (List Instr) := do
      let is ← parseGo fuel rest
      return i :: is
    match ts with
    -- Stack manipulation: IMP [Space]
    | ⟨.s,_,_⟩ :: ⟨.s,_,_⟩ :: rest =>
      let (n, rest) ← parseNum at_ rest
      cont (.push n) rest
    | ⟨.s,_,_⟩ :: ⟨.t,_,_⟩ :: ⟨.s,_,_⟩ :: rest =>
      let (n, rest) ← parseNum at_ rest
      cont (.copy n) rest
    | ⟨.s,_,_⟩ :: ⟨.t,_,_⟩ :: ⟨.l,_,_⟩ :: rest =>
      let (n, rest) ← parseNum at_ rest
      cont (.slide n) rest
    | ⟨.s,_,_⟩ :: ⟨.l,_,_⟩ :: ⟨.s,_,_⟩ :: rest => cont .dup rest
    | ⟨.s,_,_⟩ :: ⟨.l,_,_⟩ :: ⟨.t,_,_⟩ :: rest => cont .swap rest
    | ⟨.s,_,_⟩ :: ⟨.l,_,_⟩ :: ⟨.l,_,_⟩ :: rest => cont .drop rest
    -- Arithmetic: IMP [Tab][Space]
    | ⟨.t,_,_⟩ :: ⟨.s,_,_⟩ :: ⟨.s,_,_⟩ :: ⟨.s,_,_⟩ :: rest => cont .add rest
    | ⟨.t,_,_⟩ :: ⟨.s,_,_⟩ :: ⟨.s,_,_⟩ :: ⟨.t,_,_⟩ :: rest => cont .sub rest
    | ⟨.t,_,_⟩ :: ⟨.s,_,_⟩ :: ⟨.s,_,_⟩ :: ⟨.l,_,_⟩ :: rest => cont .mul rest
    | ⟨.t,_,_⟩ :: ⟨.s,_,_⟩ :: ⟨.t,_,_⟩ :: ⟨.s,_,_⟩ :: rest => cont .div rest
    | ⟨.t,_,_⟩ :: ⟨.s,_,_⟩ :: ⟨.t,_,_⟩ :: ⟨.t,_,_⟩ :: rest => cont .mod rest
    -- Heap access: IMP [Tab][Tab]
    | ⟨.t,_,_⟩ :: ⟨.t,_,_⟩ :: ⟨.s,_,_⟩ :: rest => cont .store rest
    | ⟨.t,_,_⟩ :: ⟨.t,_,_⟩ :: ⟨.t,_,_⟩ :: rest => cont .retrieve rest
    -- I/O: IMP [Tab][LF]
    | ⟨.t,_,_⟩ :: ⟨.l,_,_⟩ :: ⟨.s,_,_⟩ :: ⟨.s,_,_⟩ :: rest => cont .outChar rest
    | ⟨.t,_,_⟩ :: ⟨.l,_,_⟩ :: ⟨.s,_,_⟩ :: ⟨.t,_,_⟩ :: rest => cont .outNum rest
    | ⟨.t,_,_⟩ :: ⟨.l,_,_⟩ :: ⟨.t,_,_⟩ :: ⟨.s,_,_⟩ :: rest => cont .readChar rest
    | ⟨.t,_,_⟩ :: ⟨.l,_,_⟩ :: ⟨.t,_,_⟩ :: ⟨.t,_,_⟩ :: rest => cont .readNum rest
    -- Flow control: IMP [LF]
    | ⟨.l,_,_⟩ :: ⟨.s,_,_⟩ :: ⟨.s,_,_⟩ :: rest =>
      let (l, rest) ← parseLabel at_ rest
      cont (.label l) rest
    | ⟨.l,_,_⟩ :: ⟨.s,_,_⟩ :: ⟨.t,_,_⟩ :: rest =>
      let (l, rest) ← parseLabel at_ rest
      cont (.call l) rest
    | ⟨.l,_,_⟩ :: ⟨.s,_,_⟩ :: ⟨.l,_,_⟩ :: rest =>
      let (l, rest) ← parseLabel at_ rest
      cont (.jump l) rest
    | ⟨.l,_,_⟩ :: ⟨.t,_,_⟩ :: ⟨.s,_,_⟩ :: rest =>
      let (l, rest) ← parseLabel at_ rest
      cont (.jz l) rest
    | ⟨.l,_,_⟩ :: ⟨.t,_,_⟩ :: ⟨.t,_,_⟩ :: rest =>
      let (l, rest) ← parseLabel at_ rest
      cont (.jn l) rest
    | ⟨.l,_,_⟩ :: ⟨.t,_,_⟩ :: ⟨.l,_,_⟩ :: rest => cont .ret rest
    | ⟨.l,_,_⟩ :: ⟨.l,_,_⟩ :: ⟨.l,_,_⟩ :: rest => cont .halt rest
    | _ =>
      throw s!"unrecognised instruction at {at_}: {preview ts}"

/-- Parse Whitespace source into a `Prog`. -/
def parse (src : String) : Except String Prog := do
  let ts := tokenize src
  let is ← parseGo (ts.length + 1) ts
  return is.toArray

end Langlib.Whitespace
