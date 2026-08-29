import Langlib.Languages.Unlambda.Syntax

/-!
# Unlambda: parser

Unlambda's concrete syntax is prefix application: `` `FG `` is `F` applied
to `G`, and no parentheses are needed because every function is unary.
Whitespace is ignored everywhere except after `.` and `?`, where the very
next byte is the character the builtin carries. A `#` starts a comment that
runs to the end of the line.

The parser scans bytes rather than characters, because that is what
Madore's interpreters do: `.x` captures one byte, so a multi-byte UTF-8
character after a dot is a dot for its first byte followed by an
unrecognised command. Errors carry a line and column (columns counted in
bytes).

There is no recursion over the input here. A prefix expression is parsed
with a stack of half-built applications: `none` is a backquote still waiting
for its operator, `some F` is an application waiting for its operand.

One deliberate difference from Madore's interpreters: they stop reading at
the end of the first complete expression and treat whatever follows as the
program's *input*, because they read program and input from the same
stream. We take the program from a file and the input from stdin, so
trailing text is a mistake rather than data, and it is reported as one.
-/

namespace Langlib.Unlambda

private structure Pos where
  line : Nat := 1
  col : Nat := 1

private def Pos.show (p : Pos) : String := s!"{p.line}:{p.col}"

private def Pos.advance (p : Pos) (b : UInt8) : Pos :=
  if b == 10 then { line := p.line + 1, col := 1 }
  else { p with col := p.col + 1 }

/-- A half-built prefix expression, together with the position of the
backquote that opened it: `none` awaits an operator, `some F` awaits `F`'s
operand. -/
private abbrev Pending := List (Pos × Option Term)

/-- Plug a finished term into the pending stack. `Sum.inl` means the whole
expression is now complete. Structural in the stack, so no fuel needed. -/
private def plug : Term → Pending → Sum Term Pending
  | t, [] => .inl t
  | t, (p, none) :: rest => .inr ((p, some t) :: rest)
  | t, (_, some f) :: rest => plug (.app f t) rest

/-- What the scanner is in the middle of. -/
private inductive Mode where
  | normal
  /-- Inside a `#` comment, skipping to the end of the line. -/
  | comment
  /-- The previous byte was `.` (`isQues = false`) or `?` (`isQues = true`),
  so this byte is the character that builtin carries. -/
  | charOf (isQues : Bool)

/-- The builtin a single byte denotes, if any.

Either case is accepted for every letter, `r` included. Madore's own
interpreters are split on `r` alone: the Java and Scheme ones take `R`, the
C and Caml ones do not. Every one of them takes `K`, `S`, `I`, `V`, `D`,
`C` and `E`, so a uniform rule has to be the permissive one. See decision 9
in `docs/unlambda/spec.md`. -/
private def builtinOf (b : UInt8) : Option Term :=
  match b with
  | 107 | 75 => some .k
  | 115 | 83 => some .s
  | 105 | 73 => some .i
  | 118 | 86 => some .v
  | 100 | 68 => some .d
  | 99  | 67 => some .c
  | 101 | 69 => some .e
  | 114 | 82 => some Term.r
  | 64  => some .at
  | 124 => some .pipe
  | _ => none

/-- How an unexpected byte is named in a parse error. Printable ASCII is
quoted; anything else is given by its number, because a program is a byte
stream and a stray byte 200 has no character to show. -/
private def describeByte (b : UInt8) : String :=
  if 32 ≤ b && b ≤ 126 then
    let shown := String.ofList [Char.ofNat b.toNat]
    s!"'{shown}'"
  else
    s!"byte {b.toNat}"

/-- Parse Unlambda source into a `Prog`.

Failure modes: an unrecognised byte, a `.` or `?` at the very end of the
input, an expression that ends with operands still missing, an empty
program, and text after the end of the expression. -/
def parse (src : String) : Except String Prog := do
  let mut stack : Pending := []
  let mut mode : Mode := .normal
  let mut pos : Pos := {}
  let mut done : Option Term := none
  for b in src.toUTF8.toList do
    let mut leaf? : Option Term := none
    match mode with
    | .comment =>
      if b == 10 then mode := .normal
    | .charOf isQues =>
      mode := .normal
      leaf? := some (if isQues then .ques b else .dot b)
    | .normal =>
      if b == 96 then
        if done.isSome then throw s!"text after the end of the program at {pos.show}"
        stack := (pos, none) :: stack
      else if b == 35 then
        mode := .comment
      else if b == 32 || b == 9 || b == 10 || b == 13 then
        pure ()
      else if b == 46 then
        if done.isSome then throw s!"text after the end of the program at {pos.show}"
        mode := .charOf false
      else if b == 63 then
        if done.isSome then throw s!"text after the end of the program at {pos.show}"
        mode := .charOf true
      else
        match builtinOf b with
        | some t => leaf? := some t
        | none =>
          throw s!"unrecognised character {describeByte b} at {pos.show}"
    match leaf? with
    | none => pure ()
    | some t =>
      if done.isSome then throw s!"text after the end of the program at {pos.show}"
      match plug t stack with
      | .inl full => done := some full; stack := []
      | .inr stack' => stack := stack'
    pos := pos.advance b
  match mode with
  | .charOf isQues =>
    let what := if isQues then "?" else "."
    throw s!"end of input after '{what}' at {pos.show}: it needs a character"
  | _ =>
    match done with
    | some t => return t
    | none =>
      match stack.getLast? with
      | none => throw "empty program: an Unlambda program is one expression"
      | some (openPos, _) =>
        throw s!"unfinished application: the '`' at {openPos.show} never got its operands"

end Langlib.Unlambda
