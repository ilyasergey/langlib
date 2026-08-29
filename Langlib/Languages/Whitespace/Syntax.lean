/-!
# Whitespace: abstract syntax

Whitespace (Edwin Brady and Chris Morris, 2003) is a stack machine whose
concrete syntax uses only spaces, tabs, and linefeeds. The abstract syntax
below is the instruction set of `wspace` 0.3, the authors' interpreter:
stack manipulation, arithmetic, heap access, flow control, and I/O.

See `docs/whitespace/spec.md` for the language specification and the exact
semantic choices.
-/

namespace Langlib.Whitespace

/-- A label is an uninterpreted sequence of `[Space]`/`[Tab]` tokens, spelled
here as a string of `'S'` and `'T'` characters. Labels are compared as token
strings, so `[Space][LF]` and `[Space][Space][LF]` are distinct labels and
the empty label is legal. -/
abbrev Label := String

/-- Pretty-print a label for error messages, e.g. `[Space][Tab]`. -/
def Label.pretty (l : Label) : String :=
  if l.isEmpty then "[empty]"
  else l.foldl (fun acc c => acc ++ if c == 'T' then "[Tab]" else "[Space]") ""

/-- One Whitespace instruction. Numbers are arbitrary-precision integers;
`copy` and `slide` take their count as a (signed) number literal, as in
`wspace` 0.3. -/
inductive Instr where
  /-- `[Space][Space] n` : push `n` onto the stack. -/
  | push (n : Int)
  /-- `[Space][LF][Space]` : duplicate the top stack item. -/
  | dup
  /-- `[Space][Tab][Space] n` : copy the `n`-th stack item (0 = top) onto
  the top (v0.3). -/
  | copy (n : Int)
  /-- `[Space][LF][Tab]` : swap the top two stack items. -/
  | swap
  /-- `[Space][LF][LF]` : discard the top stack item. -/
  | drop
  /-- `[Space][Tab][LF] n` : slide `n` items off the stack, keeping the top
  (v0.3). -/
  | slide (n : Int)
  /-- `[Tab][Space][Space][Space]` : pop `b`, pop `a`, push `a + b`. -/
  | add
  /-- `[Tab][Space][Space][Tab]` : pop `b`, pop `a`, push `a - b`. -/
  | sub
  /-- `[Tab][Space][Space][LF]` : pop `b`, pop `a`, push `a * b`. -/
  | mul
  /-- `[Tab][Space][Tab][Space]` : pop `b`, pop `a`, push `a div b`
  (rounding toward negative infinity). -/
  | div
  /-- `[Tab][Space][Tab][Tab]` : pop `b`, pop `a`, push `a mod b` (sign of
  the divisor). -/
  | mod
  /-- `[Tab][Tab][Space]` : pop a value, pop an address, store the value at
  the address. -/
  | store
  /-- `[Tab][Tab][Tab]` : pop an address, push the value stored there. -/
  | retrieve
  /-- `[LF][Space][Space] l` : mark this program point with label `l`. -/
  | label (l : Label)
  /-- `[LF][Space][Tab] l` : call the subroutine at label `l`. -/
  | call (l : Label)
  /-- `[LF][Space][LF] l` : jump unconditionally to label `l`. -/
  | jump (l : Label)
  /-- `[LF][Tab][Space] l` : pop a value; jump to `l` if it is zero. -/
  | jz (l : Label)
  /-- `[LF][Tab][Tab] l` : pop a value; jump to `l` if it is negative. -/
  | jn (l : Label)
  /-- `[LF][Tab][LF]` : return from the current subroutine. -/
  | ret
  /-- `[LF][LF][LF]` : end the program. -/
  | halt
  /-- `[Tab][LF][Space][Space]` : pop a value, output it as a character. -/
  | outChar
  /-- `[Tab][LF][Space][Tab]` : pop a value, output it as a decimal
  number. -/
  | outNum
  /-- `[Tab][LF][Tab][Space]` : pop an address, read one character, store
  its code at the address. -/
  | readChar
  /-- `[Tab][LF][Tab][Tab]` : pop an address, read one line, parse a
  decimal number, store it at the address. -/
  | readNum
deriving Repr, BEq, Inhabited

/-- A Whitespace program, flattened: jumps target label instructions by
position. -/
abbrev Prog := Array Instr

/-- Encode a number literal: sign token, binary digits (most significant
first), `[LF]` terminator. Zero is encoded with a single 0 digit. -/
def encodeNum (n : Int) : String :=
  let sign := if n < 0 then "\t" else " "
  let digits := (Nat.toDigits 2 n.natAbs).map fun c => if c == '1' then '\t' else ' '
  sign ++ String.ofList digits ++ "\n"

/-- Encode a label: its tokens (`'T'` as tab, anything else as space)
followed by the `[LF]` terminator. -/
def encodeLabel (l : Label) : String :=
  String.ofList (l.toList.map fun c => if c == 'T' then '\t' else ' ') ++ "\n"

/-- Render an instruction back to concrete syntax (used to generate the
example programs, by tests, and later by the Turpentine compiler). -/
def Instr.render : Instr → String
  | .push n => "  " ++ encodeNum n
  | .dup => " \n "
  | .copy n => " \t " ++ encodeNum n
  | .swap => " \n\t"
  | .drop => " \n\n"
  | .slide n => " \t\n" ++ encodeNum n
  | .add => "\t   "
  | .sub => "\t  \t"
  | .mul => "\t  \n"
  | .div => "\t \t "
  | .mod => "\t \t\t"
  | .store => "\t\t "
  | .retrieve => "\t\t\t"
  | .label l => "\n  " ++ encodeLabel l
  | .call l => "\n \t" ++ encodeLabel l
  | .jump l => "\n \n" ++ encodeLabel l
  | .jz l => "\n\t " ++ encodeLabel l
  | .jn l => "\n\t\t" ++ encodeLabel l
  | .ret => "\n\t\n"
  | .halt => "\n\n\n"
  | .outChar => "\t\n  "
  | .outNum => "\t\n \t"
  | .readChar => "\t\n\t "
  | .readNum => "\t\n\t\t"

/-- Render a program to concrete syntax. -/
def Prog.render (p : Prog) : String :=
  p.foldl (fun acc i => acc ++ i.render) ""

end Langlib.Whitespace
