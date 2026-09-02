import Langlib.Languages.Velato.Note

/-!
# Velato: abstract syntax

A Velato program is a MIDI file, and what the language reads out of it is a
sequence of pitches. This module defines what those pitches *mean* once
`Parser.lean` has grouped them: an ordinary structured imperative program
with declarations, assignment, `while`, `if`/`else`, one output command and
one input command.

Two things about the AST are worth stating up front, because they are
consequences of the encoding rather than choices.

**Variables are pitches.** A variable is named by an absolute MIDI note,
octave included, and there are 128 of those. So the AST names variables by
`Pitch` and not by `String`, and a program has at most 128 of them. This is
the one place in Velato where absolute pitch matters, and it has a
computational consequence severe enough that `docs/velato/spec.md` devotes a
section to it: the store is a bounded number of cells, so all the unbounded
storage a Velato program can have must live *inside* the cells.

**There is no expression statement and no function.** velato.net says
functions are "not yet implemented", and no released implementation has
them, so the AST has none. What it has is exactly the command table:
`Declare`, `Let`, `While`, `If`, `Else`, `Print`, `Input`, plus the two
commands that leave no trace in the tree — the unison no-op and the root
change, which `Parser.lean` consumes while scanning.

See `docs/velato/spec.md` for the note-level encoding of each of these and
for the sources behind every semantic decision.
-/

namespace Langlib.Velato

/-- Velato's three types. Declared with a variable, and thereafter fixed
until the variable is redeclared.

There is no boolean type: comparisons produce an `int`, and `while` and `if`
test an `int` against zero. That follows the reference compiler, which
emits C# and lets C# do the work — but C# has a real `bool`, so what it
actually means is that a comparison used as a value and a comparison used as
a condition are two different C# programs. `docs/velato/spec.md` explains
how the pure semantics here reconciles the two. -/
inductive Ty where
  | int
  | char
  | double
deriving Repr, BEq, DecidableEq, Inhabited

/-- The name a type has in diagnostics and in the disassembler. -/
def Ty.name : Ty → String
  | .int => "int"
  | .char => "char"
  | .double => "double"

/-- Binary operators, in the two families the note encoding separates them
into: comparisons and logic reached through a 2nd, arithmetic through a
perfect 5th. -/
inductive BinOp where
  | add | sub | mul | div | mod
  | eq | gt | lt
  | and | or
deriving Repr, BEq, DecidableEq, Inhabited

/-- The C# spelling of an operator, which is also how the disassembler
prints it. Kept next to the operator because the reference implementation's
semantics *is* the generated C#. -/
def BinOp.symbol : BinOp → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .mod => "%"
  | .eq => "==" | .gt => ">" | .lt => "<"
  | .and => "&&" | .or => "||"

/-- Binding tightness, taken from C#'s operator precedence, because the
reference compiler emits an unparenthesised C# expression and lets the C#
compiler group it. Higher binds tighter. -/
def BinOp.prec : BinOp → Nat
  | .mul | .div | .mod => 6
  | .add | .sub => 5
  | .lt | .gt => 4
  | .eq => 3
  | .and => 2
  | .or => 1

/-- The only unary operator: logical negation, written as a 2nd followed by
a 5th. velato.net notes that it is what spells `≥` (as `NOT <`) and `≠`
(as `NOT =`), which is why the language needs no separate tokens for
those. -/
inductive UnOp where
  | not
deriving Repr, BEq, DecidableEq, Inhabited

/-- Expressions.

`doubleLit` keeps the literal in the shape the notes wrote it — a sign, a
run of digits, a decimal point, another run of digits — rather than as a
`Float`. Two reasons: the AST stays decidably equal, which the tests rely
on, and the conversion to a floating-point value happens once, in the
semantics, where the decision can be documented and pointed at. -/
inductive Expr where
  /-- A variable, named by the absolute pitch of a single note. -/
  | var (p : Pitch)
  /-- An `int` literal. Negative literals have their own note encoding, so
  the sign is already folded in here. -/
  | intLit (n : Int)
  /-- A `char` literal, written in the source as its ASCII code. -/
  | charLit (code : Int)
  /-- A `double` literal: sign, integer digits, fractional digits. -/
  | doubleLit (negative : Bool) (intDigits fracDigits : List Nat)
  | un (op : UnOp) (e : Expr)
  | bin (op : BinOp) (l r : Expr)
deriving Repr, BEq, DecidableEq, Inhabited

/-- Statements.

`ite` carries both branches because `Else` is a command in its own right in
the note encoding but a branch in every reasonable semantics; the parser
does the folding. A program with no `else` gets an empty `els`. -/
inductive Stmt where
  /-- `Declare`: give a pitch a type. Redeclaring erases the old value. -/
  | declare (v : Pitch) (ty : Ty)
  /-- `Let`: assign an expression to a pitch. -/
  | assign (v : Pitch) (e : Expr)
  /-- `Print`: write an expression to the output. -/
  | print (e : Expr)
  /-- `Input`: read one character into a pitch. -/
  | input (v : Pitch)
  | while (cond : Expr) (body : List Stmt)
  | ite (cond : Expr) (thn els : List Stmt)
deriving Repr, Inhabited

/-- A Velato program: the statements the notes spelled out, in order. -/
abbrev Prog := List Stmt

/-! ## Rendering

The runner's `--ast` flag prints this, which is what a composer checks to
see whether the piece they wrote says what they meant. The reference
compiler offers the same service by printing its syntax tree, and
velato.net's Hello World walkthrough leans on it heavily. -/

/-- Parenthesise `s` when the operator inside binds more loosely than the
context calls for. -/
private def paren (b : Bool) (s : String) : String := if b then "(" ++ s ++ ")" else s

/-- A digit run as a numeral, or `"0"` when empty. -/
private def digitsToString (ds : List Nat) : String :=
  if ds.isEmpty then "0" else String.join (ds.map toString)

/-- Pretty-print an expression at precedence `ctx`, inserting exactly the
parentheses that are needed to read it back. -/
def Expr.render (e : Expr) (ctx : Nat := 0) : String :=
  match e with
  | .var p => p.name
  | .intLit n => toString n
  | .charLit c =>
    if 32 ≤ c && c ≤ 126 then "'" ++ String.singleton (Char.ofNat c.toNat) ++ "'"
    else "char(" ++ toString c ++ ")"
  | .doubleLit neg i f =>
    (if neg then "-" else "") ++ digitsToString i ++ "." ++ digitsToString f
  | .un .not e => "!" ++ e.render 7
  | .bin op l r =>
    paren (op.prec < ctx)
      (l.render op.prec ++ " " ++ op.symbol ++ " " ++ r.render (op.prec + 1))

mutual

/-- Pretty-print a statement, indented by `ind` spaces. -/
def Stmt.render (ind : Nat) : Stmt → String
  | .declare v ty => "".pushn ' ' ind ++ ty.name ++ " " ++ v.name ++ ";"
  | .assign v e => "".pushn ' ' ind ++ v.name ++ " = " ++ e.render ++ ";"
  | .print e => "".pushn ' ' ind ++ "print(" ++ e.render ++ ");"
  | .input v => "".pushn ' ' ind ++ v.name ++ " = input();"
  | .while c body =>
    "".pushn ' ' ind ++ "while (" ++ c.render ++ ") {\n"
      ++ Stmt.renderList (ind + 2) body ++ "".pushn ' ' ind ++ "}"
  | .ite c thn els =>
    let head :=
      "".pushn ' ' ind ++ "if (" ++ c.render ++ ") {\n"
        ++ Stmt.renderList (ind + 2) thn ++ "".pushn ' ' ind ++ "}"
    if els.isEmpty then head
    else head ++ " else {\n" ++ Stmt.renderList (ind + 2) els ++ "".pushn ' ' ind ++ "}"

/-- Pretty-print a block, one statement per line. -/
def Stmt.renderList (ind : Nat) : List Stmt → String
  | [] => ""
  | s :: ss => Stmt.render ind s ++ "\n" ++ Stmt.renderList ind ss

end

/-- The whole program, as the runner's `--ast` prints it. -/
def Prog.render (p : Prog) : String := Stmt.renderList 0 p

end Langlib.Velato
