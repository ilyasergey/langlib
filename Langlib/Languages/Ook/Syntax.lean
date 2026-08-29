import Langlib.Languages.Brainfuck.Syntax

/-!
# Ook!: abstract syntax and rendering

Ook! (David Morgan-Mar, 2001) is brainfuck for orang-utans: the same eight
commands, spelled as pairs of the words `Ook.`, `Ook?`, `Ook!`. Since the
isomorphism is exact, Ook! has no AST of its own: parsing produces a
`Langlib.Brainfuck.Prog` and evaluation delegates to the brainfuck core.

This module defines the Ook! vocabulary (`Word`), the pair encoding of each
brainfuck command, and the renderer `render : Prog → String`, the inverse of
`Langlib.Ook.parse`. Our `.ook` example files are generated mechanically
with `render` from the corresponding brainfuck examples.

See `docs/ook/spec.md` for the language specification and the exact
semantic decisions.
-/

namespace Langlib.Ook

open Langlib.Brainfuck (Op)

/-- Ook! programs *are* brainfuck programs; only the concrete syntax
differs. -/
abbrev Prog := Langlib.Brainfuck.Prog

/-- The entire Ook! vocabulary: three words, distinguished by inflection. -/
inductive Word where
  /-- `Ook.` -/
  | dot
  /-- `Ook?` -/
  | quest
  /-- `Ook!` -/
  | bang
deriving Repr, BEq, Inhabited

def Word.render : Word → String
  | .dot => "Ook."
  | .quest => "Ook?"
  | .bang => "Ook!"

/-- The word pair encoding one primitive brainfuck command, and the opening
and closing pairs of a loop. `Ook? Ook?` (give the Memory Pointer a banana)
encodes nothing; see the spec page. -/
def opWords : Op → List Word
  | .right => [.dot, .quest]
  | .left => [.quest, .dot]
  | .inc => [.dot, .dot]
  | .dec => [.bang, .bang]
  | .input => [.dot, .bang]
  | .output => [.bang, .dot]
  | .loop body => [.bang, .quest] ++ body.flatMap opWords ++ [.quest, .bang]

/-- Split a list into chunks of `n` (the last may be shorter). -/
private partial def chunks (n : Nat) : List α → List (List α)
  | [] => []
  | xs => xs.take n :: chunks n (xs.drop n)

/-- Render a program as Ook! source: space-separated words, sixteen to a
line (the customary layout), with a trailing newline. This is the
`Prog → Ook!` direction of the brainfuck isomorphism; `parse` is its
inverse. -/
def render (p : Prog) : String :=
  let ws := (p.flatMap opWords).map Word.render
  if ws.isEmpty then ""
  else String.intercalate "\n" ((chunks 16 ws).map (String.intercalate " ")) ++ "\n"

end Langlib.Ook
