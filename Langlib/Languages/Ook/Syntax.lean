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

/-- The last of a word's four characters, the one that distinguishes it. -/
def lastChar : Word → Char
  | .dot => '.'
  | .quest => '?'
  | .bang => '!'

/-- The four characters of one Ook! word. -/
def wordChars (w : Word) : List Char := ['O', 'o', 'k', lastChar w]

/-- The words a program spells, in order. -/
def wordsOf (p : Prog) : List Word := p.flatMap opWords

/-- Each word followed by the whitespace character that separates it from
the next. -/
def spelled : List (Word × Char) → List Char
  | [] => []
  | (w, c) :: t => wordChars w ++ c :: spelled t

/-- The layout: a space between words, a newline after every sixteenth word
and after the last. `k` counts words already placed on the current line. -/
def renderPairs : List Word → Nat → List (Word × Char)
  | [], _ => []
  | [w], _ => [(w, '\n')]
  | w :: ws, k =>
    (w, if k == 15 then '\n' else ' ')
      :: renderPairs ws (if k == 15 then 0 else k + 1)

/-- Render a program as Ook! source: space-separated words, sixteen to a
line (the customary layout), with a trailing newline. This is the
`Prog → Ook!` direction of the brainfuck isomorphism; `parse` is its
inverse, and `Langlib.Computability.OokSyntax.parse_render` proves it.

Spelled out character by character rather than with `String.intercalate`
over a chunked list, because the chunker was necessarily `partial` and
Lean compiles a `partial def` to an opaque constant with no equations, which
no theorem can mention. This definition is structural, so the round-trip
theorem is about the string this function actually returns. -/
def render (p : Prog) : String :=
  String.ofList (spelled (renderPairs (wordsOf p) 0))

end Langlib.Ook
