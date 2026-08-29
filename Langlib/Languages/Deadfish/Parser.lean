import Langlib.Languages.Deadfish.Syntax

/-!
# Deadfish: parser

The commands are the lowercase characters `i`, `d`, `s`, `o`; every other
character (including `I`, `D`, `S`, `O`, whitespace, and newlines) is
`noise`, which at run time prints a bare newline, as in Skinner's original C
interpreter. Parsing therefore cannot fail: Deadfish is the only langlib
language in which every string is a program. The `Except` in the signature
is for uniformity with the shared runner and test harness.
-/

namespace Langlib.Deadfish

/-- Classify one character. -/
def Cmd.ofChar : Char → Cmd
  | 'i' => .inc
  | 'd' => .dec
  | 's' => .square
  | 'o' => .output
  | _ => .noise

/-- Parse Deadfish source. Never fails. -/
def parse (src : String) : Except String Prog :=
  .ok (src.toList.map Cmd.ofChar)

end Langlib.Deadfish
