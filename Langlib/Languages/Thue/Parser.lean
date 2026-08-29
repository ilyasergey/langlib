import Langlib.Languages.Thue.Syntax

/-!
# Thue: parser

A Thue source file is a rulebase followed by an initial state:

* each rulebase line is `lhs::=rhs`, split at the *first* `::=` (the rhs may
  contain further `::=`s);
* the rulebase ends at the first line whose lhs is empty or whitespace-only
  (canonically a lone `::=`); that line's rhs is ignored;
* every line after the terminator is concatenated, without newlines, to form
  the initial state.

Blank and whitespace-only lines in the rulebase are skipped. A non-blank
rulebase line without `::=` is a parse error here (Colagioia's interpreter
warns on stderr and skips it; see `docs/thue/spec.md`, decision 7). Line
endings are normalised: a trailing `\r` is stripped from every line.
-/

namespace Langlib.Thue

private def stripCR (l : String) : String :=
  if l.endsWith "\r" then String.ofList l.toList.dropLast else l

/-- Classify a right-hand side: exactly `:::` reads input, a leading `~`
writes output, anything else (including the empty string) is a literal
replacement. -/
private def classifyRhs (rhs : String) : Rhs :=
  if rhs == ":::" then .input
  else if rhs.startsWith "~" then .output (String.ofList rhs.toList.tail)
  else .str rhs

private def parseLines : List String → Nat → List Rule → Except String Prog
  | [], _, _ =>
    .error "missing rules terminator (a line with an empty lhs, canonically '::=')"
  | line :: rest, n, acc =>
    if line.trimAscii.isEmpty then
      parseLines rest (n + 1) acc
    else
      match line.splitOn "::=" with
      | [_] => .error s!"line {n}: not a rule (no '::='): '{line}'"
      | lhs :: parts =>
        if lhs.trimAscii.isEmpty then
          -- Terminator: the rhs (if any) is discarded, the rest is the state.
          .ok { rules := acc.reverse, initial := String.join rest }
        else
          let rhs := String.intercalate "::=" parts
          parseLines rest (n + 1) ({ lhs, rhs := classifyRhs rhs } :: acc)
      | [] => .error s!"line {n}: internal error: empty split"

/-- Parse Thue source into a `Prog`. -/
def parse (src : String) : Except String Prog :=
  parseLines ((src.splitOn "\n").map stripCR) 1 []

end Langlib.Thue
