import Langlib.Languages.JavaGen.Validation

/-!
# JavaGen: lexer, parser and loader

The parser is total. Recursion guards come from source length and token
count; they are unrelated to the interpreter's fuel or growing types.
The fixed binder is `x`, the fixed nullary constructor is `Z`, and comments
start with `//`. See `docs/javagen/spec.md` for the complete grammar.
-/

namespace Langlib.JavaGen
namespace Parser

structure Token where
  text : String
  line : Nat
  column : Nat
deriving Repr, Inhabited

private def lexGo : Nat → List Char → Nat → Nat → List Token →
    Except String (List Token)
  | 0, _, _, _, _ => .error "lexer exhausted its source-length bound"
  | fuel + 1, cs, line, column, acc => do
    match cs with
    | [] => return acc.reverse
    | '\n' :: rest => lexGo fuel rest (line + 1) 1 acc
    | '/' :: '/' :: rest =>
      lexGo fuel (rest.dropWhile (· != '\n')) line column acc
    | '<' :: ':' :: rest =>
      lexGo fuel rest line (column + 2) (⟨"<:", line, column⟩ :: acc)
    | c :: rest =>
      if c == ' ' || c == '\t' || c == '\r' then
        lexGo fuel rest line (column + 1) acc
      else if identStart c then
        let letters := c :: rest.takeWhile identRest
        lexGo fuel (rest.dropWhile identRest) line (column + letters.length)
          (⟨String.ofList letters, line, column⟩ :: acc)
      else if "<>{},;".toList.contains c then
        lexGo fuel rest line (column + 1) (⟨String.singleton c, line, column⟩ :: acc)
      else throw s!"{line}:{column}: unexpected character '{c}'"

def lex (src : String) : Except String (List Token) :=
  lexGo (src.length + 1) src.toList 1 1 []

abbrev P := StateT (List Token) (Except String)

private def fail (msg : String) : P α := do
  match ← get with
  | [] => throw s!"end of input: {msg}"
  | t :: _ => throw s!"{t.line}:{t.column}: {msg} (found '{t.text}')"

private def isNext (s : String) : P Bool := do
  return (← get).head?.any (·.text == s)

private def take : P String := do
  match ← get with
  | [] => fail "expected a token"
  | t :: rest => set rest; return t.text

private def expect (s : String) : P Unit := do
  unless ← isNext s do fail s!"expected '{s}'"
  let _ ← take

private def name : P String := do
  match ← get with
  | t :: _ =>
    unless validName t.text do fail "expected a constructor name"
    take
  | [] => fail "expected a constructor name"

private def type (allowVar : Bool) : Nat → P Template
  | 0 => fail "type exceeded its token-count bound"
  | fuel + 1 => do
    if ← isNext "Z" then
      expect "Z"
      return ⟨[], .zero⟩
    else if ← isNext "x" then
      unless allowVar do fail "query types must be closed (no 'x')"
      expect "x"
      return ⟨[], .var⟩
    else if ← isNext "answer" then
      if allowVar then fail "'answer' is allowed only in a query"
      expect "answer"
      return ⟨[], .var⟩
    else
      let n ← name
      expect "<"
      let arg ← type allowVar fuel
      expect ">"
      return ⟨n :: arg.ctors, arg.tail⟩

private def moreBases (bound : Nat) : Nat → P (List Template)
  | 0 => fail "superclasses exceeded their token-count bound"
  | fuel + 1 => do
    if ← isNext "," then
      expect ","
      let t ← type true bound
      return t :: (← moreBases bound fuel)
    else return []

private def decl (bound : Nat) : P Decl := do
  expect "interface"
  let n ← name
  expect "<"
  expect "x"
  expect ">"
  let mut bases := []
  if ← isNext "extends" then
    expect "extends"
    let first ← type true bound
    bases := first :: (← moreBases bound bound)
  expect "{"
  expect "}"
  return ⟨n, bases⟩

private def decls (bound : Nat) : Nat → P (List Decl)
  | 0 => fail "declarations exceeded their token-count bound"
  | fuel + 1 => do
    if ← isNext "interface" then
      let d ← decl bound
      return d :: (← decls bound fuel)
    else return []

private def program (bound : Nat) : P Program := do
  expect "zero"
  expect "Z"
  expect ";"
  let classes ← decls bound bound
  expect "check"
  let lhs ← type false bound
  expect "<:"
  let rhs ← type false bound
  expect ";"
  unless (← get).isEmpty do fail "unexpected trailing token"
  if lhs.tail == .var && rhs.tail == .var then fail "only one answer hole is allowed"
  let answerSide := if lhs.tail == .var then some Side.lhs
    else if rhs.tail == .var then some Side.rhs else none
  return { classes, query := ⟨lhs.ctors, rhs.ctors⟩, answerSide }

end Parser

/-- Parse concrete syntax, retaining declaration order. Validation is separate. -/
def parseSyntax (src : String) : Except String Program := do
  let tokens ← Parser.lex src
  return (← Parser.program (tokens.length + 1) tokens).1

/-- The loader: syntax, scope, variance, acyclicity and unique instantiation. -/
def parse (src : String) : Except String Prepared := do
  prepare (← parseSyntax src)

end Langlib.JavaGen
