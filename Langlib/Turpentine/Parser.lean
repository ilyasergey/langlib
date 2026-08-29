import Langlib.Turpentine.Syntax

/-!
# Turpentine: parser

Hand-rolled lexer and recursive-descent parser for the Dafny-flavoured
concrete syntax of Turpentine. The grammar (also in `docs/turpentine/spec.md`):

```
program  ::= decl* stmt*
decl     ::= "var" ident ":" ("int" | "bool") (":=" expr)? ";"
stmt     ::= ident ":=" ("readInt" "(" ")" | "readByte" "(" ")" | expr) ";"
           | "if" expr block ("else" (block | ifstmt))?
           | "while" expr ("invariant" expr)* ("decreases" expr)? block
           | "assert" expr ";"
           | ("print" | "println") "(" (string | expr)? ")" ";"
           | "printByte" "(" expr ")" ";"
block    ::= "{" stmt* "}"
expr     ::= precedence climbing over
             ("||") < ("&&") < (== != < <= > >=) < (+ -) < (* / %) < unary
```

Comments run from `//` to end of line. Declarations come first; a `var`
after the first statement is a parse error (one flat scope, see the spec).
-/

namespace Langlib.Turpentine

namespace Parser

structure Pos where
  line : Nat := 1
  col : Nat := 1
deriving Repr, Inhabited

def Pos.show (p : Pos) : String := s!"{p.line}:{p.col}"

inductive Tok where
  | ident (s : String)
  | int (n : Nat)
  | str (s : String)
  | kw (s : String)
  | sym (s : String)
deriving Repr, BEq, Inhabited

def Tok.show : Tok → String
  | .ident s => s!"identifier '{s}'"
  | .int n => s!"integer {n}"
  | .str _ => "string literal"
  | .kw s => s!"'{s}'"
  | .sym s => s!"'{s}'"

def keywords : List String :=
  ["var", "int", "bool", "true", "false", "if", "else", "while",
   "invariant", "decreases", "assert", "print", "println", "printByte",
   "readInt", "readByte"]

/-- Tokenize; `partial` because it recurses on a shrinking char list, which
is clearly terminating but not structurally so after multi-char tokens. -/
partial def lex (src : String) : Except String (Array (Tok × Pos)) :=
  go src.toList {} #[]
where
  go (cs : List Char) (p : Pos) (acc : Array (Tok × Pos)) :
      Except String (Array (Tok × Pos)) := do
    match cs with
    | [] => return acc
    | c :: rest =>
      let adv (n : Nat) : Pos := { p with col := p.col + n }
      if c == '\n' then
        go rest { line := p.line + 1, col := 1 } acc
      else if c == ' ' || c == '\t' || c == '\r' then
        go rest (adv 1) acc
      else if c == '/' && rest.head? == some '/' then
        let rest' := rest.dropWhile (· ≠ '\n')
        go rest' p acc  -- newline handled on the next iteration
      else if c.isDigit then
        let digits := (c :: rest.takeWhile (·.isDigit))
        let rest' := rest.dropWhile (·.isDigit)
        let n := String.ofList digits |>.toNat!
        go rest' (adv digits.length) (acc.push (.int n, p))
      else if c.isAlpha || c == '_' then
        let idChars := c :: rest.takeWhile (fun d => d.isAlphanum || d == '_')
        let rest' := rest.dropWhile (fun d => d.isAlphanum || d == '_')
        let s := String.ofList idChars
        let tok := if keywords.contains s then Tok.kw s else Tok.ident s
        go rest' (adv idChars.length) (acc.push (tok, p))
      else if c == '"' then
        let (lit, rest', len) ← lexStr rest [] 1
        go rest' (adv len) (acc.push (.str lit, p))
      else
        -- two-character symbols first
        match c, rest.head? with
        | ':', some '=' => go rest.tail (adv 2) (acc.push (.sym ":=", p))
        | '=', some '=' => go rest.tail (adv 2) (acc.push (.sym "==", p))
        | '!', some '=' => go rest.tail (adv 2) (acc.push (.sym "!=", p))
        | '<', some '=' => go rest.tail (adv 2) (acc.push (.sym "<=", p))
        | '>', some '=' => go rest.tail (adv 2) (acc.push (.sym ">=", p))
        | '&', some '&' => go rest.tail (adv 2) (acc.push (.sym "&&", p))
        | '|', some '|' => go rest.tail (adv 2) (acc.push (.sym "||", p))
        | _, _ =>
          if "+-*/%(){};:,<>!=".toList.contains c then
            go rest (adv 1) (acc.push (.sym (String.ofList [c]), p))
          else
            throw s!"{p.show}: unexpected character '{c}'"
  lexStr (cs : List Char) (acc : List Char) (len : Nat) :
      Except String (String × List Char × Nat) := do
    match cs with
    | [] => throw "unterminated string literal"
    | '"' :: rest => return (String.ofList acc.reverse, rest, len + 1)
    | '\\' :: e :: rest =>
      let c ← match e with
        | 'n' => pure '\n'
        | 't' => pure '\t'
        | '\\' => pure '\\'
        | '"' => pure '"'
        | _ => throw s!"unknown escape '\\{e}' in string literal"
      lexStr rest (c :: acc) (len + 2)
    | c :: rest => lexStr rest (c :: acc) (len + 1)

/-- Parser state: token array and cursor. -/
structure St where
  toks : Array (Tok × Pos)
  i : Nat := 0

abbrev P (α : Type) := StateT St (Except String) α

def peek? : P (Option (Tok × Pos)) := do
  let st ← get
  return st.toks[st.i]?

def bump : P Unit := modify fun st => { st with i := st.i + 1 }

def errAt (msg : String) : P α := do
  match ← peek? with
  | some (t, p) => throw s!"{p.show}: {msg} (found {t.show})"
  | none => throw s!"end of input: {msg}"

def expectSym (s : String) : P Unit := do
  match ← peek? with
  | some (.sym s', _) => if s == s' then bump else errAt s!"expected '{s}'"
  | _ => errAt s!"expected '{s}'"

def expectKw (s : String) : P Unit := do
  match ← peek? with
  | some (.kw s', _) => if s == s' then bump else errAt s!"expected '{s}'"
  | _ => errAt s!"expected '{s}'"

def atSym (s : String) : P Bool := do
  match ← peek? with
  | some (.sym s', _) => return s == s'
  | _ => return false

def atKw (s : String) : P Bool := do
  match ← peek? with
  | some (.kw s', _) => return s == s'
  | _ => return false

def expectIdent : P String := do
  match ← peek? with
  | some (.ident x, _) => bump; return x
  | _ => errAt "expected an identifier"

mutual
/-- `partial`: recursive descent consumes at least one token per branch. -/
partial def parseAtom : P Expr := do
  match ← peek? with
  | some (.int n, _) => bump; return .intLit (Int.ofNat n)
  | some (.kw "true", _) => bump; return .boolLit true
  | some (.kw "false", _) => bump; return .boolLit false
  | some (.ident x, _) => bump; return .var x
  | some (.sym "(", _) => bump; let e ← parseExpr; expectSym ")"; return e
  | some (.sym "-", _) => bump; return .un .neg (← parseAtom)
  | some (.sym "!", _) => bump; return .un .not (← parseAtom)
  | _ => errAt "expected an expression"

partial def parseBinRhs (minPrec : Nat) (lhs : Expr) : P Expr := do
  let opInfo : Option (BinOp × Nat) ← do
    match ← peek? with
    | some (.sym s, _) =>
      pure <| match s with
      | "||" => some (.or, 1)
      | "&&" => some (.and, 2)
      | "==" => some (.eq, 3) | "!=" => some (.ne, 3)
      | "<" => some (.lt, 3) | "<=" => some (.le, 3)
      | ">" => some (.gt, 3) | ">=" => some (.ge, 3)
      | "+" => some (.add, 4) | "-" => some (.sub, 4)
      | "*" => some (.mul, 5) | "/" => some (.div, 5) | "%" => some (.mod, 5)
      | _ => none
    | _ => pure none
  match opInfo with
  | none => return lhs
  | some (op, prec) =>
    if prec < minPrec then return lhs
    else
      bump
      let rhs ← parseAtom
      let rhs ← parseBinRhs (prec + 1) rhs
      parseBinRhs minPrec (.bin op lhs rhs)

partial def parseExpr : P Expr := do
  parseBinRhs 1 (← parseAtom)
end

def parseTy : P Ty := do
  match ← peek? with
  | some (.kw "int", _) => bump; return .int
  | some (.kw "bool", _) => bump; return .bool
  | _ => errAt "expected a type ('int' or 'bool')"

mutual
partial def parseBlock : P Stmt := do
  expectSym "{"
  let s ← parseStmts
  expectSym "}"
  return s

partial def parseStmts : P Stmt := do
  let mut acc := Stmt.skip
  let mut first := true
  repeat
    match ← peek? with
    | none => break
    | some (.sym "}", _) => break
    | some (.kw "var", p) =>
      throw s!"{p.show}: 'var' declarations must precede all statements"
    | _ =>
      let s ← parseStmt
      acc := if first then s else .seq acc s
      first := false
  return acc

partial def parseStmt : P Stmt := do
  match ← peek? with
  | some (.kw "if", _) =>
    bump
    let c ← parseExpr
    let thn ← parseBlock
    if ← atKw "else" then
      bump
      if ← atKw "if" then
        return .ite c thn (← parseStmt)
      else
        return .ite c thn (← parseBlock)
    else
      return .ite c thn .skip
  | some (.kw "while", _) =>
    bump
    let c ← parseExpr
    let mut invs : List Expr := []
    let mut dec : Option Expr := none
    repeat
      if ← atKw "invariant" then
        bump
        invs := invs ++ [← parseExpr]
      else if ← atKw "decreases" then
        bump
        if dec.isSome then errAt "duplicate 'decreases'"
        dec := some (← parseExpr)
      else
        break
    let body ← parseBlock
    return .while c invs dec body
  | some (.kw "assert", _) =>
    bump; let e ← parseExpr; expectSym ";"
    return .assert e
  | some (.kw "print", _) | some (.kw "println", _) =>
    let nl ← atKw "println"
    bump; expectSym "("
    let s ← do
      match ← peek? with
      | some (.str lit, _) => bump; pure (Stmt.printStr lit nl)
      | some (.sym ")", _) =>
        if nl then pure (Stmt.printStr "" true)
        else errAt "print() needs an argument (println() prints a bare newline)"
      | _ => pure (Stmt.printExpr (← parseExpr) nl)
    expectSym ")"; expectSym ";"
    return s
  | some (.kw "printByte", _) =>
    bump; expectSym "("
    let e ← parseExpr
    expectSym ")"; expectSym ";"
    return .printByte e
  | some (.ident x, _) =>
    bump; expectSym ":="
    if ← atKw "readInt" then
      bump; expectSym "("; expectSym ")"; expectSym ";"
      return .readInt x
    else if ← atKw "readByte" then
      bump; expectSym "("; expectSym ")"; expectSym ";"
      return .readByte x
    else
      let e ← parseExpr
      expectSym ";"
      return .assign x e
  | _ => errAt "expected a statement"
end

def parseDecls : P (List (String × Ty × Option Expr)) := do
  let mut decls := []
  repeat
    if ← atKw "var" then
      bump
      let x ← expectIdent
      expectSym ":"
      let t ← parseTy
      let init ← do
        if ← atSym ":=" then
          bump
          pure (some (← parseExpr))
        else
          pure none
      expectSym ";"
      decls := decls ++ [(x, t, init)]
    else
      break
  return decls

def parseProgram : P Program := do
  let decls ← parseDecls
  let body ← parseStmts
  match ← peek? with
  | none => return { decls, body }
  | some (t, p) => throw s!"{p.show}: unexpected {t.show} after the program"

end Parser

/-- Parse Turpentine source into a `Program`. -/
def parse (src : String) : Except String Program := do
  let toks ← Parser.lex src
  (Parser.parseProgram.run { toks }).map (·.1)

end Langlib.Turpentine
