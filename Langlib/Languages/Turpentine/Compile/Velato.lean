import Langlib.Languages.Turpentine.Syntax
import Langlib.Languages.Turpentine.Parser
import Langlib.Languages.Turpentine.Typecheck
import Langlib.Languages.Velato.Emit
import Langlib.Languages.Velato.Semantics
import Std.Data.HashMap

/-!
# Turpentine to Velato

A compiler from Turpentine (`.turp`) to Velato (`.vel`). The write-up, with
the fragment table and the worked example, is `docs/velato/compiler.md`.

## Why this backend is short

Every other hand-written backend in this library is long, and for the same
reason: the target is a machine and Turpentine is a language, so the
compiler has to build structured control flow out of jumps, integers out of
bytes, and variables out of addresses. `Compile/Brainfuck.lean` spends most
of its length on sixteen-bit arithmetic in eight-bit cells.

Velato is not a machine. It has `while`, `if`/`else`, named variables, and
unbounded integers with the five arithmetic operators — it is, structurally,
the same kind of language Turpentine is, wearing a MIDI file. So this
compiler is close to a direct translation of one abstract syntax into
another, and almost all of its content is in the four places where the two
languages genuinely differ.

## The four differences

**No arrays.** velato.net lists arrays, and so strings, among the features
Velato does not have, and no implementation has added them. Turpentine's
`a[i]`, `len(a)` and the three array-writing statements are therefore
outside this backend's fragment: `compile` returns `Except.error` naming
them, rather than emitting something that quietly means less.

**Division rounds the other way.** Turpentine's `/` and `%` are Euclidean —
`Int.ediv` and `Int.emod`, so the remainder is never negative. Velato's are
C#'s, which truncate toward zero and give the remainder the sign of the
dividend. The two agree whenever the dividend is non-negative and disagree
otherwise, so this compiler does not just emit `/`: it emits the truncating
quotient and remainder into scratch variables and then corrects them, which
costs an `if` and is the only way to get Turpentine's answer out of Velato's
operator.

Correcting needs statements, so `compileExpr` returns a *prelude* of
statements alongside the expression. That in turn is why `&&` and `||` are
compiled through an `if` whenever their right operand has a prelude:
hoisting the prelude out would run it unconditionally and lose the
short-circuit, which is observable — `x != 0 && 10 / x > 1` must not divide
by zero.

**No boolean type.** Velato has three types and none of them is `bool`;
there is no boolean literal and no way to declare one. A Turpentine `bool`
is carried as a Velato `int` that is `0` or `1`, which is what Velato's own
comparisons produce and what its `while` and `if` read back. Printing one
has to expand into an `if` that prints `true` or `false`, since Velato
cannot print a word it has no string type for.

**Reading a byte cannot see the difference between a zero byte and the end
of the stream.** Turpentine's `readByte` yields `-1` at end of input and
`0 … 255` otherwise, so a program can read a NUL and know it was not the
end. Velato's `Input` stores `0` for both — `docs/velato/spec.md` records
why — so this backend maps `0` to `-1`, and a NUL byte in the input is
indistinguishable from end of input. This is exactly the caveat the
brainfuck backend carries, for exactly the same reason.

## What it does not do

`readInt` and `assert` are outside the fragment. `readInt` would mean
open-coding a decimal parser, and Turpentine's version *fails* on a
malformed line, which Velato has no way to signal; `assert` likewise has
nothing to fail into, since Velato has no abort. Both are refused by name
rather than approximated.

## Register of notes

A Velato variable is an absolute MIDI pitch, and there are 128 of them. The
allocator hands out the octaves below middle C to the program's declared
variables and the ones above to the scratch cells the division correction
needs, which keeps them apart on the staff. A program needing more than 128
between them is refused, and that limit is the language's rather than this
compiler's.
-/

namespace Langlib.Turpentine.Compile.Velato

open Langlib.Turpentine
open Langlib.Velato (Pitch)

/-! ## Allocation -/

/-- Where the program's own variables start: C1, well below the register the
encoder writes commands in, so they stand out on the staff. -/
def varBase : Nat := 24

/-- The scratch cells the division correction and the short-circuit
expansion need, above the program's variables. -/
def scratchBase : Nat := 96

/-- Compiler state: the variable map, and how many scratch cells are in use.

`cur` is reset at every statement, because a statement's preludes have all
run by the time the next one starts, so the cells can be reused. `peak` is
what gets declared. -/
structure St where
  vars : Std.HashMap String Pitch := {}
  cur : Nat := 0
  peak : Nat := 0

abbrev M := StateM St

/-- A fresh scratch cell for the statement being compiled. -/
def fresh : M Pitch := do
  let s ← get
  set { s with cur := s.cur + 1, peak := max s.peak (s.cur + 1) }
  return scratchBase + s.cur

/-- Start a new statement: the scratch cells are free again. -/
def newStatement : M Unit := modify fun s => { s with cur := 0 }

/-! ## Expressions -/

open Langlib.Velato in
/-- The Velato operator a Turpentine one becomes, where there is one. The
three Turpentine comparisons Velato lacks are built from `not` below. -/
def binOp? : Turpentine.BinOp → Option Langlib.Velato.BinOp
  | .add => some .add | .sub => some .sub | .mul => some .mul
  | .eq => some .eq | .lt => some .lt | .gt => some .gt
  | .and => some .and | .or => some .or
  | _ => none

open Langlib.Velato in
/-- Compile an expression to a prelude of statements and a Velato
expression. The prelude is empty for everything but division, remainder, and
a `&&` or `||` whose right operand needs one. -/
partial def compileExpr (Γ : Langlib.Turpentine.Ctx) :
    Turpentine.Expr → M (Except String (List Langlib.Velato.Stmt × Langlib.Velato.Expr))
  | .intLit n => return .ok ([], .intLit n)
  | .boolLit b => return .ok ([], .intLit (if b then 1 else 0))
  | .var x => do
    match (← get).vars[x]? with
    | some p => return .ok ([], .var p)
    | none => return .error s!"velato: undeclared variable '{x}'"
  | .len x => return .error s!"velato: Velato has no arrays, so len({x}) has no meaning"
  | .index x _ => return .error s!"velato: Velato has no arrays, so {x}[i] has no meaning"
  | .un .not e => do
    match ← compileExpr Γ e with
    | .error m => return .error m
    | .ok (pre, ve) => return .ok (pre, .un .not ve)
  | .un .neg e => do
    -- Velato has no unary minus; zero minus the value is the same thing
    match ← compileExpr Γ e with
    | .error m => return .error m
    | .ok (pre, ve) => return .ok (pre, .bin .sub (.intLit 0) ve)
  | .bin op l r => do
    match ← compileExpr Γ l with
    | .error m => return .error m
    | .ok (lp, le) =>
      match ← compileExpr Γ r with
      | .error m => return .error m
      | .ok (rp, re) =>
        match op with
        | .ne => return .ok (lp ++ rp, .un .not (.bin .eq le re))
        | .le => return .ok (lp ++ rp, .un .not (.bin .gt le re))
        | .ge => return .ok (lp ++ rp, .un .not (.bin .lt le re))
        | .div | .mod => do
          -- Turpentine's division is Euclidean and Velato's truncates, so
          -- take the truncating answer and correct it when the remainder
          -- came out negative.
          let a ← fresh; let b ← fresh; let q ← fresh; let rr ← fresh
          let decls : List Langlib.Velato.Stmt :=
            [ .declare a .int, .declare b .int, .declare q .int, .declare rr .int ]
          let setup : List Langlib.Velato.Stmt :=
            [ .assign a le, .assign b re
            , .assign q (.bin .div (.var a) (.var b))
            , .assign rr (.bin .mod (.var a) (.var b)) ]
          let fixup : Langlib.Velato.Stmt :=
            .ite (.bin .lt (.var rr) (.intLit 0))
              [ .ite (.bin .gt (.var b) (.intLit 0))
                  [ .assign q (.bin .sub (.var q) (.intLit 1))
                  , .assign rr (.bin .add (.var rr) (.var b)) ]
                  [ .assign q (.bin .add (.var q) (.intLit 1))
                  , .assign rr (.bin .sub (.var rr) (.var b)) ] ]
              []
          let pre := lp ++ rp ++ decls ++ setup ++ [fixup]
          return .ok (pre, .var (if op == .div then q else rr))
        | .and | .or =>
          if rp.isEmpty then
            match binOp? op with
            | some vop => return .ok (lp ++ rp, .bin vop le re)
            | none => return .error "velato: unreachable operator"
          else
            -- the right operand needs statements, and running them
            -- unconditionally would lose the short circuit
            let t ← fresh
            let guard : Langlib.Velato.Expr :=
              if op == .and then le else .un .not le
            let dflt : Int := if op == .and then 0 else 1
            let body := rp ++ [.assign t (.un .not (.un .not re))]
            return .ok
              (lp ++ [.declare t .int, .assign t (.intLit dflt), .ite guard body []], .var t)
        | _ =>
          match binOp? op with
          | some vop => return .ok (lp ++ rp, .bin vop le re)
          | none => return .error s!"velato: no Velato operator for this"

/-! ## Statements -/

open Langlib.Velato in
/-- Print a string, one `Print` command per character: Velato has no
strings. -/
def putStr (s : String) : List Langlib.Velato.Stmt :=
  s.toList.map fun c => .print (.charLit c.toNat)

open Langlib.Velato in
partial def compileStmt (Γ : Langlib.Turpentine.Ctx) :
    Turpentine.Stmt → M (Except String (List Langlib.Velato.Stmt))
  | .skip => return .ok []
  | .seq a b => do
    match ← compileStmt Γ a with
    | .error m => return .error m
    | .ok sa =>
      match ← compileStmt Γ b with
      | .error m => return .error m
      | .ok sb => return .ok (sa ++ sb)
  | .assign x e => do
    newStatement
    match (← get).vars[x]? with
    | none => return .error s!"velato: undeclared variable '{x}'"
    | some p =>
      match ← compileExpr Γ e with
      | .error m => return .error m
      | .ok (pre, ve) => return .ok (pre ++ [.assign p ve])
  | .ite c thn els => do
    newStatement
    match ← compileExpr Γ c with
    | .error m => return .error m
    | .ok (pre, vc) =>
      match ← compileStmt Γ thn with
      | .error m => return .error m
      | .ok vt =>
        match ← compileStmt Γ els with
        | .error m => return .error m
        | .ok ve => return .ok (pre ++ [.ite vc vt ve])
  | .while c body => do
    newStatement
    match ← compileExpr Γ c with
    | .error m => return .error m
    | .ok (pre, vc) =>
      match ← compileStmt Γ body with
      | .error m => return .error m
      | .ok vb =>
        -- The condition's prelude has to run again before every test, so it
        -- goes both before the loop and at the end of its body. This is the
        -- one place the translation is not one for one, and it is why a
        -- division inside a loop condition costs what it does.
        return .ok (pre ++ [.while vc (vb ++ pre)])
  | .printStr s nl => do
    newStatement
    return .ok (putStr s ++ (if nl then putStr "\n" else []))
  | .printExpr e nl => do
    newStatement
    match ← compileExpr Γ e with
    | .error m => return .error m
    | .ok (pre, ve) =>
      match Langlib.Turpentine.inferExpr Γ e with
      | .ok .bool =>
        -- Velato has no bool and no strings, so printing one is an if
        return .ok (pre ++ [.ite ve (putStr "true") (putStr "false")]
                        ++ (if nl then putStr "\n" else []))
      | _ => return .ok (pre ++ [.print ve] ++ (if nl then putStr "\n" else []))
  | .printByte e => do
    newStatement
    match ← compileExpr Γ e with
    | .error m => return .error m
    | .ok (pre, ve) =>
      -- `printByte` is the byte `e mod 256` with Turpentine's Euclidean
      -- `mod`, so the same correction as `%` is needed, and then the value
      -- has to pass through a `char` variable: Velato prints an `int` as a
      -- numeral and a `char` as a character, and it has no cast.
      let a ← fresh; let rr ← fresh; let c ← fresh
      return .ok (pre ++
        [ .declare a .int, .declare rr .int, .declare c .char
        , .assign a ve
        , .assign rr (.bin .mod (.var a) (.intLit 256))
        , .ite (.bin .lt (.var rr) (.intLit 0))
            [ .assign rr (.bin .add (.var rr) (.intLit 256)) ] []
        , .assign c (.var rr)
        , .print (.var c) ])
  | .readByte x => do
    newStatement
    match (← get).vars[x]? with
    | none => return .error s!"velato: undeclared variable '{x}'"
    | some p =>
      -- Velato stores 0 at end of stream and cannot tell that from a NUL
      -- byte; Turpentine wants -1 at end of stream. See the header.
      let c ← fresh
      return .ok
        [ .declare c .char
        , .input c
        , .assign p (.var c)
        , .ite (.bin .eq (.var p) (.intLit 0))
            [ .assign p (.intLit (-1)) ] [] ]
  | .readInt x =>
    return .error s!"velato: readInt (for '{x}') is outside this backend's fragment; \
      Velato reads one character at a time and has no way to fail on a malformed line"
  | .assert _ =>
    return .error "velato: assert is outside this backend's fragment; \
      Velato has no way to abort"
  | .assignIndex x _ _ =>
    return .error s!"velato: Velato has no arrays, so '{x}[i] := e' has no meaning"
  | .readIntIndex x _ =>
    return .error s!"velato: Velato has no arrays, so '{x}[i] := readInt()' has no meaning"
  | .readByteIndex x _ =>
    return .error s!"velato: Velato has no arrays, so '{x}[i] := readByte()' has no meaning"

/-! ## Programs -/

open Langlib.Velato in
/-- Compile a type-checked program to a Velato program. -/
def compileProgram (p : Program) (Γ : Langlib.Turpentine.Ctx) :
    Except String Langlib.Velato.Prog := do
  -- Give every declared variable a pitch. Arrays get none, and the error
  -- says so before anything else goes wrong.
  let mut vars : Std.HashMap String Pitch := {}
  let mut n := 0
  for (x, t, _) in p.decls do
    if let .array _ _ := t then
      throw s!"velato: Velato has no arrays, so '{x}' cannot be declared"
    if varBase + n ≥ scratchBase then
      throw s!"velato: this program declares more variables than Velato has notes for them"
    vars := vars.insert x (varBase + n)
    n := n + 1
  let (body?, st) := (compileStmt Γ p.body).run { vars }
  let body ← body?
  if scratchBase + st.peak > 128 then
    throw "velato: this program needs more scratch variables than Velato has notes"
  -- Declarations first, then the initialisers, then the body. Velato has no
  -- initialiser syntax, so `var x: int := 3` becomes a declaration and an
  -- assignment.
  let mut decls : List Langlib.Velato.Stmt := []
  let mut inits : List Langlib.Velato.Stmt := []
  for (x, t, init) in p.decls do
    let some pt := vars[x]? | throw s!"velato: internal: '{x}' lost its pitch"
    decls := decls ++ [.declare pt .int]
    match init with
    | none =>
      -- Velato's declaration already zeroes it, and `false` is zero too
      pure ()
    | some e =>
      match (compileExpr Γ e).run { vars } with
      | (.error m, _) => throw m
      | (.ok (pre, ve), _) => inits := inits ++ pre ++ [.assign pt ve]
    match t with
    | .array _ _ => throw s!"velato: Velato has no arrays, so '{x}' cannot be declared"
    | _ => pure ()
  return decls ++ inits ++ body

/-- The command root the emitted program is written from: middle C. A Velato
program can be transposed freely, so this is a presentational choice and
nothing depends on it. -/
def defaultRoot : Pitch := 60

/-- How the emitted program is voiced: a comfortable two octaves around
middle C, leaning towards C natural minor so that the chromatic command
intervals have something to lean against. -/
def defaultVoice : Langlib.Velato.Voice :=
  { lo := 55, hi := 84, centre := 67, scale := [0, 2, 3, 5, 7, 8, 10] }

/-- Render a Velato program as `.vel` text.

The register is deliberately wider than `defaultVoice`'s: this is also the
renderer the *derived* compiler uses, whose programs are register-machine
simulations and much longer, and a wider register gives the encoder more
room to keep the line moving. `emitFrom` can only fail when no pitch in the
register satisfies a demand, which cannot happen once the register spans an
octave, so the error arm here is unreachable and says so rather than
pretending to have produced a program. -/
def renderProg (p : Langlib.Velato.Prog) : String :=
  match Langlib.Velato.emitFrom p defaultRoot { lo := 36, hi := 96, centre := 66 } with
  | .ok notes => Langlib.Velato.renderNotes notes
  | .error m => s!"% this program could not be encoded: {m}\n"

/-- Turpentine source text to Velato source text: the entry point the
runner's `--to velato` uses. -/
def compileSource (src : String) : Except String String := do
  let prog ← parse src
  let Γ ← (checkProgram prog).mapError ("type error: " ++ ·)
  let vprog ← compileProgram prog Γ
  let notes ← Langlib.Velato.emitFrom vprog defaultRoot defaultVoice
  return Langlib.Velato.renderNotes notes

end Langlib.Turpentine.Compile.Velato
