/-!
# Turpentine: abstract syntax

Turpentine (Well-Typed Formalism, file extension `.turp`) is the human-readable
front end of langlib: a small imperative language, deeply embedded in Lean,
whose programs compile to the esoteric languages in the library. Its
concrete syntax is Dafny-flavoured, inspired by Velvet
(https://github.com/verse-lab/velvet); the long-term plan is to compile a
restricted fragment of shallowly-embedded Velvet into Turpentine by relational
compilation, so the AST deliberately stays small and first-order: two value
types (`int`, `bool`), mutable variables, structured control flow, and
explicit byte- and number-level I/O matching `Langlib.Common`.

`assert` is the only specification construct. Loops carried `invariant`
and `decreases` annotations until 2026-09-01; they were removed because
nothing consumed them, since compiler verification reasons about the
semantics of `while` whatever decorates it.
-/

namespace Langlib.Turpentine

/-- Turpentine value types. Integers are unbounded (`Int`); compilers to bounded
targets document their restrictions.

Arrays are one-dimensional with a length fixed at compile time, and their
elements are scalars. Both restrictions are deliberate: the compilers have
to lay arrays out in machines with no dynamic allocation, and subleq has no
computed addressing at all, so a statically known length and element size
is what makes `a[i]` compilable there. See `docs/turpentine/spec.md`. -/
inductive Ty where
  | int
  | bool
  /-- `int[n]` or `bool[n]`; `elem` is always `int` or `bool`. -/
  | array (elem : Ty) (len : Nat)
deriving Repr, BEq, Inhabited

/-- Binary operators. Arithmetic is `Int`-valued; `div`/`mod` are Euclidean
(`Int.ediv`/`Int.emod`: the remainder is always non-negative), a decision
recorded in `docs/turpentine/spec.md`. -/
inductive BinOp where
  | add | sub | mul | div | mod
  | eq | ne | lt | le | gt | ge
  | and | or
deriving Repr, BEq, Inhabited

inductive UnOp where
  | neg  -- integer negation
  | not  -- boolean negation
deriving Repr, BEq, Inhabited

inductive Expr where
  | intLit (n : Int)
  | boolLit (b : Bool)
  | var (x : String)
  | un (op : UnOp) (e : Expr)
  | bin (op : BinOp) (e₁ e₂ : Expr)
  /-- `a[i]` : read an array element. Out of bounds is a runtime error. -/
  | index (x : String) (i : Expr)
  /-- `len(a)` : the array's length. Statically known, so the type checker
  could fold it to a literal; it is kept as a node so error messages and
  the verification pipeline can see where the programmer wrote it. -/
  | len (x : String)
deriving Repr, BEq, Inhabited

/-- Statements. I/O is statement-level, so expressions stay pure; this keeps
both the semantics and the compilers simple. -/
inductive Stmt where
  | skip
  | seq (s₁ s₂ : Stmt)
  /-- `x := e;` -/
  | assign (x : String) (e : Expr)
  /-- `if c { s₁ } else { s₂ }` (the `else` branch may be `skip`). -/
  | ite (c : Expr) (s₁ s₂ : Stmt)
  /-- `while c { body }`. -/
  | while (c : Expr) (body : Stmt)
  /-- `assert e;` : runtime error if `e` evaluates to `false`. -/
  | assert (e : Expr)
  /-- `x := readInt();` : read one line, parse a decimal integer. -/
  | readInt (x : String)
  /-- `x := readByte();` : read one byte (`0..255`), or `-1` at EOF. -/
  | readByte (x : String)
  /-- `a[i] := e;` : write an array element. Out of bounds is a runtime
  error, and the index is evaluated before the right-hand side. -/
  | assignIndex (x : String) (i : Expr) (e : Expr)
  /-- `a[i] := readInt();` -/
  | readIntIndex (x : String) (i : Expr)
  /-- `a[i] := readByte();` -/
  | readByteIndex (x : String) (i : Expr)
  /-- `print(e);` / `println(e);` : decimal rendering of an integer or
  `true`/`false` for a boolean, then a newline if `newline`. -/
  | printExpr (e : Expr) (newline : Bool)
  /-- `print("...");` / `println("...");` : a literal string. -/
  | printStr (s : String) (newline : Bool)
  /-- `printByte(e);` : the byte `e mod 256`. -/
  | printByte (e : Expr)
deriving Repr, BEq, Inhabited

/-- A Turpentine program: variable declarations (with optional initialisers,
default `0` / `false`) followed by a body. One flat scope; the type checker
rejects redeclaration and use of undeclared variables. -/
structure Program where
  decls : List (String × Ty × Option Expr)
  body : Stmt
deriving Repr, Inhabited

end Langlib.Turpentine
