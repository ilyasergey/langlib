import Langlib.Turpentine.Syntax
import Std.Data.HashMap

/-!
# Turpentine: type checker

Turpentine is the Well-Typed Formalism, so programs are checked before they run or
compile: variables must be declared exactly once and used at their declared
type, conditions and assertions must be boolean, arithmetic must be on
integers, and `readInt`/`readByte` targets must be `int`.

The checker is a plain recursive pass returning the first error as a
human-readable message. There is no inference to do: every variable's type
comes from its declaration.
-/

namespace Langlib.Turpentine

abbrev Ctx := Std.HashMap String Ty

private def Ty.show : Ty → String
  | .int => "int"
  | .bool => "bool"
  | .array .int n => s!"int[{n}]"
  | .array .bool n => s!"bool[{n}]"
  | .array _ n => s!"array[{n}]"

/-- Look up an array variable, reporting a useful error for a scalar. -/
private def lookupArray (Γ : Ctx) (x : String) : Except String (Ty × Nat) :=
  match Γ[x]? with
  | none => throw s!"undeclared variable '{x}'"
  | some (.array elem n) => return (elem, n)
  | some t => throw s!"'{x}' has type {t.show}, so it cannot be indexed"

/-- Infer the type of an expression in a context. -/
def inferExpr (Γ : Ctx) : Expr → Except String Ty
  | .intLit _ => return .int
  | .boolLit _ => return .bool
  | .var x =>
    match Γ[x]? with
    | some (.array _ n) =>
      throw s!"'{x}' is an array of length {n}; index it as '{x}[i]' or take 'len({x})'"
    | some t => return t
    | none => throw s!"undeclared variable '{x}'"
  | .index x i => do
    let (elem, _) ← lookupArray Γ x
    let ti ← inferExpr Γ i
    unless ti == .int do
      throw s!"index of '{x}' must be an int, got {ti.show}"
    return elem
  | .len x => do
    let _ ← lookupArray Γ x
    return .int
  | .un op e => do
    let t ← inferExpr Γ e
    match op, t with
    | .neg, .int => return .int
    | .not, .bool => return .bool
    | .neg, t => throw s!"unary '-' applied to {t.show}"
    | .not, t => throw s!"'!' applied to {t.show}"
  | .bin op e₁ e₂ => do
    let t₁ ← inferExpr Γ e₁
    let t₂ ← inferExpr Γ e₂
    let need (want : Ty) (result : Ty) : Except String Ty := do
      if t₁ == want && t₂ == want then return result
      else throw s!"operator expects two {want.show} operands, got {t₁.show} and {t₂.show}"
    match op with
    | .add | .sub | .mul | .div | .mod => need .int .int
    | .lt | .le | .gt | .ge => need .int .bool
    | .and | .or => need .bool .bool
    | .eq | .ne =>
      if t₁ == t₂ then return .bool
      else throw s!"'==' / '!=' compare equal types, got {t₁.show} and {t₂.show}"

/-- Check that an expression has the given type. -/
def checkExpr (Γ : Ctx) (e : Expr) (want : Ty) : Except String Unit := do
  let t ← inferExpr Γ e
  unless t == want do
    throw s!"expected {want.show}, got {t.show}"

def checkStmt (Γ : Ctx) : Stmt → Except String Unit
  | .skip => return ()
  | .seq s₁ s₂ => do checkStmt Γ s₁; checkStmt Γ s₂
  | .assign x e =>
    match Γ[x]? with
    | none => throw s!"assignment to undeclared variable '{x}'"
    | some (.array _ n) =>
      throw s!"'{x}' is an array of length {n}; assign to an element, '{x}[i] := ...'"
    | some t =>
      (checkExpr Γ e t).mapError (s!"in assignment to '{x}': " ++ ·)
  | .assignIndex x i e => do
    let (elem, _) ← lookupArray Γ x
    (checkExpr Γ i .int).mapError (s!"index of '{x}': " ++ ·)
    (checkExpr Γ e elem).mapError (s!"in assignment to '{x}[i]': " ++ ·)
  | .readIntIndex x i | .readByteIndex x i => do
    let (elem, _) ← lookupArray Γ x
    (checkExpr Γ i .int).mapError (s!"index of '{x}': " ++ ·)
    unless elem == .int do
      throw s!"read into '{x}[i]', whose elements are {elem.show}"
  | .ite c s₁ s₂ => do
    (checkExpr Γ c .bool).mapError ("'if' condition: " ++ ·)
    checkStmt Γ s₁
    checkStmt Γ s₂
  | .while c body => do
    (checkExpr Γ c .bool).mapError ("'while' condition: " ++ ·)
    checkStmt Γ body
  | .assert e => (checkExpr Γ e .bool).mapError ("'assert': " ++ ·)
  | .readInt x | .readByte x =>
    match Γ[x]? with
    | none => throw s!"read into undeclared variable '{x}'"
    | some .int => return ()
    | some .bool => throw s!"read into '{x}', which is a bool"
    | some t => throw s!"read into '{x}', which is {t.show}"
  | .printExpr e _ => do
    -- either scalar type prints; an array does not
    match ← inferExpr Γ e with
    | .array _ _ => throw "'print' of a whole array; print its elements instead"
    | _ => return ()
  | .printStr _ _ => return ()
  | .printByte e => (checkExpr Γ e .int).mapError ("'printByte': " ++ ·)

/-- Check a whole program; on success, return the typing context. -/
def checkProgram (p : Program) : Except String Ctx := do
  let mut Γ : Ctx := {}
  for (x, t, init) in p.decls do
    if Γ.contains x then
      throw s!"variable '{x}' declared twice"
    if let .array _ 0 := t then
      throw s!"array '{x}' has length 0; give it at least one element"
    if let some e := init then
      match t with
      | .array _ _ =>
        throw s!"array '{x}' cannot have an initialiser; its elements start at 0 or false"
      | _ => (checkExpr Γ e t).mapError (s!"initialiser of '{x}': " ++ ·)
    Γ := Γ.insert x t
  checkStmt Γ p.body
  return Γ

end Langlib.Turpentine
