import Langlib.Turpentine.Syntax
import Std.Data.HashMap

/-!
# Turpentine: type checker

Turpentine is the Well-Typed Formalism, so programs are checked before they run or
compile: variables must be declared exactly once and used at their declared
type, conditions and assertions must be boolean, arithmetic must be on
integers, `readInt`/`readByte` targets must be `int`, and loop annotations
must type-check (`invariant` as `bool`, `decreases` as `int`) even though
the reference semantics ignores them.

The checker is a plain recursive pass returning the first error as a
human-readable message. There is no inference to do: every variable's type
comes from its declaration.
-/

namespace Langlib.Turpentine

abbrev Ctx := Std.HashMap String Ty

private def Ty.show : Ty → String
  | .int => "int"
  | .bool => "bool"

/-- Infer the type of an expression in a context. -/
def inferExpr (Γ : Ctx) : Expr → Except String Ty
  | .intLit _ => return .int
  | .boolLit _ => return .bool
  | .var x =>
    match Γ[x]? with
    | some t => return t
    | none => throw s!"undeclared variable '{x}'"
  | .un op e => do
    let t ← inferExpr Γ e
    match op, t with
    | .neg, .int => return .int
    | .not, .bool => return .bool
    | .neg, .bool => throw "unary '-' applied to a bool"
    | .not, .int => throw "'!' applied to an int"
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
    | some t =>
      (checkExpr Γ e t).mapError (s!"in assignment to '{x}': " ++ ·)
  | .ite c s₁ s₂ => do
    (checkExpr Γ c .bool).mapError ("'if' condition: " ++ ·)
    checkStmt Γ s₁
    checkStmt Γ s₂
  | .while c invs dec body => do
    (checkExpr Γ c .bool).mapError ("'while' condition: " ++ ·)
    for i in invs do
      (checkExpr Γ i .bool).mapError ("'invariant': " ++ ·)
    if let some d := dec then
      (checkExpr Γ d .int).mapError ("'decreases': " ++ ·)
    checkStmt Γ body
  | .assert e => (checkExpr Γ e .bool).mapError ("'assert': " ++ ·)
  | .readInt x | .readByte x =>
    match Γ[x]? with
    | none => throw s!"read into undeclared variable '{x}'"
    | some .int => return ()
    | some .bool => throw s!"read into '{x}', which is a bool"
  | .printExpr e _ => do
    let _ ← inferExpr Γ e  -- either type prints
    return ()
  | .printStr _ _ => return ()
  | .printByte e => (checkExpr Γ e .int).mapError ("'printByte': " ++ ·)

/-- Check a whole program; on success, return the typing context. -/
def checkProgram (p : Program) : Except String Ctx := do
  let mut Γ : Ctx := {}
  for (x, t, init) in p.decls do
    if Γ.contains x then
      throw s!"variable '{x}' declared twice"
    if let some e := init then
      (checkExpr Γ e t).mapError (s!"initialiser of '{x}': " ++ ·)
    Γ := Γ.insert x t
  checkStmt Γ p.body
  return Γ

end Langlib.Turpentine
