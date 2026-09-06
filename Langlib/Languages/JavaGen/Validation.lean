import Langlib.Languages.JavaGen.Syntax
import Std.Data.TreeMap

/-!
# JavaGen: checked inheritance closure

Only superclass heads are traversed, never nested argument constructors.
The depth guard is the number of declared heads plus one, not a type-depth
bound or a budget for subtype search. Incompatible symbolic instantiations
are rejected even if a particular closed query would make them equal.

Closure/validation correspondence with the paper's declarative relation is
still a proof obligation; no soundness theorem for the validator is assumed.
-/

namespace Langlib.JavaGen

/-- One symbolic superclass and the intermediate instantiated templates along
the first inheritance path to it. Reflexivity has an empty path. -/
structure Ancestor where
  type : Template
  path : List Template
deriving Repr, BEq, DecidableEq, Inhabited

/-- Cached closure produced by `prepare`. Its fields are executable data;
the type itself does not assert a proved well-formedness invariant. -/
structure Prepared where
  source : Program
  closure : List (String × List Ancestor)
deriving Repr, BEq, DecidableEq, Inhabited

private def checkNames (names : Std.TreeMap String Decl) (t : List String) : Except String Unit := do
  for name in t do
    unless names.contains name do throw s!"unknown constructor '{name}'"

private def walk (decls : Std.TreeMap String Decl) : Nat → List String → Template →
    List Template → Except String (List Ancestor)
  | 0, _, _, _ => .error "cyclic inheritance (head-depth bound exceeded)"
  | fuel + 1, seen, t, path => do
    let here : Ancestor := ⟨t, path⟩
    match t.ctors with
    | [] => return [here]
    | name :: rest =>
      if seen.contains name then throw s!"cyclic inheritance through '{name}'"
      let some decl := decls[name]?
        | throw s!"unknown constructor '{name}'"
      let mut result := [here]
      for base in decl.bases do
        let next := base.subst ⟨rest, t.tail⟩
        let ancestors ← walk decls fuel (name :: seen) next (path ++ [next])
        result := ancestors.reverse ++ result
      return result.reverse

/-- Check syntax-level invariants and compute deterministic symbolic closure.
Equal diamonds retain their first path; unequal diamonds are invalid. -/
def prepare (p : Program) : Except String Prepared := do
  let names := p.classes.map Decl.name
  -- Indices accelerate validation of generated tables; lists below retain
  -- source order and the first path through equal inheritance diamonds.
  let decls := Std.TreeMap.ofList (p.classes.map fun d => (d.name, d))
  let mut seen : Std.TreeMap String Unit := {}
  for d in p.classes do
    unless validName d.name do throw s!"invalid constructor name '{d.name}'"
    if seen.contains d.name then throw s!"duplicate constructor '{d.name}'"
    seen := seen.insert d.name ()
    let mut direct : Std.TreeMap (Option String) Unit := {}
    for base in d.bases do
      checkNames decls base.ctors
      if base.tail == .var && base.ctors.length % 2 != 1 then
        throw s!"'{d.name}': variable superclass must have odd constructor depth"
      let head := base.ctors.head?
      if direct.contains head then throw s!"'{d.name}': repeated direct superclass"
      direct := direct.insert head ()
  checkNames decls p.query.lhs
  checkNames decls p.query.rhs
  if p.answerSide.isSome then
    for digit in ["Succ", "Pad"] do
      let some decl := decls[digit]?
        | throw ("answer queries require 'interface " ++ digit ++ "<x> {}'")
      unless decl.bases.isEmpty do throw s!"answer constructor '{digit}' must have no superclasses"
  let mut closure := []
  for name in names do
    let paths ← walk decls (names.length + 1) [] ⟨[name], .var⟩ []
    let mut unique : List Ancestor := []
    let mut byHead : Std.TreeMap (Option String) Ancestor := {}
    for a in paths do
      match byHead[a.type.ctors.head?]? with
      | none =>
        unique := a :: unique
        byHead := byHead.insert a.type.ctors.head? a
      | some previous =>
        if previous.type != a.type then
          throw s!"'{name}': multiple instantiation of '{a.type.ctors.headD "Z"}'"
    closure := (name, unique.reverse) :: closure
  return { source := p, closure := closure.reverse }

/-- Resolve a closed source type to one superclass head, including `Z` (`none`).
The returned path records actual closed inheritance rewrites. -/
def Prepared.resolve (p : Prepared) (source : Ty) (head : Option String) :
    Option (Ty × List Ty) := do
  match source with
  | [] => if head.isNone then some ([], []) else none
  | name :: arg =>
    let (_, ancestors) ← p.closure.find? (·.1 == name)
    let a ← ancestors.find? (fun a => a.type.ctors.head? == head)
    return (a.type.instantiate arg, a.path.map (·.instantiate arg))

end Langlib.JavaGen
