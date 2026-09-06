/-!
# JavaGen: unary contravariant types

The core is Grigore's subtyping machine (POPL 2017, §§3–4).
Constructor lists run from outside to inside; the empty closed type is `Z`.
See `docs/javagen/spec.md` for syntax and semantic conventions.
-/

namespace Langlib.JavaGen

/-- A closed unary type, with an implicit final `Z`. -/
abbrev Ty := List String

/-- A superclass template either preserves or discards its parameter. -/
inductive Tail where
  | var
  | zero
deriving Repr, BEq, DecidableEq, Inhabited

structure Template where
  ctors : List String
  tail : Tail
deriving Repr, BEq, DecidableEq, Inhabited

/-- Substitute a closed argument for the template's bound variable. -/
def Template.instantiate (t : Template) (arg : Ty) : Ty :=
  t.ctors ++ match t.tail with | .var => arg | .zero => []

/-- Substitute a template, as needed when following indirect inheritance. -/
def Template.subst (t arg : Template) : Template :=
  match t.tail with
  | .zero => t
  | .var => { ctors := t.ctors ++ arg.ctors, tail := arg.tail }

theorem Template.instantiate_subst (t arg : Template) (u : Ty) :
    (t.subst arg).instantiate u = t.instantiate (arg.instantiate u) := by
  cases t with
  | mk ctors tail => cases tail <;> simp [subst, instantiate, List.append_assoc]

structure Decl where
  name : String
  bases : List Template := []
deriving Repr, BEq, DecidableEq, Inhabited

structure Query where
  lhs : Ty
  rhs : Ty
deriving Repr, BEq, DecidableEq, Inhabited

inductive Side where
  | lhs
  | rhs
deriving Repr, BEq, DecidableEq, Inhabited

structure Program where
  classes : List Decl
  query : Query
  /-- One query tail may be an unknown natural answer, rather than `Z`.
  This is an inference request, elaborated to a concrete query before Java export. -/
  answerSide : Option Side := none
deriving Repr, BEq, DecidableEq, Inhabited

def renderChain (names : List String) (tail : String) : String :=
  names.foldr (fun name body => name ++ "<" ++ body ++ ">") tail

def Ty.render (t : Ty) : String := renderChain t "Z"

def Template.render (t : Template) : String :=
  renderChain t.ctors (match t.tail with | .var => "x" | .zero => "Z")

def Query.render (q : Query) : String := q.lhs.render ++ " <: " ++ q.rhs.render

def Decl.render (d : Decl) : String :=
  "interface " ++ d.name ++ "<x>" ++
    (if d.bases.isEmpty then "" else
      " extends " ++ String.intercalate ", " (d.bases.map Template.render)) ++ " {}"

/-- Canonical source text; comments and whitespace are not represented in the AST. -/
def Program.render (p : Program) : String :=
  "zero Z;\n" ++ String.join (p.classes.map (fun d => d.render ++ "\n")) ++
    "check " ++ renderChain p.query.lhs (if p.answerSide == some .lhs then "answer" else "Z") ++
    " <: " ++ renderChain p.query.rhs (if p.answerSide == some .rhs then "answer" else "Z") ++ ";\n"

/-- Unary digits separated by an inert variance-reversing constructor.
Zero is `Z`; positive `n` has `n` Succs and `n-1` Pads. -/
def encodeNat : Nat → Ty
  | 0 => []
  | n + 1 => "Succ" :: List.flatten (List.replicate n ["Pad", "Succ"])

/-- Specialize the original query, leaving its computation and declarations intact. -/
def Program.bindAnswer (p : Program) (n : Nat) : Program :=
  let numeral := encodeNat n
  { p with answerSide := none, query :=
      { lhs := p.query.lhs ++ if p.answerSide == some .lhs then numeral else []
        rhs := p.query.rhs ++ if p.answerSide == some .rhs then numeral else [] } }

def identStart (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || c == '_'

def identRest (c : Char) : Bool := identStart c || ('0' ≤ c && c ≤ '9')

def reserved : List String := ["Z", "x", "zero", "interface", "extends", "check", "answer"]

def validName (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => identStart c && cs.all identRest && !reserved.contains s

end Langlib.JavaGen
