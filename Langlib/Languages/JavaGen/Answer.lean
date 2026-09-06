import Langlib.Languages.JavaGen.Semantics

/-!
# JavaGen: infer a natural result, then check the specialized query

One `answer` tail is an unknown type. Symbolic execution propagates it
through unary superclass substitutions and reversals, exposing one digit
at a time. A positive numeral has alternating Succ/Pad constructors, starts
and ends with Succ, and finishes at Z; zero is Z. Both constructors have
no superclasses. Erasing an unconstrained hole is an error, not answer zero.

The original query is then specialized and run by the concrete evaluator.
Java certification independently checks that same specialization. This
is executable inference and checking, not yet a proved universal compiler.
-/

namespace Langlib.JavaGen
open Langlib.Common

structure OpenQuery where
  lhs : Template
  rhs : Template
deriving Repr, BEq, DecidableEq, Inhabited

inductive Inference where
  | candidate (n : Nat)
  | outOfFuel
  | error (message : String)
deriving Repr, BEq, DecidableEq, Inhabited

/-- Symbolic head lookup; the variable tail now denotes the answer hole. -/
def resolveOpen (p : Prepared) (source : Template) (head : Option String) : Option Template := do
  match source.ctors with
  | [] =>
    if source.tail == .zero && head.isNone then some ⟨[], .zero⟩ else none
  | name :: rest =>
    let (_, ancestors) ← p.closure.find? (·.1 == name)
    let a ← ancestors.find? (fun a => a.type.ctors.head? == head)
    return a.type.subst ⟨rest, source.tail⟩

/-- Allowed next heads in a numeral: Z can end zero or a completed digit,
while Pad must be followed by Succ. `digits` holds the exposed prefix. -/
def numeralHeads (digits : Ty) : List (Option String) :=
  match digits.getLast? with
  | none => [none, some "Succ"]
  | some "Succ" => [none, some "Pad"]
  | _ => [some "Succ"]

inductive InferStep where
  | candidate (n : Nat)
  | error (message : String)
  | next (query : OpenQuery) (digits : Ty)
deriving Repr, Inhabited

/-- One symbolic inference action, including exposing a numeral constructor. -/
def inferStep (p : Prepared) (q : OpenQuery) (digits : Ty) : InferStep :=
    if q.lhs == ⟨[], .var⟩ then
      if q.rhs.tail != .zero then .error "answer is not ground"
      else
        let head := q.rhs.ctors.head?
        if !(numeralHeads digits).contains head then .error "answer is not a padded unary numeral"
        else match head with
        | none => .candidate (digits.filter (· == "Succ")).length
        | some c => .next { q with lhs := ⟨[c], .var⟩ } (digits ++ [c])
    else if q.rhs == ⟨[], .var⟩ then
      let choices := (numeralHeads digits).filter (fun head => (resolveOpen p q.lhs head).isSome)
      match choices with
      | [none] => .candidate (digits.filter (· == "Succ")).length
      | [some c] => .next { q with rhs := ⟨[c], .var⟩ } (digits ++ [c])
      | [] => .error "answer is not a padded unary numeral"
      | _ => .error "answer query has ambiguous numeric heads"
    else
      match resolveOpen p q.lhs q.rhs.ctors.head? with
      | none => .error "answer query is not a subtype"
      | some super =>
        match q.rhs.ctors, super.ctors with
        | [], [] => .error "answer was erased without being constrained"
        | _ :: targetArg, _ :: sourceArg =>
          .next ⟨⟨targetArg, q.rhs.tail⟩, ⟨sourceArg, super.tail⟩⟩ digits
        | _, _ => .error "answer query is not a subtype"


/-- Inference fuel counts both digit exposure and subtype transitions. -/
def infer (p : Prepared) : Nat → OpenQuery → Ty → Inference
  | 0, _, _ => .outOfFuel
  | fuel + 1, q, digits =>
    match inferStep p q digits with
    | .candidate n => .candidate n
    | .error msg => .error msg
    | .next q' digits' => infer p fuel q' digits'

def initialOpen (p : Program) : OpenQuery :=
  { lhs := ⟨p.query.lhs, if p.answerSide == some .lhs then .var else .zero⟩
    rhs := ⟨p.query.rhs, if p.answerSide == some .rhs then .var else .zero⟩ }

def checkedAnswer (n : Nat) (r : RunResult) : RunResult :=
  { r with output := if r.exit == .halted then s!"{n}\n".toUTF8 else .empty }

/-- Each phase gets the given budget: inference, then concrete verification.
Only a concretely accepted candidate is emitted as decimal output. -/
def evalAnswer (p : Prepared) (fuel : Nat) : RunResult :=
  match infer p fuel (initialOpen p.source) [] with
  | .outOfFuel => { exit := .outOfFuel }
  | .error msg => { exit := .error msg }
  | .candidate n =>
    match prepare (p.source.bindAnswer n) with
    | .error msg => { exit := .error ("answer specialization: " ++ msg) }
    | .ok concrete =>
      checkedAnswer n (evalProg concrete fuel)

def evalPrepared (p : Prepared) (fuel : Nat) : RunResult :=
  if p.source.answerSide.isSome then evalAnswer p fuel else evalProg p fuel

def runWithAnswer (src : String) (_input : Input) (fuel : Nat) : Except String RunResult := do
  let p ← parse src
  return evalPrepared p fuel

end Langlib.JavaGen
