import Langlib.Common.Io
import Langlib.Languages.JavaGen.Parser

/-!
# JavaGen: the subtyping machine

The two step cases implement §4 of Grigore's paper. Every continuation
reverses the argument comparison. Successful executions retain queries and
inheritance paths, including the state before ground inheritance erases it.
This generic record is not yet a certified decoder for simulated URM answers.
-/

namespace Langlib.JavaGen
open Langlib.Common

structure Frame where
  query : Query
  inheritance : List Ty
deriving Repr, BEq, DecidableEq, Inhabited

def Frame.render (f : Frame) : String :=
  f.query.render ++ "\n" ++
    String.join (f.inheritance.map (fun t => "  via " ++ t.render ++ "\n"))

inductive Step where
  | accept (frame : Frame)
  | next (frame : Frame) (query : Query)
  | reject
deriving Repr, BEq, DecidableEq, Inhabited

/-- One subtype inference, including its finite inheritance lookup. -/
def step (p : Prepared) (q : Query) : Step :=
  match p.resolve q.lhs q.rhs.head? with
  | none => .reject
  | some (super, path) =>
    let frame : Frame := ⟨q, path⟩
    match q.rhs, super with
    | [], [] => .accept frame
    | _ :: targetArg, _ :: sourceArg => .next frame ⟨targetArg, sourceArg⟩
    | _, _ => .reject

structure State where
  query : Query
  /-- Most recent inference first; reversed only when serializing success. -/
  history : List Frame := []
deriving Repr, Inhabited

/-- Zero fuel is always inconclusive. Acceptance and rejection each cost a step. -/
def exec (p : Prepared) : Nat → State → State × Exit
  | 0, st => (st, .outOfFuel)
  | fuel + 1, st =>
    match step p st.query with
    | .accept frame => ({ st with history := frame :: st.history }, .halted)
    | .reject => (st, .error ("not a subtype: " ++ st.query.render))
    | .next frame q => exec p fuel ⟨q, frame :: st.history⟩

/-- A successful proof record; rejection and incomplete search emit no bytes. -/
def result (r : State × Exit) : RunResult :=
  { exit := r.2, output := if r.2 == .halted then
      ("accepted\n" ++ String.join (r.1.history.reverse.map Frame.render)).toUTF8
    else .empty }

def evalProg (p : Prepared) (fuel : Nat) : RunResult :=
  if p.source.answerSide.isSome then
    { exit := .error "unbound answer: use the answer evaluator" }
  else result (exec p fuel ⟨p.source.query, []⟩)

/-- Parse and run; all input is in the query, so the byte stream is ignored. -/
def run (src : String) (_input : Input) (fuel : Nat) : Except String RunResult := do
  return evalProg (← parse src) fuel

end Langlib.JavaGen
