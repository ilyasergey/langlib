import Langlib.Languages.JavaGen.Semantics
import Std.Data.HashMap

/-! # Numeric observation for compiled counter programs

The compiler stores `answer` as occurrences of `Letter_1` in a padded tape.
Observe that tape in the last sweeper control query before ground inheritance
erases it. Execution uses the ordinary subtype `step`, retaining only this
query instead of the full proof history. This mode does not infer an answer
hole or certify a numeric specialization with Java.
-/

namespace Langlib.JavaGen.CompiledAnswer
open Langlib.Common

private def tapeAnswer : Ty → Option Nat
  | ["End", "End"] => some 0
  | letter :: "ScanPad" :: rest => do
    let n ← (letter.drop "Letter_".length).toString.toNat?
    unless letter == "Letter_" ++ toString n do none
    let answer ← tapeAnswer rest
    return answer + if n == 1 then 1 else 0
  | _ => none

/-- Decode only a complete boundary tape containing the answer register marker. -/
def decode (q : Query) : Option Nat := do
  let head :: tape := q.lhs | none
  unless head.startsWith "State_" && q.rhs == ["End", "End"] &&
      tape.contains "Letter_0" do none
  tapeAnswer tape

/-- Index the validated closure by source head. The ordinary `step` only reads
that row; it need not linearly search every generated control-state declaration. -/
private def execIndexed (p : Prepared) (index : Std.HashMap String (List Ancestor)) :
    Nat → Query → Option Query → RunResult
  | 0, _, _ => { exit := .outOfFuel }
  | fuel + 1, q, last =>
    let last := if q.lhs.headD "" |>.startsWith "State_" then some q else last
    let focused := match q.lhs with
      | [] => p
      | head :: _ => { p with closure := [(head, index[head]?.getD [])] }
    match step focused q with
    | .reject => { exit := .error ("not a subtype: " ++ q.render) }
    | .next _ next => execIndexed p index fuel next last
    | .accept _ =>
      match last.bind decode with
      | some n => { exit := .halted, output := (toString n ++ "\n").toUTF8 }
      | none => { exit := .error "not a compiled counter answer" }

/-- Same subtype transitions and fuel costs; retain only the last control query. -/
def exec (p : Prepared) (fuel : Nat) (q : Query) (last : Option Query) : RunResult :=
  execIndexed p (Std.HashMap.ofList p.closure) fuel q last

def run (src : String) (_input : Input) (fuel : Nat) : Except String RunResult := do
  let p ← parse src
  if p.source.answerSide.isSome then
    throw "--compiled-answer requires a closed compiled counter query"
  return exec p fuel p.source.query none

end Langlib.JavaGen.CompiledAnswer
