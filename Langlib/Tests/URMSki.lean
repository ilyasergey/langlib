import Langlib.Common.TestHarness
import Langlib.Computability.Ski

/-!
Tests for the certified compiler into the SKI calculus.

Two suites, because the target's reference interpreter is the slow half.
`Langlib.Ski.step` rescans the whole term to find the leftmost redex, so a
run costs the size of the term times the number of steps, and a URM program
with even one instruction is out of reach: the counter machine's dispatcher
runs millions of steps on a term of ten thousand combinators.

* The **URM suite** therefore covers what does finish end to end: the empty
  program, whose answer is the first component of the input vector. It still
  exercises the whole pipeline, since `counterProgram` loads the inputs,
  runs the dispatcher to a halt, and encodes the answer by emitting bytes.
* The **counter suite** tests the half of the compiler that is new here, on
  hand-written counter-machine programs, against an executable counter
  interpreter written below. Those run in milliseconds and cover increment,
  decrement, emit, loops and nested loops.
-/

namespace Langlib.Tests.URMSki

open Langlib.Common
open Langlib.Computability.Counter
open Langlib.Computability.URMSki
open Cslib.URM (Program Instr)

/-! ## Shared token handling -/

private def toks (line : String) : List String :=
  let body := match line.splitOn "#" with
    | [] => ""
    | h :: _ => h
  (body.splitOn " ").flatMap (fun t => t.splitOn "\t") |>.filter (fun t => t ≠ "")

private def parseNat (t : String) : Except String Nat :=
  match t.toNat? with
  | some n => .ok n
  | none => .error s!"not a number: '{t}'"

/-! ## The URM suite -/

private def parseLine (line : String) : Except String (Option (Sum (List Nat) Instr)) := do
  match toks line with
  | [] => return none
  | "in" :: rest => return some (.inl (← rest.mapM parseNat))
  | ["Z", a] => return some (.inr (.Z (← parseNat a)))
  | ["S", a] => return some (.inr (.S (← parseNat a)))
  | ["T", a, b] => return some (.inr (.T (← parseNat a) (← parseNat b)))
  | ["J", a, b, q] =>
    return some (.inr (.J (← parseNat a) (← parseNat b) (← parseNat q)))
  | ts => .error s!"bad URM line: {String.intercalate " " ts}"

private def parseURM (src : String) : Except String (Program × List Nat) := do
  let mut prog : List Instr := []
  let mut inputs : List Nat := []
  for line in src.splitOn "\n" do
    match ← parseLine line with
    | none => pure ()
    | some (.inl vs) => inputs := vs
    | some (.inr i) => prog := prog ++ [i]
  return (prog, inputs)

private def urmSteps : Nat := 10000

/-- Compile, normalise, and compare with the executable URM reference. -/
def runURM (src : String) (_input : Input) (fuel : Nat) : Except String RunResult := do
  let (P, inputs) ← parseURM src
  if ¬ Langlib.Computability.URM.haltsIn P (Cslib.URM.State.init inputs) urmSteps then
    .error s!"the URM program did not halt within {urmSteps} steps"
  else
    let want := Langlib.Computability.URM.result P inputs urmSteps
    let prog := compile P inputs
    let r := Langlib.Ski.evalProg prog fuel
    match r.exit with
    | .halted =>
      match decodeOutput r.output with
      | some got =>
        if got == want then
          return { output := s!"ok {want}".toUTF8, exit := .halted }
        else
          return { exit := .error s!"URM says {want}, compiled SKI says {got}" }
      | none => return { exit := .error "the output did not decode" }
    | .outOfFuel => return { exit := .error s!"compiled program ran out of fuel ({fuel})" }
    | .error msg => return { exit := .error s!"compiled program failed: {msg}" }

/-- Report the number of combinators, for a stable cost regression. -/
def sizeOfURM (src : String) (_input : Input) (_fuel : Nat) : Except String RunResult := do
  let (P, inputs) ← parseURM src
  return { output := s!"{(compile P inputs).size}".toUTF8, exit := .halted }

/-! ## The counter suite

Concrete syntax: `regs` gives the initial register values, `+r` and `-r`
increment and decrement, `.` emits a byte, and `[r` ... `]` is the loop.
-/

private partial def parseCode (ts : List String) : Except String (Code × List String) := do
  match ts with
  | [] => return ([], [])
  | "]" :: rest => return ([], "]" :: rest)
  | t :: rest =>
    if t == "." then
      let (cs, left) ← parseCode rest
      return (Cmd.emit :: cs, left)
    else if t.startsWith "+" then
      let r ← parseNat (t.drop 1).toString
      let (cs, left) ← parseCode rest
      return (Cmd.inc r :: cs, left)
    else if t.startsWith "-" then
      let r ← parseNat (t.drop 1).toString
      let (cs, left) ← parseCode rest
      return (Cmd.dec r :: cs, left)
    else if t.startsWith "[" then
      let r ← parseNat (t.drop 1).toString
      let (body, left) ← parseCode rest
      match left with
      | "]" :: after =>
        let (cs, left') ← parseCode after
        return (Cmd.loop r body :: cs, left')
      | _ => .error "unclosed '['"
    else
      .error s!"bad counter token: '{t}'"

private def parseCounter (src : String) : Except String (Code × List Nat) := do
  let mut regs : List Nat := []
  let mut body : List String := []
  for line in src.splitOn "\n" do
    match toks line with
    | [] => pure ()
    | "regs" :: rest => regs := (← rest.mapM parseNat)
    | ts => body := body ++ ts
  let (c, left) ← parseCode body
  if left ≠ [] then .error "trailing ']'" else return (c, regs)

/-- An executable counter machine, to compare the compiled term against. -/
private def evalCode : Nat → Code → List Nat → Nat → Option (List Nat × Nat)
  | 0, _, _, _ => none
  | _ + 1, [], regs, out => some (regs, out)
  | f + 1, Cmd.inc r :: cs, regs, out =>
      evalCode f cs (regs.set r (regs.getD r 0 + 1)) out
  | f + 1, Cmd.dec r :: cs, regs, out =>
      evalCode f cs (regs.set r (regs.getD r 0 - 1)) out
  | f + 1, Cmd.emit :: cs, regs, out => evalCode f cs regs (out + 1)
  | f + 1, Cmd.loop r b :: cs, regs, out =>
      if regs.getD r 0 = 0 then evalCode f cs regs out
      else evalCode f (b ++ Cmd.loop r b :: cs) regs out

/-- Compile a counter program and compare its answer with the interpreter's. -/
def runCounter (src : String) (_input : Input) (fuel : Nat) : Except String RunResult := do
  let (c, regs) ← parseCounter src
  match evalCode 100000 c regs 0 with
  | none => .error "the counter program did not halt"
  | some (_, want) =>
    let R := regs.length
    let prog := .app unaryT
      (.app (getT R) (.app (codeT R c) (listT (regs ++ [0]))))
    match Langlib.Ski.normalise fuel prog with
    | none => return { exit := .error s!"compiled program ran out of fuel ({fuel})" }
    | some nf =>
      match decodeOutput ((nf.render ++ "\n").toUTF8) with
      | some got =>
        if got == want then
          return { output := s!"ok {want}".toUTF8, exit := .halted }
        else
          return { exit := .error s!"counter machine says {want}, compiled SKI says {got}" }
      | none => return { exit := .error "the output did not decode" }

private def skiFuel : Nat := 4000000

def urmSuite : Suite where
  name := "urm -> ski (certified compiler)"
  run := runURM
  cases :=
    [ { name := "the empty program answers with input 0", fuel := skiFuel,
        source := .inline "in 3", expect := .outputs "ok 3" }
    , { name := "and with a zero answer", fuel := skiFuel,
        source := .inline "in 0 5", expect := .outputs "ok 0" }
    , { name := "and with no input vector at all", fuel := skiFuel,
        source := .inline "", expect := .outputs "ok 0" }
    ]

def counterSuite : Suite where
  name := "counter machine -> ski (certified back half)"
  run := runCounter
  cases :=
    [ { name := "emit once", fuel := skiFuel,
        source := .inline "regs 0\n+0 [0 -0 . ]", expect := .outputs "ok 1" }
    , { name := "a counted loop", fuel := skiFuel,
        source := .inline "regs 0\n+0 +0 +0 [0 -0 . ]", expect := .outputs "ok 3" }
    , { name := "a loop that never runs", fuel := skiFuel,
        source := .inline "regs 0 4\n[0 -0 . ]", expect := .outputs "ok 0" }
    , { name := "nested loops multiply", fuel := skiFuel,
        source := .inline "regs 0 0\n+0 +0 +1 +1 [0 -0 [1 -1 . ] ]",
        expect := .outputs "ok 2" }
    , { name := "a copy loop, then emit the copy", fuel := skiFuel,
        source := .inline "regs 0 0\n+0 +0 +0 +0 [0 -0 +1 ] [1 -1 . ]",
        expect := .outputs "ok 4" }
    , { name := "registers start from the header", fuel := skiFuel,
        source := .inline "regs 2 0\n[0 -0 . ]", expect := .outputs "ok 2" }
    ]

def sizeSuite : Suite where
  name := "urm -> ski (compiled term size)"
  run := sizeOfURM
  cases :=
    [ { name := "the empty program", source := .inline "in 3",
        expect := .outputs "1004" }
    ]

def suites : List Suite := [urmSuite, counterSuite, sizeSuite]

end Langlib.Tests.URMSki
