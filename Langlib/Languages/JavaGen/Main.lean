import Langlib.Common.Runner
import Langlib.Languages.JavaGen.Answer
import Langlib.Languages.JavaGen.Java

/-! # JavaGen: run a subtype machine or export its query to Java. -/

namespace Langlib.JavaGen
open Langlib.Common

def runner : Runner where
  name := "javagen"
  ext := "jgen"
  run := runWithAnswer
  defaultFuel := 100_000
  usageExtra :=
    [ "  stdin is ignored; successful queries emit their proof record"
    , "  --java FILE             export Java source to stdout"
    , "  --java-declarations FILE export declarations without a query"
    , "  --answer N --java FILE  specialize an answer query for Java checking"
    , "  numeric answers: inference and concrete checking each get --fuel N" ]

private def exportFile (file : String) (query : Bool) (answer : Option Nat := none) : IO UInt32 := do
  let source ← try IO.FS.readFile file catch e =>
    IO.eprintln s!"javagen: cannot read '{file}': {e}"
    return 3
  match parse source with
  | .error msg => IO.eprintln s!"javagen: {msg}"; return 3
  | .ok p =>
    let specialized ← match answer with
      | none =>
        if query && p.source.answerSide.isSome then
          IO.eprintln "javagen: supply --answer N to export an answer query"
          return 3
        pure p
      | some n =>
        unless p.source.answerSide.isSome do
          IO.eprintln "javagen: --answer requires an answer hole in the original query"
          return 3
        match prepare (p.source.bindAnswer n) with
        | .error msg => IO.eprintln s!"javagen: {msg}"; return 3
        | .ok q => pure q
    IO.print (exportJava specialized query)
    return 0

def main (args : List String) : IO UInt32 :=
  match args with
  | ["--java", file] => exportFile file true
  | ["--java-declarations", file] => exportFile file false
  | ["--answer", n, "--java", file] =>
    match n.toNat? with
    | none => do IO.eprintln "javagen: --answer expects a natural number"; return 3
    | some n => exportFile file true (some n)
  | _ => runner.main args

end Langlib.JavaGen

def main (args : List String) : IO UInt32 := Langlib.JavaGen.main args
