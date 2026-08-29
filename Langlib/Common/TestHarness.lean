import Langlib.Common.Io

/-!
# Golden-test harness

Languages register golden tests (program + input + expected output) as
`Suite`s; `Langlib/Tests/Main.lean` runs every registered suite. Tests run
against the pure interpreter cores, so `lake test` needs no subprocesses.

Program sources may be inline strings or files (paths relative to the
repository root, e.g. `Langlib/Examples/Brainfuck/hello.b`); run
`lake test` from the repository root.
-/

namespace Langlib.Common

/-- Where a test's program text comes from. -/
inductive Source where
  | inline (src : String)
  | file (path : System.FilePath)

/-- What a test expects of the run. -/
inductive Expectation where
  /-- Halts normally with exactly this output. -/
  | outputs (s : String)
  /-- Halts normally with exactly these output bytes. -/
  | outputsBytes (b : ByteArray)
  /-- Halts normally and the output equals the program's own source text
  (quines). With a `Source.file` program, keep the file byte-exact: no
  comments, no trailing newline. -/
  | selfReproduces
  /-- Runs out of fuel (used to pin down intentional divergence). -/
  | diverges
  /-- Fails at runtime; the message must contain the given substring. -/
  | runtimeError (msgPart : String)
  /-- Fails to parse; the message must contain the given substring. -/
  | parseError (msgPart : String)

structure TestCase where
  name : String
  source : Source
  input : String := ""
  expect : Expectation
  fuel : Nat := 50_000_000

structure Suite where
  /-- Language (or component) name, printed in the report. -/
  name : String
  /-- The language's parse-and-run entry point, as in `Runner.run`. -/
  run : String → Input → Nat → Except String RunResult
  cases : List TestCase

namespace Suite

private def show80 (s : String) : String :=
  let s := s.replace "\n" "\\n"
  if s.length > 80 then (s.take 77).toString ++ "..." else s

/-- Run one case; `none` means pass, `some msg` describes the failure. -/
def runCase (s : Suite) (c : TestCase) : IO (Option String) := do
  let src ← match c.source with
    | .inline src => pure src
    | .file p =>
      try
        IO.FS.readFile p
      catch _ =>
        return some s!"cannot read {p} (run `lake test` from the repo root)"
  let res := s.run src (Input.ofString c.input) c.fuel
  match c.expect, res with
  | .parseError part, .error msg =>
    if (msg.splitOn part).length > 1 then return none
    else return some s!"parse error message '{show80 msg}' does not mention '{part}'"
  | _, .error msg => return some s!"unexpected parse error: {show80 msg}"
  | .parseError part, .ok _ => return some s!"expected a parse error mentioning '{part}'"
  | .outputs want, .ok r =>
    match r.exit with
    | .halted =>
      let got := r.outputString
      if got == want then return none
      else return some s!"output mismatch:\n  want: {show80 want}\n  got:  {show80 got}"
    | .outOfFuel => return some "ran out of fuel (expected normal halt)"
    | .error m => return some s!"runtime error (expected normal halt): {show80 m}"
  | .selfReproduces, .ok r =>
    match r.exit with
    | .halted =>
      let got := r.outputString
      if got == src then return none
      else return some s!"not a quine:\n  source: {show80 src}\n  output: {show80 got}"
    | .outOfFuel => return some "ran out of fuel (expected normal halt)"
    | .error m => return some s!"runtime error (expected normal halt): {show80 m}"
  | .outputsBytes want, .ok r =>
    match r.exit with
    | .halted =>
      if r.output == want then return none
      else return some s!"output bytes mismatch ({r.output.size} bytes vs expected {want.size})"
    | .outOfFuel => return some "ran out of fuel (expected normal halt)"
    | .error m => return some s!"runtime error (expected normal halt): {show80 m}"
  | .diverges, .ok r =>
    match r.exit with
    | .outOfFuel => return none
    | .halted => return some "halted (expected to run out of fuel)"
    | .error m => return some s!"runtime error (expected out-of-fuel): {show80 m}"
  | .runtimeError part, .ok r =>
    match r.exit with
    | .error m =>
      if (m.splitOn part).length > 1 then return none
      else return some s!"error message '{show80 m}' does not mention '{part}'"
    | .halted => return some s!"halted (expected runtime error mentioning '{part}')"
    | .outOfFuel => return some s!"out of fuel (expected runtime error mentioning '{part}')"

/-- Run a suite, print a report, return the number of failures. -/
def runAll (s : Suite) : IO Nat := do
  let mut failures := 0
  IO.println s!"── {s.name} ({s.cases.length} tests)"
  for c in s.cases do
    match ← s.runCase c with
    | none => IO.println s!"  ok   {c.name}"
    | some msg =>
      failures := failures + 1
      IO.println s!"  FAIL {c.name}: {msg}"
  return failures

end Suite

/-- Run several suites and produce a process exit code. -/
def runSuites (suites : List Suite) : IO UInt32 := do
  let mut failures := 0
  let mut total := 0
  for s in suites do
    total := total + s.cases.length
    failures := failures + (← s.runAll)
  if failures == 0 then
    IO.println s!"all {total} tests passed"
    return 0
  else
    IO.println s!"{failures} of {total} tests FAILED"
    return 1

end Langlib.Common
