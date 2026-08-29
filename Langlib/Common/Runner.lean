import Langlib.Common.Io

/-!
# Shared standalone-runner scaffolding

Every language exposes a runner executable (`lake exe <langname> file`).
This module implements the parts they all share: reading the program file
and stdin, invoking the language's pure `run` function, writing the output,
and mapping the `Exit` to a process exit code.

Exit codes: `0` normal halt, `1` runtime error, `2` out of fuel,
`3` parse/usage error.
-/

namespace Langlib.Common

/-- Everything a language must provide to get a standalone runner. -/
structure Runner where
  /-- Language name, as printed in usage and error messages. -/
  name : String
  /-- Customary source-file extension, for the usage message (e.g. `"b"`). -/
  ext : String
  /-- Parse and run: source text, input stream, fuel. `Except` carries parse
  errors; runtime errors are reported inside `RunResult`. -/
  run : String → Input → Nat → Except String RunResult
  /-- Default fuel bound, overridable with `--fuel N`. -/
  defaultFuel : Nat := 200_000_000
  /-- Extra lines appended to the usage message. Languages with their own
  flags (e.g. brainfuck's `--eof`) pre-process those in their `main` before
  delegating to `Runner.main`, and document them here. -/
  usageExtra : List String := []

namespace Runner

def usage (r : Runner) : String :=
  String.intercalate "\n" <|
    [ s!"usage: lake exe {r.name} [--fuel N] [--verbose] <file.{r.ext}>"
    , "  --fuel N   maximum number of execution steps (default: " ++
        toString r.defaultFuel ++ ")"
    , "  --verbose  report how the run ended on stderr"
    , "  input is read from stdin (piped or redirected; when stdin is an"
    , "  interactive terminal the program sees empty input); output goes"
    , "  to stdout" ]
    ++ r.usageExtra

/-- The shared `main`. Languages define
`def main (args : List String) : IO UInt32 := (runner).main args`. -/
def main (r : Runner) (args : List String) : IO UInt32 := do
  let mut fuel := r.defaultFuel
  let mut file? : Option String := none
  let mut verbose := false
  let mut rest := args
  repeat
    match rest with
    | [] => break
    | "--help" :: _ =>
      IO.println r.usage
      return 0
    | "--verbose" :: rs =>
      verbose := true; rest := rs
    | "--fuel" :: n :: rs =>
      match n.toNat? with
      | some k => fuel := k; rest := rs
      | none =>
        IO.eprintln s!"{r.name}: --fuel expects a number, got '{n}'"
        return 3
    | a :: rs =>
      if a.startsWith "--" then
        IO.eprintln s!"{r.name}: unknown flag '{a}'"
        IO.eprintln r.usage
        return 3
      else if file?.isSome then
        IO.eprintln s!"{r.name}: more than one input file"
        return 3
      else
        file? := some a; rest := rs
  let some file := file? |
    IO.eprintln r.usage
    return 3
  let src ← try
      IO.FS.readFile file
    catch e =>
      IO.eprintln s!"{r.name}: cannot read '{file}': {e}"
      return 3
  -- Reading an interactive terminal to EOF would block before the program
  -- even runs, so a TTY stdin means empty input (pipe or redirect instead).
  let stdinStream ← IO.getStdin
  let stdin ← if ← stdinStream.isTty then pure ByteArray.empty
              else stdinStream.readBinToEnd
  match r.run src (Input.ofByteArray stdin) fuel with
  | .error parseErr =>
    IO.eprintln s!"{r.name}: {parseErr}"
    return 3
  | .ok res =>
    let out ← IO.getStdout
    out.write res.output
    out.flush
    if verbose then
      let exitDesc := match res.exit with
        | .halted => "halted normally"
        | .error msg => s!"runtime error: {msg}"
        | .outOfFuel => s!"ran out of fuel ({fuel} steps)"
      IO.eprintln s!"{r.name}: {exitDesc}; read {stdin.size} input byte(s), wrote {res.output.size} output byte(s)"
    match res.exit with
    | .halted => return 0
    | .error msg =>
      IO.eprintln s!"{r.name}: runtime error: {msg}"
      return 1
    | .outOfFuel =>
      IO.eprintln s!"{r.name}: out of fuel after {fuel} steps (raise with --fuel)"
      return 2

end Runner

end Langlib.Common
