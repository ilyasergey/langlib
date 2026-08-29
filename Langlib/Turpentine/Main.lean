import Langlib.Common.Runner
import Langlib.Turpentine.Semantics
import Langlib.Turpentine.Compile.Subleq
import Langlib.Turpentine.Compile.Whitespace

/-!
# Turpentine: standalone runner

```
lake exe turpentine run [--fuel N] [--verbose] file.turp   # parse, check, run
lake exe turpentine check file.turp                        # parse and type-check only
lake exe turpentine compile --to <lang> file.turp          # emit target source
lake exe turpentine [--fuel N] file.turp                   # 'run' is the default
```

`compile` writes the target program to stdout, or to a file with `-o`.
Backends and their supported fragments are documented in
`docs/<langname>/compiler.md`.
-/

namespace Langlib.Turpentine

open Langlib.Common

/-- The compilation backends, by the name accepted after `--to`. -/
def backends : List (String × (String → Except String String)) :=
  [ ("whitespace", Compile.Whitespace.compileSource)
  , ("subleq", Compile.Subleq.compileSource) ]

def backendNames : String :=
  String.intercalate "|" (backends.map (·.1))

def runner : Runner where
  name := "turpentine"
  ext := "turp"
  run := run
  usageExtra :=
    [ "subcommands:"
    , "  run <file.turp>              parse, type-check, and run (the default)"
    , "  check <file.turp>            parse and type-check only"
    , s!"  compile --to <{backendNames}> [-o out] <file.turp>" ]

def checkMain (file : String) : IO UInt32 := do
  let src ← try
      IO.FS.readFile file
    catch e =>
      IO.eprintln s!"turpentine: cannot read '{file}': {e}"
      return 3
  match parse src with
  | .error e =>
    IO.eprintln s!"turpentine: parse error: {e}"
    return 3
  | .ok prog =>
    match checkProgram prog with
    | .error e =>
      IO.eprintln s!"turpentine: type error: {e}"
      return 1
    | .ok Γ =>
      IO.println s!"{file}: well typed ({Γ.size} variable(s), {prog.decls.length} declaration(s))"
      return 0

/-- `compile --to <lang> [-o out] <file.turp>`. -/
def compileMain (args : List String) : IO UInt32 := do
  let mut target? : Option String := none
  let mut out? : Option String := none
  let mut file? : Option String := none
  let mut rest := args
  repeat
    match rest with
    | [] => break
    | "--to" :: t :: rs => target? := some t; rest := rs
    | "-o" :: o :: rs => out? := some o; rest := rs
    | a :: rs =>
      if a.startsWith "-" then
        IO.eprintln s!"turpentine compile: unknown flag '{a}'"
        return 3
      else if file?.isSome then
        IO.eprintln "turpentine compile: more than one input file"
        return 3
      else
        file? := some a; rest := rs
  let some target := target? |
    IO.eprintln s!"turpentine compile: pass --to <{backendNames}>"
    return 3
  let some file := file? |
    IO.eprintln "turpentine compile: no input file"
    return 3
  let some (_, backend) := backends.find? (·.1 == target) |
    IO.eprintln s!"turpentine compile: unknown target '{target}' (expected {backendNames})"
    return 3
  let src ← try
      IO.FS.readFile file
    catch e =>
      IO.eprintln s!"turpentine: cannot read '{file}': {e}"
      return 3
  match backend src with
  | .error e =>
    IO.eprintln s!"turpentine compile: {e}"
    return 1
  | .ok target =>
    match out? with
    | some path =>
      IO.FS.writeFile path target
      IO.eprintln s!"turpentine: wrote {target.length} bytes to {path}"
    | none => IO.print target
    return 0

end Langlib.Turpentine

open Langlib.Turpentine in
def main (args : List String) : IO UInt32 := do
  match args with
  | "check" :: [file] => checkMain file
  | "check" :: _ =>
    IO.eprintln "usage: lake exe turpentine check <file.turp>"
    return 3
  | "compile" :: rest => compileMain rest
  | "run" :: rest => runner.main rest
  | rest => runner.main rest
