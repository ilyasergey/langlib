import Langlib.Common.Runner
import Langlib.WTF.Semantics

/-!
# WTF: standalone runner

```
lake exe wtf run [--fuel N] [--verbose] file.wtf   # parse, check, run
lake exe wtf check file.wtf                        # parse and type-check only
lake exe wtf [--fuel N] file.wtf                   # 'run' is the default
```

Compilation subcommands (`wtf compile --to <lang>`) arrive with Stage 4 of
`docs/PLAN.md`.
-/

namespace Langlib.WTF

open Langlib.Common

def runner : Runner where
  name := "wtf"
  ext := "wtf"
  run := run
  usageExtra :=
    [ "subcommands:"
    , "  run <file.wtf>    parse, type-check, and run (the default)"
    , "  check <file.wtf>  parse and type-check only" ]

def checkMain (file : String) : IO UInt32 := do
  let src ← try
      IO.FS.readFile file
    catch e =>
      IO.eprintln s!"wtf: cannot read '{file}': {e}"
      return 3
  match parse src with
  | .error e =>
    IO.eprintln s!"wtf: parse error: {e}"
    return 3
  | .ok prog =>
    match checkProgram prog with
    | .error e =>
      IO.eprintln s!"wtf: type error: {e}"
      return 1
    | .ok Γ =>
      IO.println s!"{file}: well-typed formalism ({Γ.size} variable(s), {prog.decls.length} declaration(s))"
      return 0

end Langlib.WTF

open Langlib.WTF in
def main (args : List String) : IO UInt32 := do
  match args with
  | "check" :: [file] => checkMain file
  | "check" :: _ =>
    IO.eprintln "usage: lake exe wtf check <file.wtf>"
    return 3
  | "run" :: rest => runner.main rest
  | rest => runner.main rest
