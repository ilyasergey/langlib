import Langlib.Common.Runner
import Langlib.Turpentine.Semantics
import Langlib.Turpentine.Compile.Brainfuck
import Langlib.Turpentine.Compile.Subleq
import Langlib.Turpentine.Compile.Whitespace
import Langlib.Languages.Brainfuck.Semantics
import Langlib.Languages.Subleq.Semantics
import Langlib.Languages.Whitespace.Semantics

/-!
# Turpentine: standalone runner

Three ways to run a `.turp` program, which are three different questions.

**Interpret it.** What does this program do?

```
lake exe turpentine run [--fuel N] [--verbose] file.turp
```

**Emit an esolang.** What does this program look like as brainfuck-family
madness? Writes to stdout, or to a file with `-o`.

```
lake exe turpentine compile --to <lang> [-o out] file.turp
```

**Emit it and run it.** Does the compiled program agree with the
interpreter? Compiles in memory and immediately runs the result on that
language's own reference interpreter, so the output should be identical to
`run`. This is the differential test in a single command.

```
lake exe turpentine exec --via <lang> [--fuel N] [--verbose] file.turp
```

Plus `check`, which type-checks without running anything. Backends and
their supported fragments are documented in `docs/<langname>/compiler.md`.
-/

namespace Langlib.Turpentine

open Langlib.Common

/-- A compilation backend: how to emit the target's source text, and how
to run that text on the target's own reference interpreter. Adding a
backend is one entry here. -/
structure Backend where
  /-- Name accepted after `--to` and `--via`. -/
  name : String
  /-- Turpentine source text to target source text. -/
  compileSource : String → Except String String
  /-- The target language's parse-and-run, for `exec`. -/
  runTarget : String → Input → Nat → Except String RunResult

def backends : List Backend :=
  [ { name := "brainfuck"
    , compileSource := Compile.Brainfuck.compileSource
      -- The backend emits programs that expect `--eof zero`: its
      -- `readByte` reports -1 for a zero byte or end of input alike.
    , runTarget := Langlib.Brainfuck.run { eof := .zero } }
  , { name := "whitespace"
    , compileSource := Compile.Whitespace.compileSource
    , runTarget := Langlib.Whitespace.run }
  , { name := "subleq"
    , compileSource := Compile.Subleq.compileSource
    , runTarget := Langlib.Subleq.run } ]

def backendNames : String :=
  String.intercalate "|" (backends.map (·.name))

def findBackend? (n : String) : Option Backend :=
  backends.find? (·.name == n)

def runner : Runner where
  name := "turpentine"
  ext := "turp"
  run := run
  usageExtra :=
    [ "subcommands:"
    , "  run <file.turp>                    parse, type-check, and run (the default)"
    , "  check <file.turp>                  parse and type-check only"
    , s!"  compile --to <{backendNames}> [-o out] <file.turp>"
    , "                                     emit the target program"
    , s!"  exec --via <{backendNames}> <file.turp>"
    , "                                     compile, then run on that language's interpreter" ]

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
  let some backend := findBackend? target |
    IO.eprintln s!"turpentine compile: unknown target '{target}' (expected {backendNames})"
    return 3
  let src ← try
      IO.FS.readFile file
    catch e =>
      IO.eprintln s!"turpentine: cannot read '{file}': {e}"
      return 3
  match backend.compileSource src with
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

/-- `exec --via <lang> [--fuel N] [--verbose] <file.turp>`: compile in
memory, then run the emitted program on that language's own reference
interpreter. The output should match `run` exactly, which is what makes
this a differential test rather than a convenience. -/
def execMain (args : List String) : IO UInt32 := do
  let mut target? : Option String := none
  let mut file? : Option String := none
  let mut fuel := 200_000_000
  let mut verbose := false
  let mut rest := args
  repeat
    match rest with
    | [] => break
    | "--via" :: t :: rs => target? := some t; rest := rs
    | "--verbose" :: rs => verbose := true; rest := rs
    | "--fuel" :: n :: rs =>
      match n.toNat? with
      | some k => fuel := k; rest := rs
      | none =>
        IO.eprintln s!"turpentine exec: --fuel expects a number, got '{n}'"
        return 3
    | a :: rs =>
      if a.startsWith "-" then
        IO.eprintln s!"turpentine exec: unknown flag '{a}'"
        return 3
      else if file?.isSome then
        IO.eprintln "turpentine exec: more than one input file"
        return 3
      else
        file? := some a; rest := rs
  let some target := target? |
    IO.eprintln s!"turpentine exec: pass --via <{backendNames}>"
    return 3
  let some file := file? |
    IO.eprintln "turpentine exec: no input file"
    return 3
  let some backend := findBackend? target |
    IO.eprintln s!"turpentine exec: unknown target '{target}' (expected {backendNames})"
    return 3
  let src ← try
      IO.FS.readFile file
    catch e =>
      IO.eprintln s!"turpentine: cannot read '{file}': {e}"
      return 3
  match backend.compileSource src with
  | .error e =>
    IO.eprintln s!"turpentine exec: {e}"
    return 1
  | .ok targetSrc =>
    if verbose then
      IO.eprintln s!"turpentine: compiled to {targetSrc.length} bytes of {target}"
    let stdinStream ← IO.getStdin
    let stdinBytes ← if ← stdinStream.isTty then pure ByteArray.empty
                     else stdinStream.readBinToEnd
    match backend.runTarget targetSrc (Input.ofByteArray stdinBytes) fuel with
    | .error e =>
      IO.eprintln s!"turpentine exec: the emitted {target} program did not parse: {e}"
      return 1
    | .ok res =>
      let out ← IO.getStdout
      out.write res.output
      out.flush
      match res.exit with
      | .halted => return 0
      | .error msg =>
        IO.eprintln s!"turpentine exec: {target} runtime error: {msg}"
        return 1
      | .outOfFuel =>
        IO.eprintln s!"turpentine exec: out of fuel after {fuel} steps of {target} (raise with --fuel)"
        return 2

end Langlib.Turpentine

open Langlib.Turpentine in
def main (args : List String) : IO UInt32 := do
  match args with
  | "check" :: [file] => checkMain file
  | "check" :: _ =>
    IO.eprintln "usage: lake exe turpentine check <file.turp>"
    return 3
  | "compile" :: rest => compileMain rest
  | "exec" :: rest => execMain rest
  | "run" :: rest => runner.main rest
  | rest => runner.main rest
