import Langlib.Common.Runner
import Langlib.Turpentine.Semantics
import Langlib.Turpentine.Compile.Brainfuck
import Langlib.Turpentine.Compile.Subleq
import Langlib.Turpentine.Compile.Whitespace
import Langlib.Languages.Brainfuck.Semantics
import Langlib.Languages.Subleq.Semantics
import Langlib.Languages.Whitespace.Semantics
import Langlib.Computability.Derived

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
  /-- The *certified* compiler for this target, when one exists: obtained
  from the language's Turing-completeness proof rather than written by
  hand, and correct by construction. Accepts only the I/O-free fragment
  described in `docs/certified-compilation.md`. -/
  certified : Option (String → Except String String) := none

def backends : List Backend :=
  [ { name := "brainfuck"
    , compileSource := Compile.Brainfuck.compileSource
      -- The backend emits programs that expect `--eof zero`: its
      -- `readByte` reports -1 for a zero byte or end of input alike.
    , runTarget := Langlib.Brainfuck.run { eof := .zero }
    , certified := some fun src => do
        let p ← parse src
        let prog ← Langlib.Computability.derivedBrainfuck.compile p
        return Langlib.Brainfuck.Prog.render prog }
  , { name := "whitespace"
    , compileSource := Compile.Whitespace.compileSource
    , runTarget := Langlib.Whitespace.run
    , certified := some fun src => do
        let p ← parse src
        let prog ← Langlib.Computability.derivedWhitespace.compile p
        return Langlib.Whitespace.Prog.render prog }
  , { name := "subleq"
    , compileSource := Compile.Subleq.compileSource
    , runTarget := Langlib.Subleq.run
    , certified := some fun src => do
        let p ← parse src
        let prog ← Langlib.Computability.derivedSubleq.compile p
        return Langlib.Subleq.Prog.render prog } ]

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
    , "                                     compile, then run on that language's interpreter"
    , "compiler choice, for compile and exec:"
    , "  --bespoke    hand-written backend: whole language, compact output, unverified."
    , "               This is the default when neither flag is given."
    , "  --tc         derived from the language's Turing-completeness proof: correct by"
    , "               construction, far larger output, and accepts only the I/O-free"
    , "               fragment (see docs/certified-compilation.md)."
    , "  Either way the chosen scheme is named in the message the command prints." ]

/-- The full help. Turpentine has four subcommands and two compilers, so
the generic `Runner` usage is not enough; this replaces it. -/
def helpText : String :=
  String.intercalate "\n"
    [ "turpentine: the Well-Typed Formalism, LangLib's source language."
    , ""
    , "usage:"
    , "  lake exe turpentine run     [options] <file.turp>"
    , "  lake exe turpentine check              <file.turp>"
    , s!"  lake exe turpentine compile --to  <{backendNames}> [options] <file.turp>"
    , s!"  lake exe turpentine exec    --via <{backendNames}> [options] <file.turp>"
    , ""
    , "subcommands:"
    , "  run       parse, type-check, and interpret. The default: a bare"
    , "            file argument with no subcommand runs the program."
    , "  check     parse and type-check only, then report the variable count."
    , "            Nothing is executed."
    , "  compile   translate to a target language and emit its source."
    , "  exec      translate in memory, then immediately run the result on"
    , "            that target's own interpreter. The output should match"
    , "            `run` exactly, so this doubles as a differential test."
    , ""
    , "choosing a target (compile and exec):"
    , s!"  --to <lang>    for compile; one of {backendNames}"
    , s!"  --via <lang>   for exec; one of {backendNames}"
    , ""
    , "choosing a compiler (compile and exec):"
    , "  --bespoke  hand-written for that target. Accepts the whole language,"
    , "             emits compact code, and is not verified. This is the"
    , "             default when neither flag is given."
    , "  --tc       derived from the target's Turing-completeness proof, by"
    , "             composing it with the shared Turpentine-to-URM pass."
    , "             Correct by construction. Accepts only the I/O-free"
    , "             fragment: no input or output statements, no subtraction,"
    , "             division or modulo, no arrays, no && or ||, and the"
    , "             result must be left in a variable named `answer`."
    , "             Not every target has one; those that do are marked in"
    , "             docs/README.md. See docs/certified-compilation.md."
    , "  Passing both is an error. Whichever is used is named in the message"
    , "  the command prints, so a build log records which compiler ran."
    , ""
    , "output (compile):"
    , "  -o <file>  write the target program to <file>. Without it the"
    , "             program goes to stdout and the note to stderr, so"
    , "             redirecting captures only the program."
    , ""
    , "execution (run and exec):"
    , s!"  --fuel N   step budget before giving up (default {200000000})."
    , "             Running out is reported distinctly from halting."
    , "  --verbose  report on stderr how the run ended, and for exec how"
    , "             large the compiled program was."
    , ""
    , "other:"
    , "  --help     print this message."
    , ""
    , "input and output:"
    , "  Input is read from stdin, piped or redirected; when stdin is an"
    , "  interactive terminal the program sees empty input. Program output"
    , "  goes to stdout, diagnostics to stderr."
    , ""
    , "exit codes:"
    , "  0  the program halted normally"
    , "  1  runtime error, type error, or a program outside the compiler's"
    , "     supported fragment"
    , "  2  out of fuel"
    , "  3  parse error, or a problem with the command line" ]

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
  let mut useCertified := false
  let mut bespokeAsked := false
  let mut rest := args
  repeat
    match rest with
    | [] => break
    | "--to" :: t :: rs => target? := some t; rest := rs
    | "--tc" :: rs =>
      if bespokeAsked then
        IO.eprintln "turpentine compile: pass --bespoke or --tc, not both"
        return 3
      useCertified := true; rest := rs
    | "--bespoke" :: rs =>
      if useCertified then
        IO.eprintln "turpentine compile: pass --bespoke or --tc, not both"
        return 3
      bespokeAsked := true; rest := rs
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
  let (emit, scheme) ← if useCertified then
      match backend.certified with
      | some f => pure (f, "certified, derived from the Turing-completeness proof")
      | none =>
        IO.eprintln s!"turpentine compile: no certified compiler for '{target}' yet"
        return 3
    else pure (backend.compileSource, "bespoke, hand-written and unverified")
  match emit src with
  | .error e =>
    IO.eprintln s!"turpentine compile: {e}"
    if useCertified then
      IO.eprintln "turpentine: the certified compiler accepts only the I/O-free fragment"
      IO.eprintln "  (no input or output, no subtraction, no arrays,"
      IO.eprintln "  and the result in a variable named 'answer')."
      IO.eprintln s!"turpentine: retry with --bespoke to compile the whole language."
    match out? with
    | some path => IO.eprintln s!"turpentine: nothing written to {path}"
    | none => IO.eprintln "turpentine: nothing emitted"
    return 1
  | .ok target =>
    match out? with
    | some path =>
      IO.FS.writeFile path target
      IO.eprintln s!"turpentine: wrote {target.length} bytes to {path} [{scheme}]"
    | none =>
      IO.eprintln s!"turpentine: emitting {target.length} bytes [{scheme}]"
      IO.print target
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
  let mut useCertified := false
  let mut bespokeAsked := false
  let mut rest := args
  repeat
    match rest with
    | [] => break
    | "--via" :: t :: rs => target? := some t; rest := rs
    | "--tc" :: rs =>
      if bespokeAsked then
        IO.eprintln "turpentine exec: pass --bespoke or --tc, not both"
        return 3
      useCertified := true; rest := rs
    | "--bespoke" :: rs =>
      if useCertified then
        IO.eprintln "turpentine exec: pass --bespoke or --tc, not both"
        return 3
      bespokeAsked := true; rest := rs
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
  let (emit, scheme) ← if useCertified then
      match backend.certified with
      | some f => pure (f, "certified, derived from the Turing-completeness proof")
      | none =>
        IO.eprintln s!"turpentine exec: no certified compiler for '{target}' yet"
        return 3
    else pure (backend.compileSource, "bespoke, hand-written and unverified")
  match emit src with
  | .error e =>
    IO.eprintln s!"turpentine exec: {e}"
    if useCertified then
      IO.eprintln "turpentine: the certified compiler accepts only the I/O-free fragment"
      IO.eprintln "  (no input or output, no subtraction, no arrays,"
      IO.eprintln "  and the result in a variable named 'answer')."
      IO.eprintln "turpentine: retry with --bespoke to compile the whole language."
    IO.eprintln "turpentine: nothing was run"
    return 1
  | .ok targetSrc =>
    if verbose then
      IO.eprintln s!"turpentine: compiled to {targetSrc.length} bytes of {target} [{scheme}]"
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
  if args.contains "--help" || args.contains "-h" || args.isEmpty then
    IO.println helpText
    return (if args.isEmpty then 3 else 0)
  match args with
  | "check" :: [file] => checkMain file
  | "check" :: _ =>
    IO.eprintln "usage: lake exe turpentine check <file.turp>"
    return 3
  | "compile" :: rest => compileMain rest
  | "exec" :: rest => execMain rest
  | "run" :: rest => runner.main rest
  | rest => runner.main rest
