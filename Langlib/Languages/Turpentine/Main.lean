import Langlib.Common.Runner
import Langlib.Languages.Turpentine.Semantics
import Langlib.Languages.Turpentine.Compile.Brainfuck
import Langlib.Languages.Turpentine.Compile.Subleq
import Langlib.Languages.Turpentine.Compile.Whitespace
import Langlib.Languages.Turpentine.Compile.Ook
import Langlib.Languages.Turpentine.Compile.Brainloller
import Langlib.Languages.Turpentine.Compile.Fractran
import Langlib.Languages.Brainfuck.Semantics
import Langlib.Languages.Subleq.Semantics
import Langlib.Languages.Whitespace.Semantics
import Langlib.Languages.Ook.Semantics
import Langlib.Languages.Brainloller.Semantics
import Langlib.Languages.Fractran.Semantics
import Langlib.Languages.Piet.Semantics
import Langlib.Languages.Thue.Semantics
import Langlib.Languages.Unlambda.Semantics
import Langlib.Languages.Turpentine.Compile.Derived

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

/-- What a compiler produced: the target's source text, a run of exactly
that text on the target's own reference interpreter, and, when the file is
not enough to say how to run it, the command that is.

`run` closes over the emitted text on purpose, so `exec` exercises the
renderer and the target's parser rather than only the code generator. It
also lets a target whose file does not carry the whole artifact still be
executed: FRACTRAN's compiled program is a fraction list *and* a starting
value, and only the fractions go in the file. -/
structure Artifact where
  /-- The target program, as the target's own source text. -/
  text : String
  /-- Run that text on the target's interpreter. -/
  run : Input → Nat → Except String RunResult
  /-- How to run the emitted file by hand, when `lake exe <target> <file>`
  is not the whole story. `<file>` in it is replaced by the path written. -/
  runNote : Option String := none

/-- A compiler into some target: Turpentine source text to an `Artifact`,
or an error naming what it refused. -/
abbrev Compiler := String → Except String Artifact

/-- The common case: emit source text, and run it with the target's
parse-and-run. -/
def compilerOfSource (emit : String → Except String String)
    (run : String → Input → Nat → Except String RunResult) : Compiler :=
  fun src => do
    let text ← emit src
    return { text, run := run text }

/-- The certified route for a target: parse, type-check, compile through
the shared URM pass and the target's completeness witness, then render. One
line per target, because `derived` did the work. `compile` is the
`TurpentineCompiler.compileSource` of that target's derived compiler. -/
def compilerOfCertified {α : Type} (compile : String → Except String α)
    (render : α → String)
    (run : String → Input → Nat → Except String RunResult) : Compiler :=
  compilerOfSource (fun src => do return render (← compile src)) run

/-- FRACTRAN's certified backend, which needs its own entry because a `.ft`
file holds only the fractions: the starting value is a command-line flag or
the first line of stdin. The emitted file records it in a comment, the note
repeats the command, and `exec` supplies it the way the note says to. -/
def fractranCertified : Compiler := fun src => do
  let cp ← Langlib.Turpentine.Compile.derivedFractran.compileSource src
  let text :=
    s!"# Compiled by turpentine, certified route: derived from FRACTRAN's\n\
       # Turing-completeness proof. FRACTRAN has no I/O, so the answer is the\n\
       # exponent of 2 in the final value.\n\
       # Starting value: {cp.start}\n\
       # Run with: lake exe fractran --out final --n {cp.start} <this file>\n"
      ++ Langlib.Fractran.Prog.render cp.code ++ "\n"
  return { text
         , runNote := some s!"lake exe fractran --out final --n {cp.start} <file>"
         , run := Langlib.Fractran.run { out := .final, n? := some cp.start } text }

/-- FRACTRAN's hand-written backend. Like the certified one it needs its
own entry, because a `.ft` file holds only the fractions. Unlike it, the
answer needs no decoding: the compiler arranges for the run to end on
`2 ^ answer` and for no earlier value to be a power of two, so
`--out pow2` prints the answer as a decimal number and nothing else. -/
def fractranBespoke : Compiler := fun src => do
  let (prog, start) ← Compile.Fractran.compileProgram src
  let text :=
    s!"# Compiled by turpentine, bespoke route: Turpentine to a Minsky\n\
       # machine to fractions. FRACTRAN has no I/O; the run ends on two to\n\
       # the power of the answer, which --out pow2 prints on its own.\n\
       # Starting value: {start}\n\
       # Run with: lake exe fractran --out pow2 --n {start} <this file>\n"
      ++ Langlib.Fractran.Prog.render prog ++ "\n"
  return { text
         , runNote := some s!"lake exe fractran --out pow2 --n {start} <file>"
         , run := Langlib.Fractran.run { out := .pow2, n? := some start } text }

/-- A compilation target: the name accepted after `--to` and `--via`, and
the compilers that reach it. Adding a target is one entry here.

Neither compiler is guaranteed to exist. `bespoke` is hand-written, accepts
the whole language and is unverified; FRACTRAN and Thue have none, because
neither is a language anybody would hand-write a backend for. `certified`
is derived from the target's Turing-completeness proof and accepts only the
I/O-free fragment; a language whose completeness is still open has none. -/
structure Backend where
  /-- Name accepted after `--to` and `--via`. -/
  name : String
  /-- The hand-written backend, if there is one. -/
  bespoke : Option Compiler := none
  /-- The compiler derived from the completeness proof, if there is one.
  See `docs/certified-compilation.md`. -/
  certified : Option Compiler := none

def backends : List Backend :=
  [ { name := "brainfuck"
      -- The backend emits programs that expect `--eof zero`: its
      -- `readByte` reports -1 for a zero byte or end of input alike.
    , bespoke := some (compilerOfSource Compile.Brainfuck.compileSource
        (Langlib.Brainfuck.run { eof := .zero }))
    , certified := some (compilerOfCertified
        Langlib.Turpentine.Compile.derivedBrainfuck.compileSource
        Langlib.Brainfuck.Prog.render
        (Langlib.Brainfuck.run { eof := .zero })) }
  , { name := "whitespace"
    , bespoke := some (compilerOfSource Compile.Whitespace.compileSource
        Langlib.Whitespace.run)
    , certified := some (compilerOfCertified
        Langlib.Turpentine.Compile.derivedWhitespace.compileSource
        Langlib.Whitespace.Prog.render
        Langlib.Whitespace.run) }
  , { name := "subleq"
    , bespoke := some (compilerOfSource Compile.Subleq.compileSource
        Langlib.Subleq.run)
    , certified := some (compilerOfCertified
        Langlib.Turpentine.Compile.derivedSubleq.compileSource
        Langlib.Subleq.Prog.render
        Langlib.Subleq.run) }
  , { name := "ook"
      -- Ook! is brainfuck under a different concrete syntax, so both
      -- compilers are brainfuck's with a different renderer, and the
      -- emitted code wants the same `--eof zero` convention.
    , bespoke := some (compilerOfSource Compile.Ook.compileSource
        (Langlib.Ook.run { eof := .zero }))
    , certified := some (compilerOfCertified
        Langlib.Turpentine.Compile.derivedOok.compileSource
        Langlib.Ook.render
        (Langlib.Ook.run { eof := .zero })) }
  , { name := "brainloller"
      -- The target text is an ASCII PPM image, which is what
      -- `lake exe brainloller` reads.
    , bespoke := some (compilerOfSource Compile.Brainloller.compileSource
        (Langlib.Brainloller.run { eof := .zero }))
    , certified := some (compilerOfCertified
        Langlib.Turpentine.Compile.derivedBrainloller.compileSource
        (fun prog =>
          (Langlib.Brainloller.encode (Langlib.Brainfuck.Prog.render prog)
            Compile.Brainloller.defaultWidth).toPpm3)
        (Langlib.Brainloller.run { eof := .zero })) }
  , { name := "piet"
      -- The target text is an ASCII PPM image, as `lake exe piet` reads.
      -- `Grid.toImage` paints it and `colorOfRgb_toRgb` says the parser
      -- reads back the colours the compiler chose.
    , certified := some (compilerOfCertified
        Langlib.Turpentine.Compile.derivedPiet.compileSource
        (fun grid => grid.toImage.toPpm3)
        (Langlib.Piet.run {})) }
  , { name := "fractran"
    , bespoke := some fractranBespoke
    , certified := some fractranCertified }
  , { name := "thue"
      -- `finalState` is what makes the answer visible: Thue's only output
      -- primitive is `~`, and the compiled program does not use it, so the
      -- halted state string is the result.
    , certified := some (compilerOfCertified
        Langlib.Turpentine.Compile.derivedThue.compileSource
        Langlib.Thue.Prog.render
        (Langlib.Thue.run { finalState := true })) }
  , { name := "unlambda"
      -- The emitted term uses only `s`, `k`, `i`, `.x` and application, all
      -- of them ASCII, so `Term.render` round-trips through the parser. The
      -- answer is printed in unary, one `*` per unit.
    , certified := some (compilerOfCertified
        Langlib.Turpentine.Compile.derivedUnlambda.compileSource
        Langlib.Unlambda.Term.render
        Langlib.Unlambda.run) } ]

/-- Which compilers a target has, for the help text and for the message a
refused `--bespoke` or `--tc` prints. -/
def Backend.schemes (b : Backend) : String :=
  match b.bespoke, b.certified with
  | some _, some _ => "bespoke and certified"
  | some _, none => "bespoke only"
  | none, some _ => "certified only (--tc)"
  | none, none => "none"

def backendNames : String :=
  String.intercalate "|" (backends.map (·.name))

/-- One line per target, naming the compilers it has, for the help text.
Padded so the second column lines up. -/
def backendTable : List String :=
  let width := backends.foldl (fun w b => max w b.name.length) 0
  backends.map fun b =>
    s!"  {b.name}{String.ofList (List.replicate (width + 2 - b.name.length) ' ')}{b.schemes}"

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
    , s!"  compile --to <target> [-o out] <file.turp>"
    , "                                     emit the target program"
    , s!"  exec --via <target> <file.turp>"
    , "                                     compile, then run on that language's interpreter"
    , "targets, and the compilers each has:" ]
    ++ backendTable ++
    [ "compiler choice, for compile and exec:"
    , "  --bespoke    hand-written backend: whole language, compact output, unverified."
    , "               This is the default when neither flag is given."
    , "  --tc         derived from the language's Turing-completeness proof: correct by"
    , "               construction, far larger output, and accepts only the I/O-free"
    , "               fragment (see docs/certified-compilation.md)."
    , "  Either way the chosen scheme is named in the message the command prints." ]

/-- The full help. Turpentine has four subcommands and two compilers, so
the generic `Runner` usage is not enough; this replaces it. -/
def helpText : String :=
  String.intercalate "\n" (
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
    , "  --to <lang>    for compile"
    , "  --via <lang>   for exec"
    , "  Targets, and the compilers each of them has. A target with no"
    , "  hand-written backend is reachable only with --tc, and one whose"
    , "  completeness is still open only with --bespoke:" ]
    ++ backendTable ++
    [ ""
    , "choosing a compiler (compile and exec):"
    , "  --bespoke  hand-written for that target. Accepts the whole language,"
    , "             emits compact code, and is not verified. This is the"
    , "             default when neither flag is given."
    , "  --tc       derived from the target's Turing-completeness proof, by"
    , "             composing it with the shared Turpentine-to-URM pass."
    , "             Correct by construction. Accepts only the I/O-free"
    , "             fragment: no input or output statements, no subtraction,"
    , "             and no && or || whose right operand indexes an array."
    , "             Arrays, division and modulo are supported. The result"
    , "             must be left in a variable named `answer`."
    , "             Not every target has one; the list above says which"
    , "             do. See docs/certified-compilation.md."
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
    , "  3  parse error, or a problem with the command line" ])

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
  let (compiler, scheme) ← if useCertified then
      match backend.certified with
      | some f => pure (f, "certified, derived from the Turing-completeness proof")
      | none =>
        IO.eprintln s!"turpentine compile: no certified compiler for '{target}' yet"
        IO.eprintln s!"turpentine: {target} has {backend.schemes}"
        return 3
    else
      match backend.bespoke with
      | some f => pure (f, "bespoke, hand-written and unverified")
      | none =>
        IO.eprintln s!"turpentine compile: no hand-written backend for '{target}'"
        IO.eprintln s!"turpentine: it has {backend.schemes}; retry with --tc"
        return 3
  match compiler src with
  | .error e =>
    IO.eprintln s!"turpentine compile: {e}"
    if useCertified then
      IO.eprintln "turpentine: the certified compiler accepts only the I/O-free fragment"
      IO.eprintln "  (no input or output, no subtraction, and the result in a"
      IO.eprintln "  variable named 'answer'); arrays, division and modulo are"
      IO.eprintln "  supported, and the message above names what was rejected."
      if backend.bespoke.isSome then
        IO.eprintln s!"turpentine: retry with --bespoke to compile the whole language."
    match out? with
    | some path => IO.eprintln s!"turpentine: nothing written to {path}"
    | none => IO.eprintln "turpentine: nothing emitted"
    return 1
  | .ok art =>
    match out? with
    | some path =>
      IO.FS.writeFile path art.text
      IO.eprintln s!"turpentine: wrote {art.text.length} bytes to {path} [{scheme}]"
      if let some note := art.runNote then
        IO.eprintln s!"turpentine: run it with: {note.replace "<file>" path}"
    | none =>
      IO.eprintln s!"turpentine: emitting {art.text.length} bytes [{scheme}]"
      if let some note := art.runNote then
        IO.eprintln s!"turpentine: run it with: {note}"
      IO.print art.text
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
  let (compiler, scheme) ← if useCertified then
      match backend.certified with
      | some f => pure (f, "certified, derived from the Turing-completeness proof")
      | none =>
        IO.eprintln s!"turpentine exec: no certified compiler for '{target}' yet"
        IO.eprintln s!"turpentine: {target} has {backend.schemes}"
        return 3
    else
      match backend.bespoke with
      | some f => pure (f, "bespoke, hand-written and unverified")
      | none =>
        IO.eprintln s!"turpentine exec: no hand-written backend for '{target}'"
        IO.eprintln s!"turpentine: it has {backend.schemes}; retry with --tc"
        return 3
  match compiler src with
  | .error e =>
    IO.eprintln s!"turpentine exec: {e}"
    if useCertified then
      IO.eprintln "turpentine: the certified compiler accepts only the I/O-free fragment"
      IO.eprintln "  (no input or output, no subtraction, and the result in a"
      IO.eprintln "  variable named 'answer'); arrays, division and modulo are"
      IO.eprintln "  supported, and the message above names what was rejected."
      if backend.bespoke.isSome then
        IO.eprintln "turpentine: retry with --bespoke to compile the whole language."
    IO.eprintln "turpentine: nothing was run"
    return 1
  | .ok art =>
    if verbose then
      IO.eprintln s!"turpentine: compiled to {art.text.length} bytes of {target} [{scheme}]"
    let stdinStream ← IO.getStdin
    let stdinBytes ← if ← stdinStream.isTty then pure ByteArray.empty
                     else stdinStream.readBinToEnd
    match art.run (Input.ofByteArray stdinBytes) fuel with
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
