import Langlib.Languages.Velato.Syntax

/-!
# Velato: from notes to abstract syntax

The Velato "lexer" is the MIDI file: a program is the sequence of pitches
its note-on events sound, in file order. This module is everything that
happens after that — grouping those pitches into commands and expressions
according to the interval tables on velato.net.

## The shape of the grammar

Parsing is one left-to-right pass with a single piece of mutable context,
the **command root**. Every interval is measured from it, and the program's
first note establishes it. Two commands are invisible in the output:

* a note at the unison (or an octave from the root) is a **no-op**. This is
  what the specification means when it says every statement begins with the
  command root: the leading root note parses as a no-op and the interval
  after it names the command. Treating it as a command in its own right,
  rather than as a required prefix, is the reference compiler's reading, and
  it is the one that explains why a composer may sprinkle extra root notes
  through a piece to fill out a bar.
* a **major 2nd** changes the root: the very next note becomes the new one.
  That note is then re-read as the start of the next command, where it sits
  at the unison and is a no-op — so a root change costs two notes and
  produces nothing.

Everything else is in the tables below, which are transcribed from
velato.net's command and expression lists and cross-checked against the 2009
reference compiler. `docs/velato/spec.md` records where the two disagree and
which one we follow; the one substantive case is `If`, whose branch in the
reference parser reads no condition and cannot terminate. We follow the
specification's table, under which `If` takes its condition exactly as
`While` does.

## Expression blocks, and the rule that surprises people

An expression block is not "read expressions until the statement ends".
The reference reads **exactly one** expression token — and then keeps going
only while parentheses are open. So `Let x 5` is one token and complete,
while a compound right-hand side has to be written parenthesised. `While`
and `If` conditions get an *implied* opening parenthesis, so their condition
runs to the matching close. This is faithfully reproduced here, because it
is load-bearing: without it there would be no way to tell where an
assignment's right-hand side stops and the next statement starts.

## Concrete syntax

`parse` accepts langlib's text form: whitespace-separated scientific pitch
names, `C4`, `D#5`, `Bb3`, one per note, with `#` or `s` for sharps and `b`
or `&` for flats, and `%`, `;` or `//` starting a comment. The binary form
is a MIDI file, read by `Langlib/Languages/Velato/Midi.lean`. Both funnel
into `parseNotes`, so the two forms cannot drift apart.
-/

namespace Langlib.Velato

/-! ## Note text -/

/-- Parse a scientific pitch name into a MIDI note number.

Accepts `C4`, `C#4`, `Cs4`, `Db4`, `D&4` (the GUIDO flat velato.net's
tutorial uses), and negative octaves as in `C-1`. Double accidentals are not
accepted: no MIDI note needs one, and rejecting them catches typos. -/
def parsePitch? (s : String) : Option Pitch := do
  let cs := s.toList
  let (letter, cs) ← match cs with
    | c :: rest =>
      let step ← match c.toUpper with
        | 'C' => some 0 | 'D' => some 2 | 'E' => some 4 | 'F' => some 5
        | 'G' => some 7 | 'A' => some 9 | 'B' => some 11 | _ => none
      some (step, rest)
    | [] => none
  let (accidental, cs) : Int × List Char := match cs with
    | '#' :: rest => (1, rest)
    | 's' :: rest => (1, rest)
    | 'S' :: rest => (1, rest)
    | 'b' :: rest => (-1, rest)
    | '&' :: rest => (-1, rest)
    | rest => (0, rest)
  let (neg, cs) := match cs with
    | '-' :: rest => (true, rest)
    | rest => (false, rest)
  if cs.isEmpty then none else
  if !cs.all Char.isDigit then none else
  let oct : Int := (String.ofList cs).toNat!
  let octave : Int := if neg then -oct else oct
  let n : Int := (octave + 1) * 12 + letter + accidental
  if 0 ≤ n && n ≤ 127 then some n.toNat else none

/-- Strip a comment: everything from `%`, `;` or `//` to end of line. -/
private def stripComment (line : String) : String :=
  let cs := line.toList
  let rec go : List Char → List Char
    | [] => []
    | '%' :: _ => []
    | ';' :: _ => []
    | '/' :: '/' :: _ => []
    | c :: rest => c :: go rest
  String.ofList (go cs)

/-- Tokenise langlib's text form into MIDI note numbers. -/
def parseNoteText (src : String) : Except String (Array Pitch) := do
  let mut out : Array Pitch := #[]
  for line in src.splitOn "\n" do
    for word in (stripComment line).split (fun c => c == ' ' || c == '\t' || c == '\r') do
      if !word.toString.isEmpty then
        match parsePitch? word.toString with
        | some p => out := out.push p
        | none => throw s!"not a note name: '{word.toString}'"
  return out

/-! ## Parser state -/

/-- The parser's whole state: the notes, how far we have read, and the
command root every interval is measured from. -/
structure PState where
  notes : Array Pitch
  pos : Nat
  root : Pitch
  /-- What each note turned out to be, filled in as the parse goes.

  This is the sheet-music annotation, and it lives in the parser rather than
  in a separate pass on purpose: a second scanner that re-derived the roles
  from the same tables would be a second grammar, free to drift from this
  one. Here a note cannot be labelled `print` unless the parser really read
  a print command there. -/
  labels : Array String
deriving Inhabited

namespace PState

/-- How many notes remain. Every parsing step strictly decreases this, which
is what the fuel bounds below are counting. -/
def left (st : PState) : Nat := st.notes.size - st.pos

/-- The note under the cursor. -/
def peek? (st : PState) : Option Pitch := st.notes[st.pos]?

/-- The interval of the note under the cursor, from the command root. -/
def interval? (st : PState) : Option Interval :=
  st.peek?.map (intervalFrom st.root)

/-- Advance one note. -/
def bump (st : PState) : PState := { st with pos := st.pos + 1 }

/-- Record what the note under the cursor is, for the sheet's label row. -/
def mark (st : PState) (s : String) : PState :=
  if st.pos < st.labels.size then { st with labels := st.labels.set! st.pos s } else st

/-- Record and advance, which is what almost every step does. -/
def take (st : PState) (s : String) : PState := (st.mark s).bump

/-- Where we are, for an error message. -/
def where_ (st : PState) : String :=
  match st.peek? with
  | some p => s!"note #{st.pos + 1} ({p.name})"
  | none => s!"end of program (after {st.notes.size} notes)"

end PState

/-- Fail with the position folded in, so every diagnostic says which note. -/
private def perr (st : PState) (msg : String) : Except String α :=
  .error s!"{msg}, at {st.where_}"

/-! ## Numbers

A number is a run of notes, one per decimal digit, ending at a perfect
fifth. Notes at the unison inside the run are skipped rather than being
digits — the root is reserved — which is what lets a composer land on the
tonic in the middle of a numeral. -/

/-- Read a digit run and the perfect fifth that ends it. `fuel` is the
number of notes left, so the recursion is structural on it. -/
private def digitsGo : Nat → List Nat → PState → Except String (List Nat × PState)
  | 0, _, st => perr st "number is not terminated by a perfect 5th"
  | fuel + 1, acc, st =>
    match st.interval? with
    | none => perr st "number is not terminated by a perfect 5th"
    | some i =>
      if i == perfectFifth then .ok (acc.reverse, st.take "end num")
      else
        match i.digit? with
        | none => digitsGo fuel acc (st.take "-")    -- unison: reserved, skipped
        | some d => digitsGo fuel (d :: acc) (st.take s!"{d}")

/-- The decimal value of a digit run. -/
private def digitsValue (ds : List Nat) : Int :=
  ds.foldl (fun (acc : Int) (d : Nat) => acc * 10 + (d : Int)) 0

/-- Read a number: the digits, then the terminating perfect fifth. Rejects
an empty run, as the reference does when its `Int32.TryParse` is handed the
empty string. -/
private def readDigits (st : PState) : Except String (List Nat × PState) := do
  let (ds, st') ← digitsGo (st.left + 1) [] st
  if ds.isEmpty then perr st "number has no digits before its terminating perfect 5th"
  else .ok (ds, st')

/-! ## Expression tokens -/

/-- One token of an expression stream, before precedence is applied. -/
inductive Tok where
  | val (e : Expr)
  | op (o : BinOp)
  | notOp
  | lpar
  | rpar
deriving Repr, Inhabited

/-- Read one expression token.

The dispatch is velato.net's expression table. Expressions read intervals
*coarsely* — a third is either third, a fifth is either a diminished or a
perfect one — so that a composer can stay diatonic; only the perfect fourth
is exact, because six semitones is spoken for as a diminished fifth. -/
private def parseTok (st : PState) : Except String (Tok × PState) := do
  let some i := st.interval? | perr st "expected an expression"
  match i.degree with
  | .unison => perr st "the command root has no meaning inside an expression"
  | .second =>
    -- comparisons and logic
    let st := st.take "cmp"
    let some j := st.interval? | perr st "expected the second note of a comparison"
    match j.degree with
    | .second => .ok (.op .eq, st.take "==")
    | .third => .ok (.op .gt, st.take ">")
    | .fourth => .ok (.op .lt, st.take "<")
    | .fifth => .ok (.notOp, st.take "not")
    | .sixth => .ok (.op .and, st.take "and")
    | .seventh => .ok (.op .or, st.take "or")
    | .unison => perr st "the command root cannot follow a 2nd in an expression"
  | .third =>
    -- values: a variable, or a literal of one of the three types
    let st := st.take "value"
    let some j := st.interval? | perr st "expected the second note of a value"
    match j.degree with
    | .second =>
      let st := st.take "var"
      let some v := st.peek? | perr st "expected a note naming a variable"
      .ok (.val (.var v), st.take s!"[{v.name}]")
    | .third => do
      let (ds, st) ← readDigits (st.take "-int")
      .ok (.val (.intLit (-(digitsValue ds))), st)
    | .fourth => do
      let (ds, st) ← readDigits (st.take "char")
      .ok (.val (.charLit (digitsValue ds)), st)
    | .fifth => do
      let (ds, st) ← readDigits (st.take "int")
      .ok (.val (.intLit (digitsValue ds)), st)
    | .sixth => do
      let (whole, st) ← readDigits (st.take "dbl")
      let (frac, st) ← readDigits st
      .ok (.val (.doubleLit false whole frac), st)
    | .seventh => do
      let (whole, st) ← readDigits (st.take "-dbl")
      let (frac, st) ← readDigits st
      .ok (.val (.doubleLit true whole frac), st)
    | .unison => perr st "the command root cannot follow a 3rd in an expression"
  | .fifth =>
    -- arithmetic: a fifth, a fifth, then the operator
    let st := st.take "math"
    let some j := st.interval? | perr st "expected the second note of an operator"
    if j.degree != .fifth then
      perr st s!"an operator needs a 5th here, found a {intervalName j}"
    else
      let st := st.take "math"
      let some k := st.interval? | perr st "expected the third note of an operator"
      match k.degree with
      | .second => .ok (.op .sub, st.take "minus")
      | .third => .ok (.op .add, st.take "plus")
      | .fourth => .ok (.op .div, st.take "div")
      | .fifth => .ok (.op .mul, st.take "times")
      | .sixth => .ok (.op .mod, st.take "mod")
      | _ => perr st s!"no operator is spelled 5th 5th {intervalName k}"
  | .sixth =>
    -- grouping: a sixth, a sixth, then which bracket
    let st := st.take "group"
    let some j := st.interval? | perr st "expected the second note of a bracket"
    if j.degree != .sixth then
      perr st s!"a bracket needs a 6th here, found a {intervalName j}"
    else
      let st := st.take "group"
      let some k := st.interval? | perr st "expected the third note of a bracket"
      match k.degree with
      | .second => .ok (.rpar, st.take ")")
      | .sixth => .ok (.lpar, st.take "(")
      | _ => perr st s!"no bracket is spelled 6th 6th {intervalName k}"
  | _ =>
    perr st s!"no expression begins with a {intervalName i}"

/-- Read an expression block: one token, then more only while brackets are
open. `depth` is how many are open already — one for a `While` or `If`
condition, which has an implied opening bracket, and zero everywhere else. -/
private def blockGo : Nat → Nat → List Tok → PState → Except String (List Tok × PState)
  | 0, _, _, st => perr st "expression is too long (unbalanced brackets?)"
  | fuel + 1, depth, acc, st => do
    let (t, st') ← parseTok st
    let depth' ← match t with
      | .lpar => .ok (depth + 1)
      | .rpar =>
        if depth == 0 then perr st "a closing bracket with nothing open"
        else .ok (depth - 1)
      | _ => .ok depth
    if depth' == 0 then .ok ((t :: acc).reverse, st')
    else blockGo fuel depth' (t :: acc) st'

/-- The token stream of an expression block. `implied` is set for the
conditions of `While` and `If`, which behave as though an opening bracket
had already been played, so the condition runs to its matching close. -/
private def parseTokens (implied : Bool) (st : PState) :
    Except String (List Tok × PState) :=
  blockGo (st.left + 1) (if implied then 1 else 0) [] st

/-! ## Precedence

The reference compiler emits the tokens as an unparenthesised C# expression
and lets the C# compiler group them, so C#'s precedence *is* Velato's. These
two functions apply it: `climb` is ordinary precedence climbing, left
associative at every level, over the token list. -/

mutual

/-- A primary: a value, a negation, or a bracketed subexpression. -/
private def prim : Nat → List Tok → Except String (Expr × List Tok)
  | 0, _ => .error "expression nests too deeply"
  | fuel + 1, ts =>
    match ts with
    | .val e :: rest => .ok (e, rest)
    | .notOp :: rest => do
      let (e, rest) ← prim fuel rest
      .ok (.un .not e, rest)
    | .lpar :: rest => do
      let (e, rest) ← climb fuel 0 rest
      match rest with
      | .rpar :: rest => .ok (e, rest)
      | _ => .error "a bracket is opened and never closed"
    | .rpar :: _ => .error "a closing bracket where a value was expected"
    | .op o :: _ => .error s!"the operator '{o.symbol}' where a value was expected"
    | [] => .error "an expression ended where a value was expected"

/-- Parse a subexpression whose operators all bind at least as tightly as
`minPrec`. -/
private def climb : Nat → Nat → List Tok → Except String (Expr × List Tok)
  | 0, _, _ => .error "expression nests too deeply"
  | fuel + 1, minPrec, ts => do
    let (lhs, rest) ← prim fuel ts
    climbLoop fuel minPrec lhs rest

/-- Absorb operators to the right of `lhs` while they bind tightly enough.
Right operands are parsed at `prec + 1`, which is what makes every level
left associative, as C#'s are. -/
private def climbLoop : Nat → Nat → Expr → List Tok → Except String (Expr × List Tok)
  | 0, _, l, rest => .ok (l, rest)
  | fuel + 1, minPrec, l, rest =>
    match rest with
    | .op o :: more =>
      if o.prec < minPrec then .ok (l, rest)
      else do
        let (r, rest') ← climb fuel (o.prec + 1) more
        climbLoop fuel minPrec (.bin o l r) rest'
    | _ => .ok (l, rest)

end

/-- Turn an expression block's tokens into a tree, insisting that the whole
block is consumed. `implied` blocks carry the closing bracket of their
implied opening one, so one is put back before parsing. -/
private def toExpr (implied : Bool) (ts : List Tok) : Except String Expr := do
  let ts := if implied then .lpar :: ts else ts
  let (e, rest) ← climb (8 * ts.length + 16) 0 ts
  if rest.isEmpty then .ok e
  else .error "an expression has notes left over after it is complete"

/-- Read an expression block and grouping it into a tree. -/
private def parseExpr (implied : Bool) (st : PState) : Except String (Expr × PState) := do
  let (ts, st) ← parseTokens implied st
  match toExpr implied ts with
  | .ok e => .ok (e, st)
  | .error m => perr st m

/-! ## Commands -/

/-- What ended a block of statements. -/
inductive BlockEnd where
  | eof
  | endWhile
  | endIf
  | else_
deriving Repr, BEq, Inhabited

/-- The type a declaration's third note names. Coarse, like every other
expression-side interval, except the perfect fourth. -/
private def parseTy (st : PState) : Except String Ty :=
  match st.interval? with
  | none => perr st "expected a note naming a type"
  | some i =>
    match i.degree with
    | .second => .ok .int
    | .third => .ok .char
    | .fourth => .ok .double
    | _ => perr st s!"no type is named by a {intervalName i}"

mutual

/-- Parse statements until the block ends, reporting how it ended.

`fuel` bounds the recursion by the number of notes left; every branch either
consumes a note or fails, so the bound is never the reason a valid program
is rejected. -/
private def stmtsGo : Nat → List Stmt → PState → Except String (List Stmt × BlockEnd × PState)
  | 0, acc, st => .ok (acc.reverse, .eof, st)
  | fuel + 1, acc, st =>
    match st.interval? with
    | none => .ok (acc.reverse, .eof, st)
    | some i =>
      if i == unison then
        -- a no-op: the root note that punctuates statements
        stmtsGo fuel acc (st.take "-")
      else if i == majorSecond then
        -- change of command root: the next note becomes the root, and is
        -- then re-read as that statement's leading no-op
        let st := st.take "set root"
        match st.peek? with
        | none => perr st "a root change with no note to change to"
        | some p => stmtsGo fuel acc { st.mark "root" with root := p }
      else if i == minorThird then
        -- Let: a variable, then an expression
        let st := st.take "let"
        match st.peek? with
        | none => perr st "an assignment with no variable to assign to"
        | some v =>
          match parseExpr false (st.take s!"[{v.name}]") with
          | .error e => .error e
          | .ok (rhs, st) => stmtsGo fuel (.assign v rhs :: acc) st
      else if i == minorSixth then
        -- Declare: a variable, then a type
        let stv := st.take "declare"
        match stv.peek? with
        | none => perr stv "a declaration with no variable to declare"
        | some v =>
          let stt := stv.take s!"[{v.name}]"
          match parseTy stt with
          | .error e => .error e
          | .ok ty => stmtsGo fuel (.declare v ty :: acc) (stt.take ty.name)
      else if i == majorSixth then
        -- Special commands: input and print
        let st := st.take "cmd"
        match st.interval? with
        | none => perr st "expected the second note of a special command"
        | some j =>
          if j == perfectFifth then
            match parseExpr false (st.take "print") with
            | .error e => .error e
            | .ok (e, st) => stmtsGo fuel (.print e :: acc) st
          else if j == perfectFourth || j == majorSixth then
            let stv := st.take "input"
            match stv.peek? with
            | none => perr stv "an input command with no variable to read into"
            | some v => stmtsGo fuel (.input v :: acc) (stv.take s!"[{v.name}]")
          else
            perr st s!"no special command is spelled major 6th, {intervalName j}"
      else if i == majorThird then
        -- Blocks
        let st := st.take "block"
        match st.interval? with
        | none => perr st "expected the second note of a block command"
        | some j =>
          if j == majorThird then
            match whileGo fuel (st.take "while") with
            | .error e => .error e
            | .ok (s, st) => stmtsGo fuel (s :: acc) st
          else if j == perfectFifth then
            match iteGo fuel (st.take "if") with
            | .error e => .error e
            | .ok (s, st) => stmtsGo fuel (s :: acc) st
          else if j == perfectFourth then .ok (acc.reverse, .endWhile, st.take "end while")
          else if j == majorSeventh then .ok (acc.reverse, .endIf, st.take "end if")
          else if j == majorSixth then .ok (acc.reverse, .else_, st.take "else")
          else perr st s!"no block command is spelled major 3rd, {intervalName j}"
      else
        perr st s!"no command begins with a {intervalName i}"
  termination_by n => n

/-- `While`: a condition with an implied opening bracket, then a body ending
at `End While`. -/
private def whileGo : Nat → PState → Except String (Stmt × PState)
  | 0, st => perr st "program ends inside a while loop"
  | fuel + 1, st => do
    let (cond, st) ← parseExpr true st
    let (body, fin, st) ← stmtsGo fuel [] st
    match fin with
    | .endWhile => .ok (.while cond body, st)
    | .eof => perr st "a while loop is never closed by an End While"
    | _ => perr st "a while loop is closed by the wrong block command"
  termination_by n => n

/-- `If`: a condition, a then-branch ending at `Else` or `End If`, and — if
it was `Else` — an else-branch ending at `End If`.

velato.net puts `If` in the same block family as `While`, with the same
shape; the 2009 reference parser's `If` branch reads no condition and its
loop condition is a tautology, so it cannot return. We follow the
specification. See `docs/velato/spec.md`. -/
private def iteGo : Nat → PState → Except String (Stmt × PState)
  | 0, st => perr st "program ends inside an if"
  | fuel + 1, st => do
    let (cond, st) ← parseExpr true st
    let (thn, fin, st) ← stmtsGo fuel [] st
    match fin with
    | .endIf => .ok (.ite cond thn [], st)
    | .else_ =>
      let (els, fin2, st) ← stmtsGo fuel [] st
      match fin2 with
      | .endIf => .ok (.ite cond thn els, st)
      | .eof => perr st "an else is never closed by an End If"
      | _ => perr st "an else is closed by the wrong block command"
    | .eof => perr st "an if is never closed by an End If"
    | _ => perr st "an if is closed by the wrong block command"
  termination_by n => n

end

/-! ## Entry points -/

/-- Parse a note sequence, keeping the per-note roles the sheet engraver
prints under the staff. The first note is the initial command root and is
consumed by it, exactly as the specification says. -/
def parseNotesAnnotated (notes : Array Pitch) : Except String (Prog × Array String) := do
  let some root := notes[0]? | .error "a Velato program needs at least one note"
  let st : PState :=
    { notes, pos := 1, root, labels := (Array.replicate notes.size "").set! 0 "root" }
  let (stmts, fin, st) ← stmtsGo (notes.size + 1) [] st
  match fin with
  | .eof => .ok (stmts, st.labels)
  | .endWhile => perr st "an End While with no while loop open"
  | .endIf => perr st "an End If with no if open"
  | .else_ => perr st "an Else with no if open"

/-- Parse a note sequence. -/
def parseNotes (notes : Array Pitch) : Except String Prog :=
  (parseNotesAnnotated notes).map Prod.fst

/-- Parse langlib's text form. -/
def parse (src : String) : Except String Prog := do
  parseNotes (← parseNoteText src)

/-- Parse langlib's text form, keeping the note roles. -/
def parseAnnotated (src : String) : Except String (Array Pitch × Prog × Array String) := do
  let notes ← parseNoteText src
  let (p, labels) ← parseNotesAnnotated notes
  return (notes, p, labels)

end Langlib.Velato
