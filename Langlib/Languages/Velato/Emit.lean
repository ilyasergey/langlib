import Langlib.Languages.Velato.Parser

/-!
# Velato: writing notes, not just reading them

`Parser.lean` goes from notes to a program. This module goes the other way,
and it is what makes Velato practical to *write*: the encoder that the
example generator, the Turpentine backend
(`Langlib/Languages/Turpentine/Compile/Velato.lean`) and the completeness
witness (`Langlib/Computability/Velato.lean`) all emit through.

## The freedom a Velato composer actually has

Turning a program into notes is not a function, it is a search, because the
language leaves a great deal underdetermined:

* **Octave is free** everywhere except a variable's name. A command or a
  digit fixes a pitch *class*; which of the ten octaves it is sounded in is
  the composer's business. This is by far the largest degree of freedom, and
  it is what lets a program have a melodic contour at all.
* **Quality is free inside expressions.** A third may be minor or major, a
  sixth either sixth, a fifth diminished or perfect. Commands are exact, and
  so is the perfect fifth that ends a number, but everything else in an
  expression comes in two flavours. velato.net says why: forcing the exact
  quality would force progressions like C E C E♭ on a composer writing in C.
* **The unison is free to repeat.** A note at the root is a no-op, so a
  composer may sprinkle them anywhere between statements to fill out a bar.
* **The command root can move**, and variables may be given any pitch.

`choose` below spends that freedom on making the result sound like music. It
scores every legal pitch and takes the best: small intervals beat large
ones, notes inside a chosen scale beat notes outside it, and a note near the
middle of the register beats one at the edge. When a `follow` melody is
given, proximity to that melody's next note dominates everything else, which
is what the disguised programs in `Langlib/Examples/Velato/` are built with.

Velato programs are chromatic whatever you do — `Let` is a minor third and
`Blocks` is a major third, so any program that assigns inside a loop sounds
both at once — so the goal here is not diatonic purity. It is smooth
voice leading, which is what turns a chromatic pitch set into the "dense,
jazz-like harmonies" velato.net describes rather than into noise.

## Round-tripping

`emit` is checked against `parseNotes` in `Langlib/Tests/Velato.lean`: for
every program the tests build, parsing the emitted notes gives the program
back. That is the property that makes this module trustworthy as a compiler
backend, and it is the one that would break first if the tables here and the
tables in `Parser.lean` ever drifted apart.
-/

namespace Langlib.Velato

/-! ## What the encoder needs next -/

/-- One demand on the next note: either its interval from the command root
must be one of `choices` — with the octave free — or it must be exactly this
pitch, which is what naming a variable requires. -/
inductive Need where
  /-- Any note whose interval from the root is in this list. Never empty. -/
  | interval (choices : List Interval)
  /-- This exact MIDI note: a variable's name. -/
  | exact (p : Pitch)
deriving Repr, Inhabited

/-- The demand for a note of a given degree, taking every quality the degree
allows. Used for the expression-side intervals, which are read coarsely. -/
def Need.degree (d : Degree) : Need :=
  .interval <| match d with
    | .unison => [unison]
    | .second => [majorSecond, minorSecond]
    | .third => [minorThird, majorThird]
    | .fourth => [perfectFourth]
    | .fifth => [perfectFifth, diminishedFifth]
    | .sixth => [minorSixth, majorSixth]
    | .seventh => [minorSeventh, majorSeventh]

/-- The demand for one exact interval: what a command spells. -/
def Need.exactly (i : Interval) : Need := .interval [i]

/-! ## Taste -/

/-- How the encoder spends the freedom the language leaves it. -/
structure Voice where
  /-- The lowest and highest note it will write. The defaults are a
  comfortable two and a half octaves around middle C. -/
  lo : Pitch := 48
  hi : Pitch := 84
  /-- Where the line is pulled back towards when nothing else decides. -/
  centre : Pitch := 64
  /-- Pitch classes to prefer, `[]` for no preference. A scale here does not
  constrain the program — Velato's command intervals are what they are — it
  only breaks ties. -/
  scale : List Nat := []
  /-- What leaving the scale costs, in the same units as a semitone of
  leap. -/
  scaleCost : Nat := 3
  /-- What each semitone away from `centre` costs, per twelve semitones. -/
  centreCost : Nat := 2
  /-- A melody to shadow. When it has a note for this position, being far
  from it costs `followCost` per semitone, which swamps everything else. -/
  follow : Array Pitch := #[]
  followCost : Nat := 40
deriving Inhabited

/-- Absolute difference, as a `Nat`. -/
private def dist (a b : Nat) : Nat := if a ≥ b then a - b else b - a

/-- What it would cost to write `p` as the `idx`-th note, coming from
`prev`. -/
private def cost (v : Voice) (idx : Nat) (prev : Pitch) (p : Pitch) : Nat :=
  let leap := dist prev p
  let centrePull := dist p v.centre * v.centreCost / 12
  let offScale := if v.scale.isEmpty || v.scale.contains (p % 12) then 0 else v.scaleCost
  let followPull :=
    match v.follow[idx]? with
    | some t => dist t p * v.followCost
    | none => 0
  leap + centrePull + offScale + followPull

/-- Pick the note to write. Every pitch in the register that satisfies the
demand is scored, and the cheapest wins; ties go to the lower note, which
keeps the choice deterministic and therefore keeps generated examples
reproducible. -/
def choose (v : Voice) (idx : Nat) (root prev : Pitch) : Need → Option Pitch
  | .exact p => some p
  | .interval choices => Id.run do
    let mut best : Option (Nat × Pitch) := none
    for p in [v.lo:v.hi+1] do
      if choices.contains (intervalFrom root p) then
        let c := cost v idx prev p
        match best with
        | some (bc, _) => if c < bc then best := some (c, p)
        | none => best := some (c, p)
    return best.map Prod.snd

/-! ## Programs to demands

Everything below is the mirror image of `Parser.lean`, one table at a time.
Where the parser reads an interval and dispatches, this writes the interval
that would make it dispatch that way. -/

/-- The digits of a non-negative integer, most significant first. -/
private def decDigits (n : Nat) : List Nat :=
  if n < 10 then [n]
  else
    let rec go : Nat → Nat → List Nat → List Nat
      | 0, k, acc => k :: acc
      | fuel + 1, k, acc => if k < 10 then k :: acc else go fuel (k / 10) (k % 10 :: acc)
    go (n + 1) n []

/-- A number: one note per digit, then the perfect fifth that ends it. The
terminator is exact — the parser tests for a perfect fifth and not for the
degree — so a diminished fifth would be read as the digit 5. -/
private def numNeeds (n : Nat) : List Need :=
  (decDigits n).map (fun d => Need.exactly (digitInterval d)) ++ [Need.exactly perfectFifth]

/-- The demands for one expression token. -/
private def tokNeeds : Tok → List Need
  | .val (.var p) => [Need.degree .third, Need.degree .second, .exact p]
  | .val (.intLit n) =>
    if n < 0 then [Need.degree .third, Need.degree .third] ++ numNeeds (-n).toNat
    else [Need.degree .third, Need.degree .fifth] ++ numNeeds n.toNat
  | .val (.charLit c) =>
    [Need.degree .third, Need.degree .fourth] ++ numNeeds (max c 0).toNat
  | .val (.doubleLit neg w f) =>
    [Need.degree .third, Need.degree (if neg then .seventh else .sixth)]
      ++ w.map (fun d => Need.exactly (digitInterval d)) ++ [Need.exactly perfectFifth]
      ++ f.map (fun d => Need.exactly (digitInterval d)) ++ [Need.exactly perfectFifth]
  | .val e =>
    -- a compound expression is never a single token; `exprNeeds` takes it
    -- apart before we get here, and this arm keeps the function total
    match e with
    | _ => [Need.degree .third, Need.degree .fifth] ++ numNeeds 0
  | .notOp => [Need.degree .second, Need.degree .fifth]
  | .op .eq => [Need.degree .second, Need.degree .second]
  | .op .gt => [Need.degree .second, Need.degree .third]
  | .op .lt => [Need.degree .second, Need.degree .fourth]
  | .op .and => [Need.degree .second, Need.degree .sixth]
  | .op .or => [Need.degree .second, Need.degree .seventh]
  | .op .sub => [Need.degree .fifth, Need.degree .fifth, Need.degree .second]
  | .op .add => [Need.degree .fifth, Need.degree .fifth, Need.degree .third]
  | .op .div => [Need.degree .fifth, Need.degree .fifth, Need.degree .fourth]
  | .op .mul => [Need.degree .fifth, Need.degree .fifth, Need.degree .fifth]
  | .op .mod => [Need.degree .fifth, Need.degree .fifth, Need.degree .sixth]
  | .lpar => [Need.degree .sixth, Need.degree .sixth, Need.degree .sixth]
  | .rpar => [Need.degree .sixth, Need.degree .sixth, Need.degree .second]

/-- Is this expression a single token, needing no brackets anywhere? -/
private def isAtom : Expr → Bool
  | .var _ | .intLit _ | .charLit _ | .doubleLit .. => true
  | _ => false

/-- The tokens of an expression, bracketed exactly where the parser's
precedence climbing would otherwise regroup it. Emitting brackets everywhere
would also be correct and would cost six notes per operator, which is enough
to bury a short program. -/
private def exprToks (minPrec : Nat) : Expr → List Tok
  | .var p => [.val (.var p)]
  | .intLit n => [.val (.intLit n)]
  | .charLit c => [.val (.charLit c)]
  | .doubleLit neg w f => [.val (.doubleLit neg w f)]
  | .un .not e => .notOp :: exprToks 7 e
  | .bin op l r =>
    let inner := exprToks op.prec l ++ [.op op] ++ exprToks (op.prec + 1) r
    if op.prec < minPrec then .lpar :: inner ++ [.rpar] else inner

/-- The demands for an expression in the position of a `Let` right-hand side
or a `Print` argument, where the parser reads exactly one token unless
brackets open. A compound expression therefore has to be bracketed, which is
not an encoder's choice: it is the only way the parser can tell where the
expression stops and the next statement starts. -/
private def valueNeeds (e : Expr) : List Need :=
  let toks := if isAtom e then exprToks 0 e else .lpar :: exprToks 0 e ++ [.rpar]
  toks.flatMap tokNeeds

/-- The demands for a condition, which is read with an implied opening
bracket and so ends at a closing one. -/
private def condNeeds (e : Expr) : List Need :=
  (exprToks 0 e ++ [Tok.rpar]).flatMap tokNeeds

/-- The interval a type is named by. Coarse, except `double`. -/
private def tyNeed : Ty → Need
  | .int => Need.degree .second
  | .char => Need.degree .third
  | .double => Need.degree .fourth

mutual

/-- The demands for one statement, including the leading no-op at the root
that the specification calls "every statement begins with the command root".
The parser does not require it — a unison is simply a no-op wherever it
falls — but emitting it makes a generated program look like the ones on
velato.net, and it gives the line one more note to shape. -/
private def stmtNeeds : Stmt → List Need
  | .declare v ty => [Need.exactly unison, Need.exactly minorSixth, .exact v, tyNeed ty]
  | .assign v e => [Need.exactly unison, Need.exactly minorThird, .exact v] ++ valueNeeds e
  | .print e =>
    [Need.exactly unison, Need.exactly majorSixth, Need.exactly perfectFifth] ++ valueNeeds e
  | .input v =>
    [Need.exactly unison, Need.exactly majorSixth, Need.exactly perfectFourth, .exact v]
  | .while c body =>
    [Need.exactly unison, Need.exactly majorThird, Need.exactly majorThird]
      ++ condNeeds c ++ blockNeeds body
      ++ [Need.exactly unison, Need.exactly majorThird, Need.exactly perfectFourth]
  | .ite c thn els =>
    [Need.exactly unison, Need.exactly majorThird, Need.exactly perfectFifth]
      ++ condNeeds c ++ blockNeeds thn
      ++ (if els.isEmpty then []
          else [Need.exactly unison, Need.exactly majorThird, Need.exactly majorSixth]
                 ++ blockNeeds els)
      ++ [Need.exactly unison, Need.exactly majorThird, Need.exactly majorSeventh]

private def blockNeeds : List Stmt → List Need
  | [] => []
  | s :: rest => stmtNeeds s ++ blockNeeds rest

end

/-- Every note a program needs, in order, as demands. -/
def progNeeds (p : Prog) : List Need := blockNeeds p

/-! ## Placement -/

/-- Turn a program into notes.

`root` is the command root, which is also the program's first note: the
specification says the first note of the song establishes it, so it is
written out before anything else and every interval afterwards is measured
from it. This encoder never moves the root — there is no need, since octave
is already free — so a program it writes is in one key throughout, and can
be transposed by transposing `root` and re-emitting.

Fails only if a demand cannot be met inside the voice's register, which
happens when `lo` and `hi` are less than an octave apart. -/
def emitFrom (p : Prog) (root : Pitch) (v : Voice := {}) : Except String (Array Pitch) := do
  let mut out : Array Pitch := #[root]
  let mut prev := root
  for need in progNeeds p do
    match choose v out.size root prev need with
    | some n => out := out.push n; prev := n
    | none =>
      throw s!"no note between {(v.lo : Pitch).name} and {(v.hi : Pitch).name} \
        can spell this, at note #{out.size + 1}"
  return out

/-! ## Following a melody, by changing key

`emitFrom` above has only octave and quality to spend, and that is not
enough to make a program follow a given tune: within a statement the pitch
*classes* are forced, so a melody note that wants an F when the encoding
wants a G cannot be had at any octave.

The freedom that does help is the one velato.net says root changes are for —
"to allow versatility in Velato composition ... this allows the programmer
to choose a starting pitch that better fits the flow of the song". Moving
the root transposes every interval after it, so the whole forced pitch-class
pattern of the next statement slides to wherever the tune needs it.

Root changes are legal only where a *statement* may begin, because a major
2nd anywhere else is read as a comparison operator. So the encoder below
chops a program into chunks at exactly the statement boundaries, and at each
boundary tries all twelve roots, keeping the one whose forced pattern lies
closest to the melody. Changing key costs two notes — the major 2nd, and the
note that becomes the new root — and both of those are placed against the
melody too. When the root changes, the statement's leading no-op is dropped:
the new root note is already read as one, which is the same economy the
reference compiler's own examples use.

This does not, and cannot, make an arbitrary program come out as an
arbitrary tune. What it does is get a good deal closer than octave choice
alone, and `docs/velato/spec.md` reports how close, example by example. -/

/-! Where a root change is legal: the start of a statement, and the closing
command of a block, which is also a statement position. Each chunk below is
a run of demands with no legal root change inside it. -/

mutual

/-- The chunks of one statement. -/
private def stmtChunks : Stmt → List (List Need)
  | .declare v ty => [stmtNeeds (.declare v ty)]
  | .assign v e => [stmtNeeds (.assign v e)]
  | .print e => [stmtNeeds (.print e)]
  | .input v => [stmtNeeds (.input v)]
  | .while c body =>
    ([Need.exactly unison, Need.exactly majorThird, Need.exactly majorThird] ++ condNeeds c)
      :: blockChunks body
      ++ [[Need.exactly unison, Need.exactly majorThird, Need.exactly perfectFourth]]
  | .ite c thn els =>
    ([Need.exactly unison, Need.exactly majorThird, Need.exactly perfectFifth] ++ condNeeds c)
      :: blockChunks thn
      ++ (if els.isEmpty then []
          else [Need.exactly unison, Need.exactly majorThird, Need.exactly majorSixth]
                 :: blockChunks els)
      ++ [[Need.exactly unison, Need.exactly majorThird, Need.exactly majorSeventh]]

/-- The chunks of a block. -/
private def blockChunks : List Stmt → List (List Need)
  | [] => []
  | s :: rest => stmtChunks s ++ blockChunks rest

end

/-- Lay out a run of demands from a given root, returning the notes and what
they cost. Used both to commit to a layout and to price a hypothetical
one. -/
private def layout (v : Voice) (root : Pitch) (startIdx : Nat) (prev : Pitch)
    (needs : List Need) : Option (Array Pitch × Nat) := Id.run do
  let mut out : Array Pitch := #[]
  let mut prev := prev
  let mut total := 0
  for need in needs do
    match choose v (startIdx + out.size) root prev need with
    | none => return none
    | some n =>
      total := total + cost v (startIdx + out.size) prev n
      out := out.push n
      prev := n
  return some (out, total)

/-- Encode a program so that its notes shadow `v.follow` as closely as the
language allows, changing the command root between statements wherever a
change pays for itself. -/
def emitFollowing (p : Prog) (root0 : Pitch) (v : Voice := {}) :
    Except String (Array Pitch) := do
  let mut out : Array Pitch := #[root0]
  let mut root := root0
  let mut prev := root0
  for chunk in blockChunks p do
    -- the same chunk without its leading no-op, for the branches that
    -- change key: the new root note is already read as one
    let bare := match chunk with
      | Need.interval [0] :: rest => rest
      | c => c
    let mut best : Option (Nat × Array Pitch × Pitch) := none
    for cand in [0:12] do
      let opt : Option (Array Pitch × Nat × Pitch) :=
        if intervalFrom root (root % 12 + cand) == 0 && cand == root % 12 then
          -- staying put: no change notes, and the chunk keeps its no-op
          (layout v root out.size prev chunk).map fun (ns, c) => (ns, c, root)
        else
          -- change key: a major 2nd from the old root, then the new root
          match choose v out.size root prev (Need.exactly majorSecond) with
          | none => none
          | some m2 =>
            -- the new root can be sounded in any octave, so pick the one
            -- that sits best in the line
            match choose v (out.size + 1) (cand % 12) m2 (Need.exactly unison) with
            | none => none
            | some newRoot =>
              (layout v newRoot (out.size + 2) newRoot bare).map fun (ns, c) =>
                (#[m2, newRoot] ++ ns,
                 c + cost v out.size prev m2 + cost v (out.size + 1) m2 newRoot + 2,
                 newRoot)
      match opt with
      | none => pure ()
      | some (ns, c, r) =>
        match best with
        | some (bc, _, _) => if c < bc then best := some (c, ns, r)
        | none => best := some (c, ns, r)
    match best with
    | none => throw s!"no key lets this statement be written in the given register"
    | some (_, ns, r) =>
      out := out ++ ns
      root := r
      prev := ns.back!
  return out

/-- How many of a program's notes coincide with the melody it was told to
shadow. Reported in `docs/velato/spec.md` for each disguised example, since
the honest answer is never "all of them". -/
def followMatch (notes melody : Array Pitch) : Nat × Nat := Id.run do
  let mut hit := 0
  for (n, i) in notes.toList.zipIdx do
    if melody[i]? == some n then hit := hit + 1
  return (hit, notes.size)

/-- The same, rendered in langlib's text form: what the example generator
writes into a `.vel` file. `perLine` note names to a line. -/
def renderNotes (notes : Array Pitch) (perLine : Nat := 8) : String := Id.run do
  let mut out := ""
  let mut line : Array String := #[]
  for (n, i) in notes.toList.zipIdx do
    line := line.push n.name
    if (i + 1) % perLine == 0 then
      out := out ++ String.intercalate " " line.toList ++ "\n"
      line := #[]
  if !line.isEmpty then out := out ++ String.intercalate " " line.toList ++ "\n"
  return out

end Langlib.Velato
