/-!
# Unlambda: abstract syntax

Unlambda (David Madore, 1999) has one syntactic construct, application,
written prefix with a backquote, and a handful of nullary builtins. There
are no variables, no binders, and no data: an Unlambda program is a binary
tree whose leaves are builtins.

Two of the builtins carry a byte: `.x` prints `x`, and `?x` asks whether the
last character read was `x`. `r` is not a separate constructor, it is `.x`
with `x` the newline byte, exactly as Madore specifies.

See `docs/unlambda/spec.md` for the language specification and the exact
semantic choices.
-/

namespace Langlib.Unlambda

/-- An Unlambda expression. Leaves are builtins; `app` is the backquote. -/
inductive Term where
  /-- `k` : the constant-function generator. -/
  | k
  /-- `s` : substituted application. -/
  | s
  /-- `i` : identity. -/
  | i
  /-- `v` : the black hole; swallows any argument and returns itself. -/
  | v
  /-- `d` : delay. The one special form: `` `dX `` does not evaluate `X`. -/
  | d
  /-- `c` : call with current continuation. -/
  | c
  /-- `e` : exit, ending the program at once (Unlambda 2). -/
  | e
  /-- `.x` : print the byte `x` and return the argument. `r` is `.x` with
  `x` the newline byte. -/
  | dot (ch : UInt8)
  /-- `@` : read one byte into the current character (Unlambda 2). -/
  | at
  /-- `?x` : is the current character `x`? (Unlambda 2). -/
  | ques (ch : UInt8)
  /-- `|` : hand the current character back as a printing function
  (Unlambda 2). -/
  | pipe
  /-- `` `FG `` : the application of `F` to `G`. -/
  | app (fn arg : Term)
deriving Repr, BEq, Inhabited

/-- An Unlambda program is a single expression. -/
abbrev Prog := Term

namespace Term

/-- The newline byte, which is what `r` prints. -/
def newlineByte : UInt8 := 10

/-- `r`, the customary spelling of `.` followed by a newline. -/
def r : Term := .dot newlineByte

/-- The bytes of a builtin leaf, in concrete syntax. A `.x` printing a
newline comes back as `r`, which parses to the same term and keeps the text
on one line. -/
private def leafBytes : Term → List UInt8
  | .k => [107]
  | .s => [115]
  | .i => [105]
  | .v => [118]
  | .d => [100]
  | .c => [99]
  | .e => [101]
  | .at => [64]
  | .pipe => [124]
  | .dot ch => if ch == newlineByte then [114] else [46, ch]
  | .ques ch => [63, ch]
  | .app _ _ => []

/-- Render a term back to concrete syntax, as bytes.

Bytes rather than a `String` because `.x` and `?x` carry a *byte*, not a
character: `.é` in a source file is `.` followed by the first byte of the
UTF-8 encoding, and only a byte-level rendering parses back to the term it
came from. `parse (render t) = .ok t` for every `t`. -/
def renderBytes (t : Term) : ByteArray :=
  go t .empty
where
  go : Term → ByteArray → ByteArray
    | .app f a, acc => go a (go f (acc.push 96))
    | leaf, acc => leaf.leafBytes.foldl ByteArray.push acc

/-- Render a term back to concrete syntax. Terms whose `.x` and `?x`
payloads are all ASCII round-trip through this; for the general case use
`renderBytes`, which is what `parse` actually reads. -/
def render (t : Term) : String :=
  String.ofList ((renderBytes t).toList.map fun b => Char.ofNat b.toNat)

/-- The number of leaves in a term, i.e. the number of builtins in it. -/
def size : Term → Nat
  | .app f a => size f + size a
  | _ => 1

end Term

end Langlib.Unlambda
