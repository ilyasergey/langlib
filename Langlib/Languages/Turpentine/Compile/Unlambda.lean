import Langlib.Languages.Turpentine.Syntax
import Langlib.Languages.Turpentine.Parser
import Langlib.Languages.Turpentine.Typecheck
import Langlib.Languages.Unlambda.Syntax
import Std.Data.HashMap

/-!
# Turpentine to Unlambda

A hand-written compiler from Turpentine (`.turp`) to Unlambda. The write-up,
with the fragment table, the costs and the worked example, is
`docs/unlambda/compiler.md`.

Every other backend in this library compiles a machine to a machine. Unlambda
has no store, no program counter and no jumps, so this one translates the
*meaning* of a Turpentine program: a statement becomes a function from states
to states, a state is a tuple of values, and `while` is a fixed point.

The route is the one `docs/unlambda/compiler.md` laid out before any of this
existed:

1. build a lambda term (`LE`) with real variables and real binders;
2. eliminate the binders by bracket abstraction (`abs`), which is where call
   by value bites;
3. print the result, since `s`, `k`, `i` and application *are* Unlambda.

## Call by value, and the clause that is wrong

Unlambda is call by value, so the textbook clause `[x] E = k E` for an `E`
without `x` is unsound: it evaluates `E` when the closure is built rather
than when it is called, which runs a loop body before its test and prints
before the print statement is reached. `Langlib/Computability/Unlambda.lean`
found this in the completeness proof and kept the clause for *value
expressions* only; `abs` here does the same, with `isVal` as the test, and
falls back to the `s` expansion everywhere else. That fallback is what makes
a thunk a thunk: `s` evaluates neither of its arguments until an argument
arrives.

Three consequences run through the whole file, and two of them are not
optional in the way a style rule is optional: without them the compiler
builds programs no machine can run.

* Every conditional passes both branches as thunks and forces the chosen
  one, and every value used twice is bound with `letV`, because a repeated
  expression is recomputed rather than shared.
* **Constructors are strict** (`strict`). A closure that captures an
  unevaluated field recomputes it at every projection, and a loop's state is
  a chain of such closures, so the cost of reading a variable doubles per
  iteration.
* **Everything that crosses a binder must be a value** (`fixRec2`,
  `assemble`). The library is bound by two dozen `let`s; a subterm that is
  not a value cannot be carried past one with a single `k`, and the `s`
  expansion doubles it instead — two dozen times over.

## Where `c` is unavoidable

`?x`, `@` and `|` do not return booleans. They apply their argument to `i` or
to `v`, and `v` swallows everything it is handed, so a program can *act* on a
match and can do nothing at all on a mismatch — but it cannot get a value
back out of the failing branch, because every value the failing branch could
produce is `v`. The only way back is to leave: `c` captures the continuation
before the test, the matching branch throws to it, and the code after the
test is the else-branch. `testCh` and `seqB` are those two halves, and the
input primitives are the only place the compiled program uses `c` — once per
primitive, not once per test: the 256-way chain that turns a byte into a
number captures one continuation and every one of its tests throws to it.

The completeness proof uses neither `c` nor `d`; this backend uses `c`
because it has input, and never uses `d`, because bracket abstraction over
`s` already delays everything that has to be delayed.

## The fragment: all of it, except failing

Every Turpentine construct compiles: arrays, `readInt`, `readByte`,
byte-exact output, the lot. What does not survive is *failure*. Unlambda has
no runtime errors — every value can be applied to every value — so
Turpentine's four ways to fail (division by zero, an index out of bounds, a
false `assert`, a malformed or absent `readInt`) all become `e`, which stops
the program where it stands, keeping the output written so far.

## Representations

* `bool` is `k` (true) and `` `ki `` (false), so a conditional is an
  application.
* `int` is a pair of a sign bit and a Scott numeral, normalised so that zero
  is never negative. Arithmetic is therefore unary: `x + y` costs O(x) steps
  and `x * y` costs O(x·y), which is the price of the smallest arithmetic
  that has no bound. `docs/unlambda/compiler.md` measures it.
* an array is a Scott list, indexed and updated by a runtime walk.
* the state is a right-nested tuple of the program's variables, threaded
  through every statement.

## The runtime library

The combinators the compiled code needs are bound once at the top of the
program, in `Lib` order, and referenced by variable: without that, every use
of `+` would carry its own copy of the addition. Only the entries a program
actually reaches are emitted, and the set is computed by scanning the
generated term rather than from a hand-written table, so it cannot drift.
-/

namespace Langlib.Turpentine.Compile.Unlambda

open Langlib.Turpentine

/-! ## The lambda IR

Unlambda terms have no binders, so the compiler builds terms that do and
removes them afterwards. `LE` is that intermediate language: the Unlambda
leaves, application, variables numbered by a counter, and `lam`. -/

/-- A lambda term over Unlambda's builtins. -/
inductive LE where
  | var (n : Nat)
  | leaf (t : Langlib.Unlambda.Term)
  | app (f a : LE)
  | lam (x : Nat) (b : LE)
deriving Inhabited

namespace LE

/-- One past the largest variable number in the term, so that a builder can
carry on numbering above it. -/
def maxVar : LE → Nat
  | .var n => n + 1
  | .leaf _ => 0
  | .app f a => max (maxVar f) (maxVar a)
  | .lam x b => max (x + 1) (maxVar b)

/-- Does `x` occur free in this term? Binders are all distinct (the builder
hands out a fresh number for each), so no shadowing is possible and the test
is a plain search. -/
def occurs (x : Nat) : LE → Bool
  | .var y => y == x
  | .leaf _ => false
  | .app f a => occurs x f || occurs x a
  | .lam _ b => occurs x b

/-- Is this a *value expression*: one whose evaluation neither prints, nor
loops, nor computes anything, but hands back a value?

Variables count, because under call by value a variable is always bound to a
value. Partial applications of `k` and `s` count, because those are exactly
the applications the machine cannot reduce. Nothing else does: `` `.xA ``
prints, `` `iA `` reduces, and an application of a variable could do
anything.

This is the side condition that makes the `k` clause of bracket abstraction
sound. -/
def isVal : LE → Bool
  | .var _ => true
  | .leaf _ => true
  | .lam _ _ => true
  | .app (.leaf .k) a => isVal a
  | .app (.leaf .s) a => isVal a
  | .app (.app (.leaf .s) a) b => isVal a && isVal b
  | _ => false

end LE

/-! ### Building terms

Terms are built as functions from "the next unused variable number" to a
term, which is de Bruijn levels in disguise: `lam1` picks the number, hands
the body a builder for it, and builds the body one level up. Nothing can
capture, so the library below can be written with ordinary Lean functions. -/

/-- A term builder: given the next free variable number, a term. -/
abbrev Bld := Nat → LE

/-- An Unlambda builtin as a builder. -/
def lit (t : Langlib.Unlambda.Term) : Bld := fun _ => .leaf t

def cK : Bld := lit .k
def cI : Bld := lit .i
def cV : Bld := lit .v
def cC : Bld := lit .c
def cE : Bld := lit .e
def cAt : Bld := lit .at
/-- `.x`, the printer for one byte. -/
def cDot (b : UInt8) : Bld := lit (.dot b)
/-- `?x`, the test on the byte `@` last read. -/
def cQues (b : UInt8) : Bld := lit (.ques b)

def ap (f a : Bld) : Bld := fun n => .app (f n) (a n)
def ap2 (f a b : Bld) : Bld := ap (ap f a) b
def ap3 (f a b c : Bld) : Bld := ap (ap2 f a b) c

/-- `λx. body`, with `x` a number nothing else will use. -/
def lam1 (f : Bld → Bld) : Bld := fun n => .lam n (f (fun _ => .var n) (n + 1))
def lam2 (f : Bld → Bld → Bld) : Bld := lam1 fun x => lam1 fun y => f x y
def lam3 (f : Bld → Bld → Bld → Bld) : Bld := lam1 fun x => lam2 fun y z => f x y z

/-- A thunk: `λ_. e`, which under `abs` becomes a term that does not run `e`
until it is applied. Every branch of every conditional is one of these. -/
def thunk (e : Bld) : Bld := lam1 fun _ => e

/-- Force a thunk. -/
def force (e : Bld) : Bld := ap e cI

/-- `let x = v in body x`, as an application: the value is computed once and
bound, which is the only way to use a result twice without recomputing it. -/
def letV (v : Bld) (body : Bld → Bld) : Bld := ap (lam1 body) v

/-! ## Bracket abstraction -/

/-- Is `` `fa `` a value expression, given the value flags of `f` and `a`?
The shape of `f` decides it, so this needs no second traversal. -/
def valApp (f : LE) (vf va : Bool) : Bool :=
  match f with
  | .leaf .k => va
  | .leaf .s => va
  | .app (.leaf .s) _ => vf && va
  | _ => false

/-- Remove one binder, carrying up whether `x` occurred and whether the term
was a value expression, so that the two side conditions cost nothing. Asking
for them separately at every node is what makes the textbook presentation of
bracket abstraction quadratic, and the terms here have tens of thousands of
nodes in them.

The clauses are the textbook ones with the `k` clause restricted to value
expressions, which is what call by value costs:

* `[x] x = i`;
* `[x] E = `kE` when `x` is not free in `E` **and `E` is a value
  expression**, so that evaluating it early cannot be observed;
* `[x] `Ex = E` (eta) under the same restriction on `E`;
* `[x] `EF = ``s[x]E[x]F` otherwise.

Everything else in this file leans on the last clause: it is what stops a
thunk from running. -/
def absAux (x : Nat) : LE → Bool × Bool × LE
  | e@(.var y) =>
    if y == x then (true, true, .leaf .i) else (false, true, .app (.leaf .k) e)
  | e@(.leaf _) => (false, true, .app (.leaf .k) e)
  -- unreachable: `toComb` abstracts inner binders first
  | e@(.lam _ _) => (e.occurs x, true, .app (.leaf .k) e)
  | .app f a =>
    let (of, vf, af) := absAux x f
    let (oa, va, aa) := absAux x a
    let occ := of || oa
    let val := valApp f vf va
    if !occ && val then (occ, val, .app (.leaf .k) (.app f a))
    else
      let eta := match a with
        | .var y => y == x && !of && vf
        | _ => false
      if eta then (occ, val, f)
      else (occ, val, .app (.app (.leaf .s) af) aa)

def abs (x : Nat) (e : LE) : LE := (absAux x e).2.2

/-- Remove every binder, innermost first. -/
def toComb : LE → LE
  | .lam x b => abs x (toComb b)
  | .app f a => .app (toComb f) (toComb a)
  | e => e

/-- The Unlambda term for a binder-free `LE`. A leftover variable is a bug in
this compiler rather than in the program being compiled, so it is reported as
one. -/
def toTerm : LE → Except String Langlib.Unlambda.Term
  | .leaf t => .ok t
  | .app f a => return .app (← toTerm f) (← toTerm a)
  | .var n => .error s!"unlambda: internal: variable {n} escaped bracket abstraction"
  | .lam x _ => .error s!"unlambda: internal: binder {x} survived bracket abstraction"


/-! ## The combinators the compiled code is made of

Booleans are `k` and `` `ki ``, which is what makes a conditional an
application: `k` handed two arguments keeps the first, `` `ki `` the second.
Both arguments are thunks and the winner is forced, because under call by
value handing a branch over unthunked would run both. -/

def bTrue : Bld := cK
def bFalse : Bld := ap cK cI

/-- `if c then t else f`, with `t` and `f` thunks. -/
def ite (c t f : Bld) : Bld := force (ap2 c t f)

def bNot (b : Bld) : Bld := ite b (thunk bFalse) (thunk bTrue)
def bAnd (a b : Bld) : Bld := ite a (thunk b) (thunk bFalse)
def bOr (a b : Bld) : Bld := ite a (thunk bTrue) (thunk b)
/-- Boolean equality, i.e. `if a then b else ¬b`. -/
def bEq (a b : Bld) : Bld := ite a (thunk b) (thunk (bNot b))

/-- Bind a term to a variable first, unless it is already a value.

Every constructor below goes through this, and it is not an optimisation: a
closure that *captures* a computation re-runs it on every application, because
bracket abstraction has nowhere to keep the result. A pair built as
`λf. f (x+1) y` would recompute `x+1` at every projection, and a chain of such
pairs — which is what a loop's state is — costs exponentially in the number of
iterations. Constructors are strict here for the same reason they are strict
in any call-by-value language.

Building the argument is done exactly once, and the body is numbered from
above whatever binders it turned out to contain. The obvious spelling —
build it once to look at it, then let the body build it again — is
exponential in how deeply constructors nest, and the 256-entry printer table
nests 256 deep. -/
def strict (v : Bld) (body : Bld → Bld) : Bld := fun n =>
  let t := v n
  let m := max n t.maxVar
  if t.isVal then
    -- a value can be dropped in as it is; every use below uses it once
    body (fun _ => t) m
  else .app (.lam m (body (fun _ => .var m) (m + 1))) t

/-- The pair `λf. f a b`, and its two projections, which are `k` and
`` `ki `` again. -/
def pairV (a b : Bld) : Bld :=
  strict a fun x => strict b fun y => lam1 fun f => ap2 f x y
def fstV (p : Bld) : Bld := ap p cK
def sndV (p : Bld) : Bld := ap p bFalse

/-! ### Scott numerals

`0` is `λz s. z i` and `n+1` is `λz s. s n`, so a numeral *is* its own case
analysis: hand it the two branches and it picks one. Both branches are
guarded — the zero branch is a thunk, the successor branch a function of the
predecessor — so neither runs before the numeral has chosen. -/

def nZero : Bld := lam2 fun z _ => ap z cI
def nSucc (n : Bld) : Bld := strict n fun m => lam2 fun _ s => ap s m
/-- Case analysis: `z` is a thunk, `s` takes the predecessor. -/
def caseN (n z s : Bld) : Bld := ap2 n z s
def nIsZero (n : Bld) : Bld := caseN n (thunk bTrue) (lam1 fun _ => bFalse)
def nPred (n : Bld) : Bld := caseN n (thunk nZero) (lam1 fun p => p)

/-- A numeral written out in full: `m` nested successors, so `m` costs O(m)
leaves. Only used for the small ones. -/
def nLitSmall : Nat → Bld
  | 0 => nZero
  | m + 1 => nSucc (nLitSmall m)

/-! ### The library

Every combinator the generated code shares is one of these. They are bound by
`let` at the top of the emitted program, in this order, so an entry may only
mention entries above it. `emit` checks the set that is actually reachable and
emits no more than that, which is why a program with no arithmetic in it does
not carry the arithmetic. -/

inductive Lib where
  | fixZ | addN | subN | mulN | leN | eqN | divmodN
  | nth | setNth | replicate
  | mkInt | iadd | imul | ilt | ieq | idivmod
  | digits | printers | printNat | printInt | printByte
  | classify | charVal | readByte | readInt
deriving DecidableEq, Repr, Inhabited, BEq

namespace Lib

/-- Dependencies come first: the `let` that binds an entry is inside the ones
that bind everything it mentions. -/
def all : List Lib :=
  [ .fixZ, .addN, .subN, .mulN, .leN, .eqN, .divmodN
  , .nth, .setNth, .replicate
  , .mkInt, .iadd, .imul, .ilt, .ieq, .idivmod
  , .digits, .printers, .printNat, .printInt, .printByte
  , .classify, .charVal, .readByte, .readInt ]

/-- The variable number an entry is bound to. Library numbers are below
`libLimit`; everything the builder invents is above it, so a scan can tell
them apart. -/
def idx (l : Lib) : Nat := all.findIdx (· == l)

/-- Where the builder starts numbering inside a library entry, kept apart per
entry so that two entries placed side by side cannot share a binder number. -/
def base (l : Lib) : Nat := 1000 * (l.idx + 1)

end Lib

/-- Library entries are referred to by their variable. -/
def lv (l : Lib) : Bld := fun _ => .var l.idx

/-- Variable numbers below this belong to the library. -/
def libLimit : Nat := 1000

/-! ### Arithmetic on Scott numerals

All of it is unary, and all of it is a fixed point. `fixZ` is the call-by-value
Y, `Z = λf. (λg. f (λx. g g x)) (λg. f (λx. g g x))`: the eta expansion
`λx. g g x` is what stops the self-application from running before an argument
arrives. It is a library entry rather than an inlined term because inlining a
fixed point duplicates the function it is taking the fixed point of. -/

def zBody : Bld :=
  lam1 fun f =>
    ap (lam1 fun g => ap f (lam1 fun x => ap2 g g x))
       (lam1 fun g => ap f (lam1 fun x => ap2 g g x))

/-- A recursive library entry, as a lambda over its arguments.

The lambda is not decoration. A library entry is bound by a `let`, which is
an abstraction the emitted program applies, and bracket abstraction can only
lift a subterm past a binder cheaply when that subterm is a *value*: anything
else has to be expanded with `s`, which doubles it. `` `Z F `` is an
application, so an entry written that way doubles at every one of the
twenty-odd `let`s outside it, and a program that reads a byte and prints one
would not fit in memory. Written as `λa b. Z F a b` it is a lambda, hence a
value once abstracted, hence carried past each binder by a single `k`. The
price is that the fixed point is rebuilt per call, which is a constant. -/
def fixRec2 (f : Bld) : Bld := lam2 fun a b => ap2 (ap (lv .fixZ) f) a b
def fixRec3 (f : Bld) : Bld := lam3 fun a b c => ap3 (ap (lv .fixZ) f) a b c

def nAdd (a b : Bld) : Bld := ap2 (lv .addN) a b
def nSub (a b : Bld) : Bld := ap2 (lv .subN) a b
def nMul (a b : Bld) : Bld := ap2 (lv .mulN) a b
def nLe (a b : Bld) : Bld := ap2 (lv .leN) a b
def nLt (a b : Bld) : Bld := bNot (nLe b a)
def nEq (a b : Bld) : Bld := ap2 (lv .eqN) a b
/-- Quotient and remainder of two numerals, as a pair; the caller guarantees a
non-zero divisor. -/
def nDivMod (a b : Bld) : Bld := ap2 (lv .divmodN) a b

def addBody : Bld := fixRec2 (lam3 fun rec a b =>
  caseN a (thunk b) (lam1 fun a' => nSucc (ap2 rec a' b)))

/-- Truncated subtraction, walking the subtrahend, so it costs O(b). -/
def subBody : Bld := fixRec2 (lam3 fun rec a b =>
  caseN b (thunk a) (lam1 fun b' => ap2 rec (nPred a) b'))

def mulBody : Bld := fixRec2 (lam3 fun rec a b =>
  caseN a (thunk nZero) (lam1 fun a' => nAdd b (ap2 rec a' b)))

/-- `a ≤ b`, walking both, so it costs O(min a b) rather than O(a): the
difference between a division that finishes and one that does not. -/
def leBody : Bld := fixRec2 (lam3 fun rec a b =>
  caseN a (thunk bTrue) (lam1 fun a' =>
    caseN b (thunk bFalse) (lam1 fun b' => ap2 rec a' b')))

def eqBody : Bld := fixRec2 (lam3 fun rec a b =>
  caseN a (thunk (nIsZero b)) (lam1 fun a' =>
    caseN b (thunk bFalse) (lam1 fun b' => ap2 rec a' b')))

/-- Division by repeated subtraction: `b` is subtracted from `a` until it no
longer fits, and the quotient counts the subtractions. O(a) all told, because
each test costs O(b) and there are a/b of them. -/
def divmodBody : Bld := fixRec2 (lam3 fun rec a b =>
  ite (nLe b a)
    (thunk (letV (ap2 rec (nSub a b) b) fun p => pairV (nSucc (fstV p)) (sndV p)))
    (thunk (pairV nZero a)))

/-! ### Scott lists, for arrays and for the printer tables -/

def lNil : Bld := lam2 fun n _ => ap n cI
def lCons (h t : Bld) : Bld :=
  strict h fun x => strict t fun xs => lam2 fun _ c => ap2 c x xs
/-- `nilT` is a thunk, `consF` takes the head and the tail. -/
def caseL (xs nilT consF : Bld) : Bld := ap2 xs nilT consF

/-- `xs[i]`, by walking. The nil case is `v`, the black hole: every caller
bounds-checks first, so reaching it would be a compiler bug and the black hole
is what a bug deserves. -/
def nthBody : Bld := fixRec2 (lam3 fun rec i xs =>
  caseL xs (thunk cV) (lam2 fun h t =>
    caseN i (thunk h) (lam1 fun i' => ap2 rec i' t)))

def setNthBody : Bld := fixRec3 (lam1 fun rec => lam3 fun i xs v =>
  caseL xs (thunk lNil) (lam2 fun h t =>
    caseN i (thunk (lCons v t)) (lam1 fun i' => lCons h (ap3 rec i' t v))))

def replicateBody : Bld := fixRec2 (lam3 fun rec n v =>
  caseN n (thunk lNil) (lam1 fun n' => lCons v (ap2 rec n' v)))

/-! ### Integers

A signed integer is a pair of a sign bit and a magnitude, normalised so that
zero is always positive; `mkInt` is the normaliser and every operation that
can produce a zero goes through it. Sign and magnitude rather than two's
complement because there is no word to complement, and rather than a
difference of two numerals because that representation has no normal form. -/

def iSign (i : Bld) : Bld := fstV i
def iMag (i : Bld) : Bld := sndV i
def mkI (neg mag : Bld) : Bld := ap2 (lv .mkInt) neg mag

def mkIntBody : Bld := lam2 fun neg mag =>
  ite (nIsZero mag) (thunk (pairV bFalse nZero)) (thunk (pairV neg mag))

/-- Ending the run. Unlambda has no runtime errors, so the failures Turpentine
does have — division by zero, an index out of bounds, a false `assert`, a
malformed `readInt` — become `e`, which stops the program where it stands.
The output written so far is kept, which is the closest an Unlambda program
can come to the reference interpreter's error. -/
def exitB : Bld := ap cE cI

def iAdd (a b : Bld) : Bld := ap2 (lv .iadd) a b
def iMul (a b : Bld) : Bld := ap2 (lv .imul) a b
def iLt (a b : Bld) : Bld := ap2 (lv .ilt) a b
def iEq (a b : Bld) : Bld := ap2 (lv .ieq) a b
def iLe (a b : Bld) : Bld := bNot (iLt b a)
def iNeg (i : Bld) : Bld := mkI (bNot (iSign i)) (iMag i)
def iSub (a b : Bld) : Bld := iAdd a (iNeg b)

def iaddBody : Bld := lam2 fun a b =>
  ite (bEq (iSign a) (iSign b))
    (thunk (pairV (iSign a) (nAdd (iMag a) (iMag b))))
    (thunk (ite (nLe (iMag b) (iMag a))
      (thunk (mkI (iSign a) (nSub (iMag a) (iMag b))))
      (thunk (mkI (iSign b) (nSub (iMag b) (iMag a))))))

def imulBody : Bld := lam2 fun a b =>
  mkI (bNot (bEq (iSign a) (iSign b))) (nMul (iMag a) (iMag b))

def iltBody : Bld := lam2 fun a b =>
  ite (iSign a)
    (thunk (ite (iSign b) (thunk (nLt (iMag b) (iMag a))) (thunk bTrue)))
    (thunk (ite (iSign b) (thunk bFalse) (thunk (nLt (iMag a) (iMag b)))))

def ieqBody : Bld := lam2 fun a b =>
  bAnd (bEq (iSign a) (iSign b)) (nEq (iMag a) (iMag b))

/-- Euclidean division, as Turpentine specifies it: the remainder is never
negative. The magnitudes divide truncatingly, and the three corrections below
are what turns that into Turpentine's answer — a negative dividend with a
non-zero remainder is the case that moves the quotient away from zero and
reflects the remainder. Returns the pair `(a / b, a % b)`. -/
def idivmodBody : Bld := lam2 fun a b =>
  ite (nIsZero (iMag b)) (thunk exitB) (thunk (
    letV (nDivMod (iMag a) (iMag b)) fun p =>
      ite (iSign a)
        (thunk (ite (nIsZero (sndV p))
          (thunk (pairV (mkI (bNot (iSign b)) (fstV p)) (pairV bFalse nZero)))
          (thunk (pairV (mkI (bNot (iSign b)) (nSucc (fstV p)))
                        (mkI bFalse (nSub (iMag b) (sndV p)))))))
        (thunk (pairV (mkI (iSign b) (fstV p)) (mkI bFalse (sndV p))))))

def iDivMod (a b : Bld) : Bld := ap2 (lv .idivmod) a b

/-! ### Output

`.x` prints one byte and hands back its argument, so printing a *computed*
byte means choosing a printer at run time: the tables below are lists of
printers and the byte is the index. That is the whole of the output side. -/

def digitsBody : Bld :=
  (List.range 10).foldr (fun d acc => lCons (cDot (UInt8.ofNat (48 + d))) acc) lNil

def printersBody : Bld :=
  (List.range 256).foldr (fun b acc => lCons (cDot (UInt8.ofNat b)) acc) lNil

/-- Print a numeral in decimal, most significant digit first: divide by ten,
print the quotient, then print the digit. The recursive call is the argument
of the digit's printer, so it runs first, which is what puts the digits in the
right order. -/
def printNatBody : Bld := fixRec2 (lam3 fun rec n s =>
  letV (nDivMod n (nLitSmall 10)) fun p =>
    ite (nIsZero (fstV p))
      (thunk (ap (ap2 (lv .nth) (sndV p) (lv .digits)) s))
      (thunk (ap (ap2 (lv .nth) (sndV p) (lv .digits)) (ap2 rec (fstV p) s))))

def printIntBody : Bld := lam2 fun i s =>
  ite (iSign i)
    (thunk (ap2 (lv .printNat) (iMag i) (ap (cDot 45) s)))
    (thunk (ap2 (lv .printNat) (iMag i) s))

/-- `printByte(e)` prints `e mod 256`, Euclidean, so a negative argument still
names a byte; the remainder is then the index into the printer table. -/
def printByteBody : Bld := lam2 fun i s =>
  letV (sndV (iDivMod i (pairV bFalse (nLitSmall 256)))) fun r =>
    ap (ap2 (lv .nth) (iMag r) (lv .printers)) s

/-! ### Input, and the only use of `c`

`?x` answers `i` or `v`, and there is no way to see a `v` from the inside: it
swallows whatever the failing branch would have returned. So every test here
runs under a captured continuation, and a *match* is what leaves. The code
after a test is its else-branch, reached by falling through. -/

/-- Sequence: run `first` for its effect, then `next`. It has to be an
abstraction rather than `` `k ``: `` ``k<next><first> `` evaluates `next`
first, which is exactly backwards. -/
def seqB (first next : Bld) : Bld := ap (thunk next) first

/-- One test: if the byte `@` last read is `ch`, leave through `k` carrying
`val`; otherwise evaluate to `v` and let the caller fall through. -/
def testCh (k : Bld) (ch : UInt8) (val : Bld) : Bld :=
  force (ap (cQues ch) (lam1 fun b => ap b (thunk (ap k val))))

/-- The value of the byte `@` last read, as a numeral: 256 tests in a row,
each one carrying the count of the tests before it. The count is an argument
rather than a literal, so the chain costs a constant per byte value rather
than growing with it. -/
def charValBody : Bld := lam1 fun _ =>
  ap cC (lam1 fun k =>
    ap ((List.range 256).foldr
        (fun i acc => lam1 fun a =>
          seqB (testCh k (UInt8.ofNat i) a) (ap acc (nSucc a)))
        (lam1 fun _ => nZero))
      nZero)

/-- Classify the byte `@` last read for `readInt`: `0` whitespace, `1`
newline, `2` a minus sign, `3 + d` the digit `d`. Anything else ends the run,
because Turpentine's `readInt` fails on a malformed line. -/
def classifyBody : Bld := lam1 fun _ =>
  ap cC (lam1 fun k =>
    ([(32, 0), (9, 0), (13, 0), (10, 1), (45, 2)] ++
      (List.range 10).map (fun d => (48 + d, 3 + d))).foldr
      (fun (p : Nat × Nat) acc =>
        seqB (testCh k (UInt8.ofNat p.1) (nLitSmall p.2)) acc)
      exitB)

/-- `readByte()`: `-1` at end of input, the byte's value otherwise. `@` is the
read, and it answers the same way `?x` does, so the end-of-input case is again
the one that falls through. -/
def readByteBody : Bld := lam1 fun _ =>
  ap cC (lam1 fun k =>
    seqB (force (ap cAt (lam1 fun b =>
            ap b (thunk (ap k (mkI bFalse (ap (lv .charVal) cI)))))))
         (pairV bTrue (nLitSmall 1)))

/-- One turn of the `readInt` machine: classify the byte just read and either
carry on with a new phase, finish the number, or stop the run. -/
def readIntStep (rec phase acc neg : Bld) : Bld :=
  letV (ap (lv .classify) cI) fun code =>
    ite (nIsZero code)
      -- whitespace: allowed before the number, and after it
      (thunk (ite (nLe (nLitSmall 2) phase)
        (thunk (ap3 rec (nLitSmall 3) acc neg))
        (thunk (ite (nIsZero phase)
          (thunk (ap3 rec phase acc neg))
          (thunk exitB)))))
      (thunk (ite (nIsZero (nPred code))
        -- a newline ends the line, and with it the number
        (thunk (ite (nLe (nLitSmall 2) phase) (thunk (mkI neg acc)) (thunk exitB)))
        (thunk (ite (nIsZero (nPred (nPred code)))
          -- a minus sign, which only the very front accepts
          (thunk (ite (nIsZero phase)
            (thunk (ap3 rec (nLitSmall 1) acc bTrue))
            (thunk exitB)))
          -- a digit, which the trailing whitespace does not accept
          (thunk (ite (nLe (nLitSmall 3) phase)
            (thunk exitB)
            (thunk (ap3 rec (nLitSmall 2)
              (nAdd (nMul acc (nLitSmall 10)) (nSub code (nLitSmall 3)))
              neg))))))))

/-- `readInt()`: one line, parsed as Turpentine's `parseNumLine` parses it —
whitespace at either end, an optional minus, at least one digit, nothing else.
`phase` is where the little machine is: `0` before the number, `1` after the
minus, `2` in the digits, `3` in the trailing whitespace. Anything the parser
would reject, and end of input before any digit, ends the run. -/
def readIntBody : Bld := lam1 fun _ =>
  ap3 (ap (lv .fixZ) (lam1 fun rec => lam3 fun phase acc neg =>
        ap cC (lam1 fun k =>
          seqB
            (force (ap cAt (lam1 fun b =>
              ap b (thunk (ap k (readIntStep rec phase acc neg))))))
            -- end of input: a number already read is a number, nothing is an error
            (ite (nLe (nLitSmall 2) phase) (thunk (mkI neg acc)) (thunk exitB)))))
      nZero nZero bFalse

/-- The term bound to each library variable. -/
def Lib.body : Lib → Bld
  | .fixZ => zBody
  | .addN => addBody
  | .subN => subBody
  | .mulN => mulBody
  | .leN => leBody
  | .eqN => eqBody
  | .divmodN => divmodBody
  | .nth => nthBody
  | .setNth => setNthBody
  | .replicate => replicateBody
  | .mkInt => mkIntBody
  | .iadd => iaddBody
  | .imul => imulBody
  | .ilt => iltBody
  | .ieq => ieqBody
  | .idivmod => idivmodBody
  | .digits => digitsBody
  | .printers => printersBody
  | .printNat => printNatBody
  | .printInt => printIntBody
  | .printByte => printByteBody
  | .classify => classifyBody
  | .charVal => charValBody
  | .readByte => readByteBody
  | .readInt => readIntBody

/-- An integer literal. Small ones are written out; larger ones are built by
Horner's rule out of their decimal digits, because a numeral written out costs
a leaf per unit and `1000000` would be a megabyte of backquotes. -/
def nLit (m : Nat) : Bld :=
  if m ≤ 16 then nLitSmall m
  else
    match (toString m).toList.map (fun c => c.toNat - 48) with
    | [] => nZero
    | d :: ds => ds.foldl
        (fun acc e => nAdd (nMul acc (nLitSmall 10)) (nLitSmall e)) (nLitSmall d)

def iLit (n : Int) : Bld :=
  if n == 0 then pairV bFalse nZero
  else pairV (if n < 0 then bTrue else bFalse) (nLit n.natAbs)


/-! ## Assembling a program

The library is bound by a chain of `let`s around the compiled body — a `let`
being an application of an abstraction, like everything else here. Without it
each use of `+` would carry its own copy of the addition, since Unlambda has
no way to name anything and no sharing in its syntax.

Which entries to bind is decided by looking: the compiled body is scanned for
library variables, and the answer is closed under the entries those entries
mention. A hand-written dependency table would be a second thing to keep true.
-/

/-- The library variables a term mentions. -/
def libVarsIn (e : LE) : List Nat :=
  go e []
where
  go : LE → List Nat → List Nat
    | .var n, acc => if n < libLimit && !acc.contains n then n :: acc else acc
    | .leaf _, acc => acc
    | .app f a, acc => go a (go f acc)
    | .lam _ b, acc => go b acc

def libsOf (e : LE) : List Lib :=
  let vs := libVarsIn e
  Lib.all.filter (fun l => vs.contains l.idx)

/-- What each entry mentions directly. Built once and passed down: rebuilding
an entry to ask the question again is the sort of thing that turns a
256-element table into a minute of compiling. -/
def depTable : List (Lib × List Lib) :=
  Lib.all.map fun l => (l, libsOf (Lib.body l l.base))

def depsOf (table : List (Lib × List Lib)) (l : Lib) : List Lib :=
  match table.find? (fun p => p.1 == l) with
  | some p => p.2
  | none => []

/-- Close a set of entries under their dependencies. At most one entry can be
added per round, so `Lib.all.length` rounds is more than enough. -/
def libClose (table : List (Lib × List Lib)) : Nat → List Lib → List Lib
  | 0, s => s
  | n + 1, s =>
    let s' := Lib.all.filter fun l => s.contains l || s.any fun m => (depsOf table m).contains l
    if s'.length == s.length then s else libClose table n s'

/-- Where the builder starts numbering the compiled body: above every library
entry's own range, so that no two binders can collide however deeply a source
program nests. A builder numbers by *depth* rather than by count — the two
sides of an application are handed the same number — so the distance between
these bases is nesting depth, not program size. -/
def coreBase : Nat := 1_000_000

/-- Wrap the compiled body in the `let`s that bind the library.

The body goes in as a thunk and is forced at the very end, for the same
reason the library entries are lambdas: a bare application would be expanded
with `s` at every enclosing binder, once per library entry, and doubling
twenty-odd times is not a compiler. Thunked, it is a value, so each binder
carries it past with a `k`; forcing it costs one application. -/
def assemble (core : Bld) : Except String Langlib.Unlambda.Term :=
  let e := (force (thunk core)) coreBase
  let used := libClose depTable Lib.all.length (libsOf e)
  toTerm (toComb (used.foldr (fun l acc => .app (.lam l.idx acc) (Lib.body l l.base)) e))


/-! ## The state

A Turpentine program's variables live in one right-nested tuple, in
declaration order, and every statement is a function from that tuple to the
next one. Reaching slot `i` is `i` projections; writing it rebuilds the
tuple down to that slot, which costs O(i) and is why the slots are handed
out in declaration order rather than by use.
-/

/-- Skip the first `i` slots. -/
def dropSlots : Nat → Bld → Bld
  | 0, s => s
  | i + 1, s => dropSlots i (sndV s)

def getSlot (i : Nat) (σ : Bld) : Bld := fstV (dropSlots i σ)

def setSlot : Nat → Bld → Bld → Bld
  | 0, σ, v => pairV v (sndV σ)
  | i + 1, σ, v => letV σ fun s => pairV (fstV s) (setSlot i (sndV s) v)

/-- Print a run of bytes known at compile time and hand back `k`. This is the
chain from Madore's own hello world: each printer is applied to the next, so
`` ``.H.e.l `` prints `H`, then `e`, and the last one is applied to whatever
comes after. -/
def printBytes (bs : List UInt8) (k : Bld) : Bld :=
  match bs with
  | [] => k
  | b :: rest => ap (rest.foldl (fun acc c => ap acc (cDot c)) (cDot b)) k

def printStrB (str : String) (k : Bld) : Bld := printBytes str.toUTF8.toList k

/-! ## Compiling expressions and statements -/

/-- What the code generator needs to know: the declared types (for the
distinction between an `int` and a `bool` comparison, and for array lengths)
and which tuple slot each variable lives in. -/
structure Env where
  types : Langlib.Turpentine.Ctx
  slot : Std.HashMap String Nat

def Env.slotOf (c : Env) (x : String) : Except String Nat :=
  match c.slot[x]? with
  | some i => .ok i
  | none => .error s!"unlambda: internal: no slot for '{x}'"

def Env.lenOf (c : Env) (x : String) : Except String Nat :=
  match c.types[x]? with
  | some (.array _ n) => .ok n
  | _ => .error s!"unlambda: internal: '{x}' is not an array"

/-- Reading `a[i]`: the index is checked against the length, which is known
at compile time, and a bad one stops the run. -/
def loadIndexTerm (slot n : Nat) (σ iv : Bld) : Bld :=
  letV iv fun v =>
    ite (bAnd (bNot (iSign v)) (nLt (iMag v) (nLit n)))
      (thunk (ap2 (lv .nth) (iMag v) (getSlot slot σ)))
      (thunk exitB)

/-- Writing `a[i] := v`: the same check, then the array slot is rebuilt around
the new element. -/
def storeIndexTerm (slot n : Nat) (σ iv vv : Bld) : Bld :=
  letV iv fun v =>
    ite (bAnd (bNot (iSign v)) (nLt (iMag v) (nLit n)))
      (thunk (setSlot slot σ (ap3 (lv .setNth) (iMag v) (getSlot slot σ) vv)))
      (thunk exitB)

/-- Compile an expression to a function of the state tuple.

Turpentine expressions are pure, so this returns a value and touches nothing;
the only thing it can do besides compute is stop the run, which is what a
division by zero and an index out of bounds do. -/
def compileExpr (c : Env) : Expr → Except String (Bld → Bld)
  | .intLit n => return fun _ => iLit n
  | .boolLit b => return fun _ => if b then bTrue else bFalse
  | .var x => do
    let i ← c.slotOf x
    return fun σ => getSlot i σ
  | .len x => do
    let n ← c.lenOf x
    return fun _ => iLit (Int.ofNat n)
  | .index x i => do
    let slot ← c.slotOf x
    let n ← c.lenOf x
    let iv ← compileExpr c i
    return fun σ => loadIndexTerm slot n σ (iv σ)
  | .un .neg e => do
    let v ← compileExpr c e
    return fun σ => iNeg (v σ)
  | .un .not e => do
    let v ← compileExpr c e
    return fun σ => bNot (v σ)
  | .bin op e₁ e₂ => do
    let a ← compileExpr c e₁
    let b ← compileExpr c e₂
    match op with
    -- The short-circuiting pair: the right operand goes into a thunk, which
    -- is the whole point — `x != 0 && 10 / x > 1` must not divide by zero.
    | .and => return fun σ => bAnd (a σ) (b σ)
    | .or => return fun σ => bOr (a σ) (b σ)
    | .add => return fun σ => iAdd (a σ) (b σ)
    | .sub => return fun σ => iSub (a σ) (b σ)
    | .mul => return fun σ => iMul (a σ) (b σ)
    | .div => return fun σ => fstV (iDivMod (a σ) (b σ))
    | .mod => return fun σ => sndV (iDivMod (a σ) (b σ))
    | .lt => return fun σ => iLt (a σ) (b σ)
    | .le => return fun σ => iLe (a σ) (b σ)
    | .gt => return fun σ => iLt (b σ) (a σ)
    | .ge => return fun σ => iLe (b σ) (a σ)
    | .eq | .ne => do
      -- `==` compares two ints or two bools, and those are different values
      let t ← (inferExpr c.types e₁).mapError ("unlambda: internal: " ++ ·)
      let same : Bld → Bld → Bld :=
        if t == .bool then bEq else iEq
      match op with
      | .eq => return fun σ => same (a σ) (b σ)
      | _ => return fun σ => bNot (same (a σ) (b σ))

/-- The value a declaration starts at: `0`, `false`, or an array of those. -/
def defaultVal : Ty → Bld
  | .int => iLit 0
  | .bool => bFalse
  | .array elem n => ap2 (lv .replicate) (nLit n) (defaultVal elem)

/-- Compile a statement to a function from state to state. -/
def compileStmt (c : Env) : Stmt → Except String Bld
  | .skip => return cI
  | .seq s₁ s₂ => do
    let f ← compileStmt c s₁
    let g ← compileStmt c s₂
    return lam1 fun σ => ap g (ap f σ)
  | .assign x e => do
    let i ← c.slotOf x
    let v ← compileExpr c e
    return lam1 fun σ => setSlot i σ (v σ)
  | .ite cond s₁ s₂ => do
    let b ← compileExpr c cond
    let f ← compileStmt c s₁
    let g ← compileStmt c s₂
    return lam1 fun σ => ite (b σ) (thunk (ap f σ)) (thunk (ap g σ))
  -- The fixed point: the loop is a function of the state that either runs the
  -- body and calls itself on the result, or hands the state back. Both arms
  -- are thunks, because under call by value an unguarded recursive arm would
  -- run before the test chose it, and the loop would never stop.
  | .while cond body => do
    let b ← compileExpr c cond
    let f ← compileStmt c body
    return ap (lv .fixZ) (lam2 fun rec σ =>
      ite (b σ) (thunk (ap rec (ap f σ))) (thunk σ))
  | .assert e => do
    let b ← compileExpr c e
    return lam1 fun σ => ite (b σ) (thunk σ) (thunk exitB)
  | .assignIndex x i e => do
    let slot ← c.slotOf x
    let n ← c.lenOf x
    let iv ← compileExpr c i
    let ev ← compileExpr c e
    return lam1 fun σ => storeIndexTerm slot n σ (iv σ) (ev σ)
  | .readInt x => do
    let i ← c.slotOf x
    return lam1 fun σ => setSlot i σ (ap (lv .readInt) cI)
  | .readByte x => do
    let i ← c.slotOf x
    return lam1 fun σ => setSlot i σ (ap (lv .readByte) cI)
  -- The read happens before the bounds check, as it does in the reference
  -- interpreter: a bad index stops the run either way, but the byte is gone.
  | .readIntIndex x i => do
    let slot ← c.slotOf x
    let n ← c.lenOf x
    let iv ← compileExpr c i
    return lam1 fun σ => letV (ap (lv .readInt) cI) fun v =>
      storeIndexTerm slot n σ (iv σ) v
  | .readByteIndex x i => do
    let slot ← c.slotOf x
    let n ← c.lenOf x
    let iv ← compileExpr c i
    return lam1 fun σ => letV (ap (lv .readByte) cI) fun v =>
      storeIndexTerm slot n σ (iv σ) v
  | .printExpr e nl => do
    let v ← compileExpr c e
    let t ← (inferExpr c.types e).mapError ("unlambda: internal: " ++ ·)
    let nlB : Bld → Bld := fun k => if nl then ap (cDot 10) k else k
    if t == .bool then
      return lam1 fun σ => ite (v σ)
        (thunk (nlB (printStrB "true" σ))) (thunk (nlB (printStrB "false" σ)))
    else
      return lam1 fun σ => nlB (ap2 (lv .printInt) (v σ) σ)
  | .printStr str nl =>
    return lam1 fun σ => printStrB (if nl then str ++ "\n" else str) σ
  | .printByte e => do
    let v ← compileExpr c e
    return lam1 fun σ => ap2 (lv .printByte) (v σ) σ

/-! ## The program -/

/-- Compile a parsed, type-checked program to an Unlambda term: lay the
variables out in a tuple, run the declarations' initialisers as assignments
(a declaration cannot see a later one, so the order is the source's), then
the body. -/
def compileProgram (p : Program) (Γ : Langlib.Turpentine.Ctx) :
    Except String Langlib.Unlambda.Term := do
  let mut slot : Std.HashMap String Nat := {}
  for h : i in [0 : p.decls.length] do
    slot := slot.insert (p.decls[i]'(h.upper)).1 i
  let c : Env := { types := Γ, slot }
  let init := p.decls.foldr (fun d acc => pairV (defaultVal d.2.1) acc) cI
  let inits := p.decls.filterMap fun d => d.2.2.map (Stmt.assign d.1)
  let f ← compileStmt c (inits.foldr Stmt.seq p.body)
  assemble (ap f init)

/-- Parse, type-check and compile: the term the backend produces. -/
def compileTerm (src : String) : Except String Langlib.Unlambda.Term := do
  let prog ← parse src
  let Γ ← (checkProgram prog).mapError ("type error: " ++ ·)
  compileProgram prog Γ

/-- The header comment the emitted file carries. Unlambda has `#` comments,
so a compiled program can say where it came from. -/
def header (t : Langlib.Unlambda.Term) : String :=
  s!"# compiled by turpentine, bespoke backend to unlambda: {t.size} builtins.\n"

/-- Turpentine source text to an Unlambda program, **as bytes**: the entry
point the runner's `--to unlambda` uses, and what gets written to a file.

Bytes rather than text because a printed byte is spelled in the program: a
program that prints byte 200 has `.` followed by byte 200 in it, and a string
holding that byte would be written out as its two-byte UTF-8 encoding, which
parses back as a dot carrying 195 followed by an unrecognised command.
`Langlib.Unlambda.parseBytes` is the other end. -/
def compileBytes (src : String) : Except String ByteArray := do
  let t ← compileTerm src
  return (header t).toUTF8 ++ t.renderBytes ++ (String.toUTF8 "\n")

/-- An emitted program as text, one character per byte: what the runner shows
and measures. It is what the *file* holds only when every byte the program
prints is ASCII, which is why `compileBytes` is what the file is written
from. -/
def renderText (bs : ByteArray) : String :=
  String.ofList (bs.toList.map fun b => Char.ofNat b.toNat)

end Langlib.Turpentine.Compile.Unlambda
