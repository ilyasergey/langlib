import Langlib.Computability.Brainfuck
import Langlib.Languages.Brainloller

/-!
# Brainloller is Turing complete

Brainloller (Lode Vandevenne, 2005) is brainfuck painted one command to a
pixel, with two extra colours that turn the instruction pointer so a
program can wrap into a rectangle. Decoding walks the pointer over the
image, collects the command characters and hands them to the brainfuck
parser; execution is then the brainfuck evaluator, with brainfuck's
conventions throughout (`docs/brainloller/spec.md`).

So a Brainloller program, once decoded, *is* a `Langlib.Brainfuck.Prog`,
and `Langlib.Computability.URMBrainfuck.compile` is already a compiler
from the unlimited register machine into it. `brainlollerComplete` is
therefore `brainfuckComplete` re-labelled: same compiler, same encodings,
same simulation theorem.

## The pictorial round trip, and how far it is proved

Compiling to Brainloller renders a program as brainfuck text and paints
that text. Reading it back is three steps, and this file proves two of
them:

1. **the pixel walk**: `decode img` recovers the command characters that
   were painted. *Not proved here*; it is checked by test at several row
   widths in `Langlib/Tests/Brainloller.lean` and
   `Langlib/Tests/CompileBrainloller.lean`. The walk is a fuelled
   traversal of a serpentine layout built by a private array-filling loop,
   and pinning it down in Lean is a separate piece of work.
2. **nothing is lost in the paint**: `bfCommands_renderBf` shows that a
   rendered program consists entirely of the eight command characters, so
   the encoder's filter drops nothing and adds nothing.
3. **the brainfuck parser is a left inverse of the renderer**:
   `parse_renderBf` shows `Langlib.Brainfuck.parse (renderBf p) = .ok p`
   for every program, proved by induction through the shipped parser's
   character loop.

`decodeProg_of_decode` composes 2 and 3: **if** the walk recovers the
painted characters, the decoded program is the one that was compiled. So
the whole obligation is reduced to step 1, and step 1 alone is what the
tests carry.

## Why `renderBf` and not `Langlib.Brainfuck.Prog.render`

`Langlib.Brainfuck.Op.render` is a `partial def`, which Lean compiles to
an **opaque** constant: no equations, no reduction, and therefore no
theorem can mention it (`#print Langlib.Brainfuck.Op.render` reports
`opaque`). `renderBf` below is a total re-implementation emitting the same
string, and it is the one the theorems are about.
`Langlib/Tests/CompileBrainloller.lean` checks byte-for-byte that the two
agree on the programs the Turpentine backend emits.

## What is proved, and what is not

`brainlollerComplete` says: every URM program that halts with `result` in
register 0 is simulated by a Brainloller program that halts with `result`
bytes of output. Not proved, and not claimed: that Brainloller computes
every partial computable function (that step is the cited classical
result, Shepherdson and Sturgis 1963; see
`Langlib.Computability.computes_of_turingComplete`), anything about
divergence (`simulates` constrains halting runs only), and the pixel walk
above.
-/

namespace Langlib.Computability.BrainlollerSyntax

open Langlib.Brainfuck (Op Prog)
open Langlib.Common (Rgb Image)

/-! ## A total renderer -/

/-- The characters of one command. -/
def renderOp : Op → List Char
  | .inc => ['+']
  | .dec => ['-']
  | .right => ['>']
  | .left => ['<']
  | .output => ['.']
  | .input => [',']
  | .loop body => '[' :: (body.flatMap renderOp ++ [']'])

def renderOps (p : Prog) : List Char := p.flatMap renderOp

/-- Render a program as brainfuck source. A total re-implementation of
`Langlib.Brainfuck.Prog.render`, which is opaque to Lean; see the module
docstring. -/
def renderBf (p : Prog) : String := String.ofList (renderOps p)

/-! ## The brainfuck parser's loop

`Langlib.Brainfuck.parse` is a `for` loop over private position state, so
the loop body cannot be named from outside the module. `BodySpec` states
what the body does instead, over an abstract position type; the hypotheses
are discharged by `rfl` against the real body where the generic lemma is
applied. -/

/-- The parser's loop state: the commands of the innermost program so far
(reversed), the stack of enclosing programs each tagged with a position,
and the current position. -/
abbrev St (P : Type) := List Op × List (P × List Op) × P

/-- What the brainfuck parser's `for` body does on each of the eight
commands. Positions are existentially quantified where they are produced,
because nothing downstream depends on them. -/
structure BodySpec {P : Type}
    (f : Char → St P → Except String (ForInStep (St P))) : Prop where
  inc : ∀ cur stack (pos : P), ∃ q,
    f '+' (cur, stack, pos) = pure (.yield (Op.inc :: cur, stack, q))
  dec : ∀ cur stack (pos : P), ∃ q,
    f '-' (cur, stack, pos) = pure (.yield (Op.dec :: cur, stack, q))
  right : ∀ cur stack (pos : P), ∃ q,
    f '>' (cur, stack, pos) = pure (.yield (Op.right :: cur, stack, q))
  left : ∀ cur stack (pos : P), ∃ q,
    f '<' (cur, stack, pos) = pure (.yield (Op.left :: cur, stack, q))
  output : ∀ cur stack (pos : P), ∃ q,
    f '.' (cur, stack, pos) = pure (.yield (Op.output :: cur, stack, q))
  input : ∀ cur stack (pos : P), ∃ q,
    f ',' (cur, stack, pos) = pure (.yield (Op.input :: cur, stack, q))
  open_ : ∀ cur stack (pos : P), ∃ q,
    f '[' (cur, stack, pos) = pure (.yield ([], (pos, cur) :: stack, q))
  close : ∀ cur (o : P) outer stack (pos : P), ∃ q,
    f ']' (cur, (o, outer) :: stack, pos)
      = pure (.yield (Op.loop cur.reverse :: outer, stack, q))

/-- Running the loop over a rendered program pushes exactly that program
onto the accumulator and leaves the stack alone. -/
theorem key {P : Type} (f : Char → St P → Except String (ForInStep (St P)))
    (hs : BodySpec f) :
    ∀ (p : Prog) (rest : List Char) (cur : List Op)
      (stack : List (P × List Op)) (pos : P),
      ∃ pos', forIn (renderOps p ++ rest) (cur, stack, pos) f
            = forIn rest (p.reverse ++ cur, stack, pos') f
  | [], rest, cur, stack, pos => ⟨pos, by simp [renderOps]⟩
  | op :: t, rest, cur, stack, pos => by
    have hsplit : renderOps (op :: t) ++ rest
        = renderOp op ++ (renderOps t ++ rest) := by
      simp [renderOps, List.append_assoc]
    rw [hsplit]
    cases op with
    | inc =>
      obtain ⟨q, hq⟩ := hs.inc cur stack pos
      obtain ⟨pos', h⟩ := key f hs t rest (Op.inc :: cur) stack q
      refine ⟨pos', ?_⟩
      simp only [renderOp, List.cons_append, List.nil_append, List.forIn_cons, hq]
      rw [show (pure (ForInStep.yield (Op.inc :: cur, stack, q)) :
          Except String (ForInStep (St P))) >>= _
        = forIn (renderOps t ++ rest) (Op.inc :: cur, stack, q) f from rfl, h]
      simp
    | dec =>
      obtain ⟨q, hq⟩ := hs.dec cur stack pos
      obtain ⟨pos', h⟩ := key f hs t rest (Op.dec :: cur) stack q
      refine ⟨pos', ?_⟩
      simp only [renderOp, List.cons_append, List.nil_append, List.forIn_cons, hq]
      rw [show (pure (ForInStep.yield (Op.dec :: cur, stack, q)) :
          Except String (ForInStep (St P))) >>= _
        = forIn (renderOps t ++ rest) (Op.dec :: cur, stack, q) f from rfl, h]
      simp
    | right =>
      obtain ⟨q, hq⟩ := hs.right cur stack pos
      obtain ⟨pos', h⟩ := key f hs t rest (Op.right :: cur) stack q
      refine ⟨pos', ?_⟩
      simp only [renderOp, List.cons_append, List.nil_append, List.forIn_cons, hq]
      rw [show (pure (ForInStep.yield (Op.right :: cur, stack, q)) :
          Except String (ForInStep (St P))) >>= _
        = forIn (renderOps t ++ rest) (Op.right :: cur, stack, q) f from rfl, h]
      simp
    | left =>
      obtain ⟨q, hq⟩ := hs.left cur stack pos
      obtain ⟨pos', h⟩ := key f hs t rest (Op.left :: cur) stack q
      refine ⟨pos', ?_⟩
      simp only [renderOp, List.cons_append, List.nil_append, List.forIn_cons, hq]
      rw [show (pure (ForInStep.yield (Op.left :: cur, stack, q)) :
          Except String (ForInStep (St P))) >>= _
        = forIn (renderOps t ++ rest) (Op.left :: cur, stack, q) f from rfl, h]
      simp
    | output =>
      obtain ⟨q, hq⟩ := hs.output cur stack pos
      obtain ⟨pos', h⟩ := key f hs t rest (Op.output :: cur) stack q
      refine ⟨pos', ?_⟩
      simp only [renderOp, List.cons_append, List.nil_append, List.forIn_cons, hq]
      rw [show (pure (ForInStep.yield (Op.output :: cur, stack, q)) :
          Except String (ForInStep (St P))) >>= _
        = forIn (renderOps t ++ rest) (Op.output :: cur, stack, q) f from rfl, h]
      simp
    | input =>
      obtain ⟨q, hq⟩ := hs.input cur stack pos
      obtain ⟨pos', h⟩ := key f hs t rest (Op.input :: cur) stack q
      refine ⟨pos', ?_⟩
      simp only [renderOp, List.cons_append, List.nil_append, List.forIn_cons, hq]
      rw [show (pure (ForInStep.yield (Op.input :: cur, stack, q)) :
          Except String (ForInStep (St P))) >>= _
        = forIn (renderOps t ++ rest) (Op.input :: cur, stack, q) f from rfl, h]
      simp
    | loop b =>
      obtain ⟨q, hq⟩ := hs.open_ cur stack pos
      obtain ⟨p1, h1⟩ := key f hs b (']' :: (renderOps t ++ rest)) []
        ((pos, cur) :: stack) q
      obtain ⟨r, hr⟩ := hs.close (b.reverse ++ []) pos cur stack p1
      obtain ⟨pos', h2⟩ := key f hs t rest (Op.loop b :: cur) stack r
      refine ⟨pos', ?_⟩
      have hb : renderOp (Op.loop b) ++ (renderOps t ++ rest)
          = '[' :: (renderOps b ++ (']' :: (renderOps t ++ rest))) := by
        simp [renderOp, renderOps, List.append_assoc]
      rw [hb, List.forIn_cons, hq]
      rw [show (pure (ForInStep.yield (([] : List Op), (pos, cur) :: stack, q)) :
          Except String (ForInStep (St P))) >>= _
        = forIn (renderOps b ++ (']' :: (renderOps t ++ rest)))
            (([] : List Op), (pos, cur) :: stack, q) f from rfl, h1]
      rw [List.forIn_cons]
      simp only [List.append_nil] at hr
      simp only [List.append_nil, hr]
      rw [show (pure (ForInStep.yield
            (Op.loop b.reverse.reverse :: cur, stack, r)) :
          Except String (ForInStep (St P))) >>= _
        = forIn (renderOps t ++ rest)
            (Op.loop b.reverse.reverse :: cur, stack, r) f from rfl]
      simp only [List.reverse_reverse]
      rw [h2]
      simp

theorem parse_generic {P : Type}
    (f : Char → St P → Except String (ForInStep (St P)))
    (fin : St P → Except String Prog)
    (hs : BodySpec f)
    (hfin : ∀ (cur : List Op) (pos : P), fin (cur, [], pos) = .ok cur.reverse)
    (p : Prog) (pos : P) :
    (do
      let s ← forIn (renderOps p)
        (([] : List Op), ([] : List (P × List Op)), pos) f
      fin s) = .ok p := by
  obtain ⟨pos', h⟩ := key f hs p [] [] [] pos
  rw [show renderOps p = renderOps p ++ ([] : List Char) by simp]
  rw [h]
  simp only [List.forIn_nil, List.append_nil]
  show fin (p.reverse, [], pos') = _
  rw [hfin]
  simp

/-- **The brainfuck parser is a left inverse of the renderer.** -/
theorem parse_renderBf (p : Prog) :
    Langlib.Brainfuck.parse (renderBf p) = .ok p := by
  unfold Langlib.Brainfuck.parse renderBf
  simp only [String.toList_ofList]
  refine parse_generic _ _ ?_ ?_ p _
  · constructor <;> intros <;> exact ⟨_, rfl⟩
  · intros; rfl

/-! ## The paint keeps every command -/

/-- Every character a rendered program contains is one of the eight
brainfuck commands, so it has a colour. -/
theorem rgbOfCmd_isSome : ∀ (p : Prog) (c : Char), c ∈ renderOps p →
    (Langlib.Brainloller.rgbOfCmd c).isSome = true
  | [], c, h => by simp [renderOps] at h
  | op :: t, c, h => by
    simp only [renderOps, List.flatMap_cons, List.mem_append] at h
    rcases h with h | h
    · cases op with
      | loop b =>
        simp only [renderOp, List.mem_cons, List.mem_append,
          List.not_mem_nil, or_false] at h
        rcases h with h | h | h
        · subst h; rfl
        · exact rgbOfCmd_isSome b c (by simpa [renderOps] using h)
        · subst h; rfl
      | _ => simp only [renderOp, List.mem_singleton] at h; subst h; rfl
    · exact rgbOfCmd_isSome t c (by simpa [renderOps] using h)
  termination_by p => sizeOf p

/-- The encoder's filter drops nothing from a rendered program. -/
theorem bfCommands_renderBf (p : Prog) :
    Langlib.Brainloller.bfCommands (renderBf p) = renderOps p := by
  simp only [Langlib.Brainloller.bfCommands, renderBf, String.toList_ofList]
  exact List.filter_eq_self.mpr (fun c hc => rgbOfCmd_isSome p c hc)

/-! ## Composing what is proved -/

/-- **Everything except the pixel walk.** If the walk over an image
recovers the characters of a rendered program, then decoding that image
yields exactly that program. -/
theorem decodeProg_of_decode {img : Image} {p : Prog}
    (h : Langlib.Brainloller.decode img = .ok (renderBf p)) :
    Langlib.Brainloller.decodeProg img = .ok p := by
  simp only [Langlib.Brainloller.decodeProg, h, bind, Except.bind]
  exact parse_renderBf p

/-- The colour table round-trips on the eight commands: a painted command
reads back as itself. (This is what makes step 1 of the round trip a
statement about the *walk* alone.) -/
theorem colour_roundTrip : ∀ c ∈ ['>', '<', '+', '-', '.', ',', '[', ']'],
    (Langlib.Brainloller.rgbOfCmd c).map Langlib.Brainloller.instrOfRgb
      = some (.cmd c) := by
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end Langlib.Computability.BrainlollerSyntax

namespace Langlib.Computability

open Langlib.Common

/-- The tag type naming Brainloller for the shared computability
interface. -/
inductive BrainlollerLang : Type

/-- A Brainloller program is an image; `parse` is the PPM reader followed
by the pixel walk, exactly as `Langlib.Brainloller.run` does it, and the
program the walk yields is a brainfuck program. -/
instance : ProgLang BrainlollerLang where
  Prog := Langlib.Brainfuck.Prog
  parse := fun src => do
    let img ← Image.parsePpm src.toUTF8
    Langlib.Brainloller.decodeProg img
  run := Langlib.Brainfuck.evalProg {}

/-- **Brainloller is Turing complete.**

The witness is `brainfuckComplete`'s, unchanged: a decoded Brainloller
program is a `Langlib.Brainfuck.Prog` and it runs on the brainfuck
evaluator, so the compiler, the encodings and the simulation proof all
transfer definitionally. The Brainloller-specific content is the round
trip discussed in the module docstring.

The compiled program ignores its external input, because the URM input
vector is embedded by the compiler. -/
def brainlollerComplete : TuringComplete BrainlollerLang where
  compile := URMBrainfuck.compile
  encodeInput := URMBrainfuck.encodeInput
  decodeOutput := URMBrainfuck.decodeOutput
  simulates := fun P inputs result h =>
    URMBrainfuck.simulation P inputs result h (URMBrainfuck.encodeInput inputs)

/-- The compiled URM program, painted and read back, is the program the
simulation theorem is about, provided the pixel walk recovers the painted
characters. That proviso is the one link carried by test rather than by
proof; see the module docstring. -/
theorem decode_compile (P : Cslib.URM.Program) (inputs : List Nat)
    {img : Langlib.Common.Image}
    (h : Langlib.Brainloller.decode img
      = .ok (BrainlollerSyntax.renderBf (brainlollerComplete.compile P inputs))) :
    Langlib.Brainloller.decodeProg img = .ok (brainlollerComplete.compile P inputs) :=
  BrainlollerSyntax.decodeProg_of_decode h

end Langlib.Computability
