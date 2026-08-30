import Langlib.Computability.Brainfuck
import Langlib.Languages.Ook
import Batteries.Tactic.OpenPrivate

/-!
# Ook! is Turing complete, and its syntax is a faithful skin on brainfuck

Ook! (David Morgan-Mar, 2001) is brainfuck with the eight commands spelled
as pairs of the words `Ook.`, `Ook?`, `Ook!`. The correspondence is exact,
so `Langlib.Ook.Prog` is a definitional abbreviation for
`Langlib.Brainfuck.Prog`, `Langlib.Ook.run` calls the brainfuck evaluator,
and `Langlib.Computability.URMBrainfuck.compile` is already a compiler from
the unlimited register machine into Ook!'s program type.

That makes `ookComplete` a re-labelling of `brainfuckComplete`: same
compiler, same input encoding, same output decoding, same simulation
theorem. What is genuinely new here is the **syntactic** half, the part
that says Ook! *source text* can carry those programs:

    parse_render : ∀ p, Langlib.Ook.parse (Langlib.Ook.render p) = .ok p

for every `p : Langlib.Brainfuck.Prog`, the compiled URM programs included.
It is proved by induction over the program, through the real
`Langlib.Ook.parse`: its character-level tokeniser and its pair-consuming
loop are both handled, so the theorem is about the shipped parser and not
about a model of it.

## The renderer is total, on purpose

`Langlib.Ook.render` used to lay its words out sixteen to a line with a
`private partial def chunks`, and Lean compiles a `partial def` to an
**opaque** constant: it has no equations, `rfl` cannot reduce it, and no
theorem can say anything about it. A proof therefore had to be about a
total re-implementation, with a test pinning the two together.

That is gone. `Langlib.Ook.render` is now spelled out character by
character (`spelled`, `renderPairs`, `wordsOf`, all in
`Langlib/Languages/Ook/Syntax.lean`), emitting exactly the same bytes, so
the round trip below is proved about the string the shipped renderer
actually returns, and about the literal output of
`Langlib/Languages/Turpentine/Compile/Ook.lean`. No bridging test is needed.

## The shape of the proof

`Langlib.Ook.parse` is two `for` loops over private state. Neither loop
body can be named from outside the module, so both are handled the same
way: the loop is stated over an *arbitrary* body function constrained by
hypotheses that say what it does on each input, and those hypotheses are
discharged by `rfl` against the real body when the generic lemma is
applied. `TokSpec` is that constraint for the tokeniser and `PairSpec` for
the pair loop. The position type and the token type stay abstract, which
is what lets the statement avoid the module's private `Pos` and `Tok`
entirely.

* `tokKey` runs the tokeniser over one word plus its separator at a time.
* `pairKey` runs the pair loop over one `Op` at a time, and is the place
  where `Ook! Ook?` / `Ook? Ook!` rebuild a `loop` node from the stack.
* `parse_render` composes them, having first shown that the token count
  is even (so the odd-Ook check passes) and that `pairUp` recovers exactly
  the word pairs the program spells.

## What is proved, and what is not

`ookComplete` says: every URM program that halts with `result` in register
0 is simulated by an Ook! program that halts with `result` bytes of output.
`parse_render` says: that program is the reading of a real Ook! file.
The two together are what "Ook! is Turing complete" means in this library.

Not proved, and not claimed:

* that Ook! computes every partial computable function. That step is the
  cited classical result (Shepherdson and Sturgis 1963); see
  `Langlib.Common.computes_of_turingComplete` for the honest
  statement of what does follow.
* anything about divergence. `simulates` constrains halting runs only.
* the other direction of the round trip, `render <$> parse s = s`, which
  is false as stated: parsing forgets line breaks, and Ook! sources need
  not use this renderer's layout.
-/

open private tokenize pairUp Tok Tok.word from Langlib.Languages.Ook.Parser

namespace Langlib.Computability.OokSyntax

open Langlib.Brainfuck (Op Prog)
open Langlib.Ook (Word opWords lastChar wordChars wordsOf spelled renderPairs)

/-! ## Facts about the renderer

`lastChar`, `wordChars`, `wordsOf`, `spelled` and `renderPairs` are the
shipped definitions from `Langlib.Ook`; this section proves what the
round-trip argument needs about them. -/

theorem push_wordChars (w : Word) :
    ((("".push 'O').push 'o').push 'k').push (lastChar w) = w.render := by
  cases w <;> rfl

theorem lastChar_not_ws (w : Word) : (lastChar w).isWhitespace = false := by
  cases w <;> rfl

theorem renderPairs_fst : ∀ (ws : List Word) (k : Nat),
    (renderPairs ws k).map Prod.fst = ws
  | [], _ => rfl
  | [_], _ => rfl
  | w :: w' :: ws, k => by
    simp only [renderPairs, List.map_cons]
    rw [renderPairs_fst (w' :: ws)]

theorem renderPairs_ws : ∀ (ws : List Word) (k : Nat) (x : Word × Char),
    x ∈ renderPairs ws k → x.2.isWhitespace = true
  | [], _, _, h => by simp [renderPairs] at h
  | [_], _, x, h => by
    simp only [renderPairs, List.mem_singleton] at h
    subst h; rfl
  | _ :: w' :: ws, _, x, h => by
    simp only [renderPairs, List.mem_cons] at h
    rcases h with h | h
    · subst h; split <;> rfl
    · exact renderPairs_ws (w' :: ws) _ x h

/-! ## The tokeniser -/

/-- The tokeniser's loop state: the tokens read so far, the characters of
the word being read, the position that word started at, and the current
position. The position type is abstract, so the module's private `Pos`
never has to be named. -/
abbrev TSt (T P : Type) := Array T × String × P × P

/-- What the tokeniser's `for` body does. Positions are existentially
quantified because nothing downstream depends on them. -/
structure TokSpec {T P : Type} (wd : T → Word)
    (f : Char → TSt T P → Except String (ForInStep (TSt T P))) : Prop where
  /-- A non-space character extends the word being read. -/
  push : ∀ (c : Char), c.isWhitespace = false →
    ∀ (toks : Array T) (cur : String) (curPos pos : P), ∃ q r,
      f c (toks, cur, curPos, pos) = pure (.yield (toks, cur.push c, q, r))
  /-- A space after a complete word emits that word as a token. -/
  flush : ∀ (c : Char), c.isWhitespace = true →
    ∀ (toks : Array T) (w : Word) (curPos pos : P), ∃ t q r,
      f c (toks, w.render, curPos, pos) = pure (.yield (toks.push t, "", q, r)) ∧
      wd t = w

variable {T P : Type} {wd : T → Word}
  {f : Char → TSt T P → Except String (ForInStep (TSt T P))}

theorem step_push (hs : TokSpec wd f) (c : Char) (hc : c.isWhitespace = false)
    (toks : Array T) (cur : String) (curPos pos : P) (rest : List Char) :
    ∃ q r, forIn (c :: rest) (toks, cur, curPos, pos) f
         = forIn rest (toks, cur.push c, q, r) f := by
  obtain ⟨q, r, h⟩ := hs.push c hc toks cur curPos pos
  exact ⟨q, r, by rw [List.forIn_cons, h]; rfl⟩

theorem step_flush (hs : TokSpec wd f) (c : Char) (hc : c.isWhitespace = true)
    (toks : Array T) (w : Word) (curPos pos : P) (rest : List Char) :
    ∃ t q r, wd t = w ∧ forIn (c :: rest) (toks, w.render, curPos, pos) f
         = forIn rest (toks.push t, "", q, r) f := by
  obtain ⟨t, q, r, h, hw⟩ := hs.flush c hc toks w curPos pos
  exact ⟨t, q, r, hw, by rw [List.forIn_cons, h]; rfl⟩

/-- The tokeniser reads a rendered word list back as tokens spelling
exactly those words. -/
theorem tokKey (hs : TokSpec wd f) :
    ∀ (l : List (Word × Char)), (∀ x ∈ l, x.2.isWhitespace = true) →
    ∀ (rest : List Char) (toks : Array T) (curPos pos : P),
      ∃ (ts : Array T) (q r : P),
        ts.toList.map wd = toks.toList.map wd ++ l.map Prod.fst ∧
        forIn (spelled l ++ rest) (toks, "", curPos, pos) f
          = forIn rest (ts, "", q, r) f
  | [], _, rest, toks, curPos, pos => ⟨toks, curPos, pos, by simp, by simp [spelled]⟩
  | (w, c) :: t, hws, rest, toks, curPos, pos => by
    have hc : c.isWhitespace = true := hws (w, c) (by simp)
    have hrest : ∀ x ∈ t, x.2.isWhitespace = true := fun x hx => hws x (by simp [hx])
    have hsp : spelled ((w, c) :: t) ++ rest
        = 'O' :: 'o' :: 'k' :: lastChar w :: c :: (spelled t ++ rest) := by
      simp [spelled, wordChars]
    rw [hsp]
    obtain ⟨q1, r1, h1⟩ := step_push hs 'O' rfl toks "" curPos pos
      ('o' :: 'k' :: lastChar w :: c :: (spelled t ++ rest))
    obtain ⟨q2, r2, h2⟩ := step_push hs 'o' rfl toks ("".push 'O') q1 r1
      ('k' :: lastChar w :: c :: (spelled t ++ rest))
    obtain ⟨q3, r3, h3⟩ := step_push hs 'k' rfl toks (("".push 'O').push 'o') q2 r2
      (lastChar w :: c :: (spelled t ++ rest))
    obtain ⟨q4, r4, h4⟩ := step_push hs (lastChar w) (lastChar_not_ws w) toks
      ((("".push 'O').push 'o').push 'k') q3 r3 (c :: (spelled t ++ rest))
    rw [h1, h2, h3, h4, push_wordChars w]
    obtain ⟨tk, q5, r5, hw5, h5⟩ := step_flush hs c hc toks w q4 r4 (spelled t ++ rest)
    rw [h5]
    obtain ⟨ts, q, r, hts, h⟩ := tokKey hs t hrest rest (toks.push tk) q5 r5
    exact ⟨ts, q, r, by simp [hts, hw5], h⟩

theorem tokenize_generic (wd : T → Word)
    (f : Char → TSt T P → Except String (ForInStep (TSt T P)))
    (fin : TSt T P → Except String (Array T))
    (hs : TokSpec wd f)
    (hfin : ∀ (toks : Array T) (curPos pos : P),
      fin (toks, "", curPos, pos) = .ok toks)
    (l : List (Word × Char)) (hws : ∀ x ∈ l, x.2.isWhitespace = true)
    (curPos0 pos0 : P) :
    ∃ ts : Array T, ts.toList.map wd = l.map Prod.fst ∧
      (do
        let s ← forIn (spelled l) ((#[] : Array T), "", curPos0, pos0) f
        fin s) = .ok ts := by
  obtain ⟨ts, q, r, hts, h⟩ := tokKey hs l hws [] #[] curPos0 pos0
  refine ⟨ts, by simpa using hts, ?_⟩
  rw [show spelled l = spelled l ++ ([] : List Char) by simp, h]
  simp only [List.forIn_nil]
  show fin (ts, "", q, r) = _
  exact hfin ts q r

/-- Tokenising rendered source gives back exactly the program's words. -/
theorem tokenize_render (p : Prog) :
    ∃ ts : Array Tok, ts.toList.map Tok.word = wordsOf p ∧
      tokenize (Langlib.Ook.render p) = .ok ts := by
  have h : ∃ ts : Array Tok,
      ts.toList.map Tok.word = (renderPairs (wordsOf p) 0).map Prod.fst ∧
      tokenize (Langlib.Ook.render p) = .ok ts := by
    unfold tokenize
    simp only [Langlib.Ook.render, String.toList_ofList]
    refine tokenize_generic Tok.word _ _ ?_ ?_ _ (renderPairs_ws _ _) _ _
    · constructor
      · intro c hc toks cur curPos pos
        rw [if_neg (by simp [hc])]
        split <;> exact ⟨_, _, rfl⟩
      · intro c hc toks w curPos pos
        rw [if_pos hc]
        cases w <;> exact ⟨_, _, _, rfl, rfl⟩
    · intro toks curPos pos; rfl
  simpa [renderPairs_fst] using h

/-! ## Word pairs -/

/-- The word pairs one command spells. -/
def opPairs : Op → List (Word × Word)
  | .right => [(.dot, .quest)]
  | .left => [(.quest, .dot)]
  | .inc => [(.dot, .dot)]
  | .dec => [(.bang, .bang)]
  | .input => [(.dot, .bang)]
  | .output => [(.bang, .dot)]
  | .loop body => (.bang, .quest) :: (body.flatMap opPairs ++ [(.quest, .bang)])

def progPairs (p : Prog) : List (Word × Word) := p.flatMap opPairs

def flat (ps : List (Word × Word)) : List Word := ps.flatMap (fun x => [x.1, x.2])

theorem flat_append (a b : List (Word × Word)) :
    flat (a ++ b) = flat a ++ flat b := by simp [flat]

theorem wordsOf_eq : ∀ (p : Prog), wordsOf p = flat (progPairs p)
  | [] => rfl
  | op :: t => by
    simp only [wordsOf, progPairs, List.flatMap_cons, flat_append]
    rw [show t.flatMap opWords = flat (t.flatMap opPairs) from wordsOf_eq t]
    congr 1
    cases op with
    | loop b =>
      simp only [Langlib.Ook.opWords, opPairs, flat, List.flatMap_cons,
        List.flatMap_append, List.flatMap_nil, List.nil_append, List.cons_append]
      rw [show b.flatMap opWords = flat (b.flatMap opPairs) from wordsOf_eq b]
      simp [flat]
    | _ => simp [Langlib.Ook.opWords, opPairs, flat]
  termination_by p => sizeOf p

theorem flat_length (ps : List (Word × Word)) :
    (flat ps).length = 2 * ps.length := by
  induction ps with
  | nil => rfl
  | cons _ t ih => simp [flat, List.flatMap_cons] at *; omega

theorem map_eq_append {α β : Type} (g : α → β) :
    ∀ (l : List α) (b c : List β), l.map g = b ++ c →
      ∃ l1 l2, l = l1 ++ l2 ∧ l1.map g = b ∧ l2.map g = c
  | l, [], c, h => ⟨[], l, by simp, rfl, by simpa using h⟩
  | [], (_ :: _), _, h => by simp at h
  | (a :: l), (_ :: xs), c, h => by
    simp only [List.map_cons, List.cons_append, List.cons.injEq] at h
    obtain ⟨l1, l2, hl, h1, h2⟩ := map_eq_append g l xs c h.2
    exact ⟨a :: l1, l2, by simp [hl], by simp [h1, h.1], h2⟩

/-- Every token is consumed in a pair, and the pairs spell the program. -/
theorem pairUp_spec : ∀ (l : List Tok) (ps : List (Word × Word)),
    l.map Tok.word = flat ps →
      (pairUp l).map (fun x => (Tok.word x.1, Tok.word x.2)) = ps
  | l, [], h => by
    have hl : l = [] := by
      cases l with
      | nil => rfl
      | cons _ _ => simp [flat] at h
    subst hl; simp [pairUp]
  | l, (_, _) :: ps, h => by
    match l, h with
    | x :: y :: l', h =>
      simp only [List.map_cons, flat, List.flatMap_cons, List.cons_append,
        List.nil_append, List.cons.injEq] at h
      rw [show pairUp (x :: y :: l') = (x, y) :: pairUp l' from rfl]
      simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq]
      refine ⟨⟨h.1, h.2.1⟩, pairUp_spec l' ps ?_⟩
      simpa [flat] using h.2.2

/-! ## The pair loop -/

/-- The pair loop's state: the commands of the innermost program so far
(reversed) and the stack of enclosing programs, each tagged with the token
that opened it. -/
abbrev PSt (T : Type) := List Op × List (T × List Op)

/-- What the pair loop's `for` body does, keyed on the two words. -/
structure PairSpec {T : Type} (wd : T → Word)
    (g : (T × T) → PSt T → Except String (ForInStep (PSt T))) : Prop where
  right : ∀ (a b : T) cur stack, wd a = .dot → wd b = .quest →
    g (a, b) (cur, stack) = pure (.yield (Op.right :: cur, stack))
  left : ∀ (a b : T) cur stack, wd a = .quest → wd b = .dot →
    g (a, b) (cur, stack) = pure (.yield (Op.left :: cur, stack))
  inc : ∀ (a b : T) cur stack, wd a = .dot → wd b = .dot →
    g (a, b) (cur, stack) = pure (.yield (Op.inc :: cur, stack))
  dec : ∀ (a b : T) cur stack, wd a = .bang → wd b = .bang →
    g (a, b) (cur, stack) = pure (.yield (Op.dec :: cur, stack))
  output : ∀ (a b : T) cur stack, wd a = .bang → wd b = .dot →
    g (a, b) (cur, stack) = pure (.yield (Op.output :: cur, stack))
  input : ∀ (a b : T) cur stack, wd a = .dot → wd b = .bang →
    g (a, b) (cur, stack) = pure (.yield (Op.input :: cur, stack))
  open_ : ∀ (a b : T) cur stack, wd a = .bang → wd b = .quest →
    g (a, b) (cur, stack) = pure (.yield ([], (a, cur) :: stack))
  close : ∀ (a b : T) cur (o : T) outer stack, wd a = .quest → wd b = .bang →
    g (a, b) (cur, (o, outer) :: stack)
      = pure (.yield (Op.loop cur.reverse :: outer, stack))

/-- The pair loop rebuilds the program, one command at a time, with `loop`
nodes assembled from the stack. -/
theorem pairKey {T : Type} (wd : T → Word)
    (g : (T × T) → PSt T → Except String (ForInStep (PSt T)))
    (hs : PairSpec wd g) :
    ∀ (p : Prog) (l lrest : List (T × T)) (cur : List Op)
      (stack : List (T × List Op)),
      l.map (fun x => (wd x.1, wd x.2)) = progPairs p →
      forIn (l ++ lrest) (cur, stack) g
        = forIn lrest (p.reverse ++ cur, stack) g
  | [], l, lrest, cur, stack, h => by
    have hl : l = [] := by
      cases l with
      | nil => rfl
      | cons _ _ => simp [progPairs] at h
    subst hl; simp
  | op :: t, l, lrest, cur, stack, h => by
    have hsp : progPairs (op :: t) = opPairs op ++ progPairs t := by
      simp [progPairs]
    rw [hsp] at h
    obtain ⟨l1, l2, rfl, h1, h2⟩ := map_eq_append _ l _ _ h
    rw [List.append_assoc]
    cases op with
    | loop b =>
      obtain ⟨x, m, rfl⟩ : ∃ x m, l1 = x :: m := by
        cases l1 with
        | nil => simp [opPairs] at h1
        | cons a t' => exact ⟨a, t', rfl⟩
      simp only [List.map_cons, opPairs, List.cons.injEq, Prod.mk.injEq] at h1
      obtain ⟨hx, hm⟩ := h1
      rw [show b.flatMap opPairs = progPairs b from rfl] at hm
      obtain ⟨m1, m2, rfl, hm1, hm2⟩ := map_eq_append _ m _ _ hm
      obtain ⟨y, rfl⟩ : ∃ y, m2 = [y] := by
        cases m2 with
        | nil => simp at hm2
        | cons a t' =>
          cases t' with
          | nil => exact ⟨a, rfl⟩
          | cons _ _ => simp at hm2
      simp only [List.map_cons, List.map_nil, List.cons.injEq, Prod.mk.injEq] at hm2
      obtain ⟨x1, x2⟩ := x
      obtain ⟨y1, y2⟩ := y
      rw [List.cons_append, List.forIn_cons, hs.open_ x1 x2 cur stack hx.1 hx.2]
      show forIn ((m1 ++ [(y1, y2)]) ++ (l2 ++ lrest))
        (([] : List Op), (x1, cur) :: stack) g = _
      rw [List.append_assoc]
      rw [pairKey wd g hs b m1 ([(y1, y2)] ++ (l2 ++ lrest)) [] ((x1, cur) :: stack) hm1]
      rw [List.singleton_append, List.forIn_cons,
        hs.close y1 y2 (b.reverse ++ []) x1 cur stack hm2.1.1 hm2.1.2]
      show forIn (l2 ++ lrest)
        (Op.loop (b.reverse ++ ([] : List Op)).reverse :: cur, stack) g = _
      simp only [List.append_nil, List.reverse_reverse]
      rw [pairKey wd g hs t l2 lrest (Op.loop b :: cur) stack h2]
      simp
    | inc =>
      obtain ⟨x, rfl⟩ : ∃ x, l1 = [x] := by
        cases l1 with
        | nil => simp [opPairs] at h1
        | cons a t' =>
          cases t' with
          | nil => exact ⟨a, rfl⟩
          | cons _ _ => simp [opPairs] at h1
      simp only [List.map_cons, List.map_nil, opPairs, List.cons.injEq,
        Prod.mk.injEq] at h1
      obtain ⟨x1, x2⟩ := x
      rw [List.cons_append, List.forIn_cons, hs.inc x1 x2 cur stack h1.1.1 h1.1.2]
      show forIn (l2 ++ lrest) (Op.inc :: cur, stack) g = _
      rw [pairKey wd g hs t l2 lrest (Op.inc :: cur) stack h2]
      simp
    | dec =>
      obtain ⟨x, rfl⟩ : ∃ x, l1 = [x] := by
        cases l1 with
        | nil => simp [opPairs] at h1
        | cons a t' =>
          cases t' with
          | nil => exact ⟨a, rfl⟩
          | cons _ _ => simp [opPairs] at h1
      simp only [List.map_cons, List.map_nil, opPairs, List.cons.injEq,
        Prod.mk.injEq] at h1
      obtain ⟨x1, x2⟩ := x
      rw [List.cons_append, List.forIn_cons, hs.dec x1 x2 cur stack h1.1.1 h1.1.2]
      show forIn (l2 ++ lrest) (Op.dec :: cur, stack) g = _
      rw [pairKey wd g hs t l2 lrest (Op.dec :: cur) stack h2]
      simp
    | right =>
      obtain ⟨x, rfl⟩ : ∃ x, l1 = [x] := by
        cases l1 with
        | nil => simp [opPairs] at h1
        | cons a t' =>
          cases t' with
          | nil => exact ⟨a, rfl⟩
          | cons _ _ => simp [opPairs] at h1
      simp only [List.map_cons, List.map_nil, opPairs, List.cons.injEq,
        Prod.mk.injEq] at h1
      obtain ⟨x1, x2⟩ := x
      rw [List.cons_append, List.forIn_cons, hs.right x1 x2 cur stack h1.1.1 h1.1.2]
      show forIn (l2 ++ lrest) (Op.right :: cur, stack) g = _
      rw [pairKey wd g hs t l2 lrest (Op.right :: cur) stack h2]
      simp
    | left =>
      obtain ⟨x, rfl⟩ : ∃ x, l1 = [x] := by
        cases l1 with
        | nil => simp [opPairs] at h1
        | cons a t' =>
          cases t' with
          | nil => exact ⟨a, rfl⟩
          | cons _ _ => simp [opPairs] at h1
      simp only [List.map_cons, List.map_nil, opPairs, List.cons.injEq,
        Prod.mk.injEq] at h1
      obtain ⟨x1, x2⟩ := x
      rw [List.cons_append, List.forIn_cons, hs.left x1 x2 cur stack h1.1.1 h1.1.2]
      show forIn (l2 ++ lrest) (Op.left :: cur, stack) g = _
      rw [pairKey wd g hs t l2 lrest (Op.left :: cur) stack h2]
      simp
    | output =>
      obtain ⟨x, rfl⟩ : ∃ x, l1 = [x] := by
        cases l1 with
        | nil => simp [opPairs] at h1
        | cons a t' =>
          cases t' with
          | nil => exact ⟨a, rfl⟩
          | cons _ _ => simp [opPairs] at h1
      simp only [List.map_cons, List.map_nil, opPairs, List.cons.injEq,
        Prod.mk.injEq] at h1
      obtain ⟨x1, x2⟩ := x
      rw [List.cons_append, List.forIn_cons, hs.output x1 x2 cur stack h1.1.1 h1.1.2]
      show forIn (l2 ++ lrest) (Op.output :: cur, stack) g = _
      rw [pairKey wd g hs t l2 lrest (Op.output :: cur) stack h2]
      simp
    | input =>
      obtain ⟨x, rfl⟩ : ∃ x, l1 = [x] := by
        cases l1 with
        | nil => simp [opPairs] at h1
        | cons a t' =>
          cases t' with
          | nil => exact ⟨a, rfl⟩
          | cons _ _ => simp [opPairs] at h1
      simp only [List.map_cons, List.map_nil, opPairs, List.cons.injEq,
        Prod.mk.injEq] at h1
      obtain ⟨x1, x2⟩ := x
      rw [List.cons_append, List.forIn_cons, hs.input x1 x2 cur stack h1.1.1 h1.1.2]
      show forIn (l2 ++ lrest) (Op.input :: cur, stack) g = _
      rw [pairKey wd g hs t l2 lrest (Op.input :: cur) stack h2]
      simp
  termination_by p => sizeOf p

theorem pairFinal {T : Type} (wd : T → Word)
    (g : (T × T) → PSt T → Except String (ForInStep (PSt T)))
    (fin : PSt T → Except String Prog)
    (hs : PairSpec wd g)
    (hfin : ∀ (cur : List Op), fin (cur, []) = .ok cur.reverse)
    (p : Prog) (l : List (T × T))
    (h : l.map (fun x => (wd x.1, wd x.2)) = progPairs p) :
    (do
      let s ← forIn l (([] : List Op), ([] : List (T × List Op))) g
      fin s) = .ok p := by
  have hk := pairKey wd g hs p l [] [] [] h
  simp only [List.append_nil, List.forIn_nil] at hk
  rw [hk]
  show fin (p.reverse, []) = _
  rw [hfin]; simp

theorem ok_bind {α β : Type} (a : α) (f : α → Except String β) :
    (Except.ok a : Except String α) >>= f = f a := rfl

/-! ## The isomorphism -/

/-- **Ook! source is a faithful encoding of brainfuck programs.** Parsing
the rendering of any program gives that program back. -/
theorem parse_render (p : Prog) :
    Langlib.Ook.parse (Langlib.Ook.render p) = .ok p := by
  obtain ⟨ts, hts, htok⟩ := tokenize_render p
  have hlen : ts.size = 2 * (progPairs p).length := by
    have h := congrArg List.length hts
    simp only [List.length_map, Array.length_toList] at h
    rw [h, wordsOf_eq, flat_length]
  have hodd : (ts.size % 2 == 1) = false := by simp [hlen, Nat.mul_mod_right]
  have hpairs : (pairUp ts.toList).map (fun x => (Tok.word x.1, Tok.word x.2))
      = progPairs p := by
    refine pairUp_spec _ _ ?_
    rw [hts, wordsOf_eq]
  unfold Langlib.Ook.parse
  rw [htok, ok_bind, if_neg (by simp [hodd])]
  refine pairFinal Tok.word _ _ ?_ ?_ p _ hpairs
  · constructor <;> (intros; simp_all)
  · intro _; rfl

end Langlib.Computability.OokSyntax

namespace Langlib.Computability

open Langlib.Common

/-- The tag type naming Ook! for the shared computability interface. -/
inductive OokLang : Type

instance : ProgLang OokLang where
  Prog := Langlib.Ook.Prog
  parse := Langlib.Ook.parse
  run := Langlib.Brainfuck.evalProg {}

/-- **Ook! is Turing complete.**

The witness is `brainfuckComplete`'s, unchanged: `Langlib.Ook.Prog` is
`Langlib.Brainfuck.Prog` and `Langlib.Ook.run` is the brainfuck
evaluator, so the compiler, the encodings and the simulation proof all
transfer definitionally. The Ook!-specific content is
`OokSyntax.parse_render`, which says the compiled program can be
written down as Ook! text and read back unchanged.

The compiled program ignores its external input, because the URM input
vector is embedded by the compiler. -/
def ookComplete : TuringComplete OokLang where
  compile := URMBrainfuck.compile
  encodeInput := URMBrainfuck.encodeInput
  decodeOutput := URMBrainfuck.decodeOutput
  simulates := fun P inputs result h =>
    URMBrainfuck.simulation P inputs result h (URMBrainfuck.encodeInput inputs)

/-- The compiled URM program, written as Ook! source, parses back to the
program the simulation theorem is about. This is `parse_render`
instantiated at the compiler's output; it is what makes `ookComplete` a
claim about the *language* rather than about a shared syntax tree. -/
theorem parse_render_compile (P : Cslib.URM.Program) (inputs : List Nat) :
    Langlib.Ook.parse (Langlib.Ook.render (ookComplete.compile P inputs))
      = .ok (ookComplete.compile P inputs) :=
  OokSyntax.parse_render _

end Langlib.Computability
