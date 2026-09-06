import Langlib.Computability.JavaGen.Names
import Batteries.Tactic.OpenPrivate

/-! # Round trips through the ordinary token parser

Token coordinates remain arbitrary. The proofs use the executable parser's
own recursion budgets; none of these bounds concerns subtype execution.
-/

open private fail isNext take expect name type moreBases decl decls program
  from Langlib.Languages.JavaGen.Parser

namespace Langlib.Computability.JavaGen.Source
open Langlib.JavaGen Langlib.JavaGen.Parser

/-- A parser consumes exactly these token texts and leaves any suffix intact. -/
def Parses (p : P α) (words : List String) (value : α) : Prop :=
  ∀ tokens rest, tokens.map Token.text = words → p (tokens ++ rest) = .ok (value, rest)

private theorem split_texts {tokens : List Token} {a b : List String}
    (texts : tokens.map Token.text = a ++ b) :
    ∃ first second, tokens = first ++ second ∧
      first.map Token.text = a ∧ second.map Token.text = b := by
  exact List.map_eq_append_iff.mp texts

theorem Parses.pure (value : α) : Parses (pure value) [] value := by
  intro tokens rest texts
  have : tokens = [] := List.map_eq_nil_iff.mp texts
  subst tokens
  rfl

theorem Parses.bind {p : P α} {q : α → P β} {a b : List String} {x : α} {y : β}
    (first : Parses p a x) (second : Parses (q x) b y) : Parses (p >>= q) (a ++ b) y := by
  intro tokens rest texts
  obtain ⟨left, right, rfl, hl, hr⟩ := split_texts texts
  change (p ((left ++ right) ++ rest) >>= fun result => q result.1 result.2) = _
  rw [List.append_assoc, first left (right ++ rest) hl]
  exact second right rest hr

@[simp] private theorem get_tokens (ts : List Token) :
    (getThe (List Token) : P (List Token)) ts = .ok (ts, ts) := rfl

@[simp] private theorem state_get_tokens (ts : List Token) :
    (MonadStateOf.get : P (List Token)) ts = .ok (ts, ts) := rfl

@[simp] private theorem run_bind (p : P α) (q : α → P β) (ts : List Token) :
    (p >>= q) ts = (p ts >>= fun x => q x.1 x.2) := rfl

@[simp] private theorem run_pure (a : α) (ts : List Token) :
    (pure a : P α) ts = .ok (a, ts) := rfl

@[simp] private theorem ok_bind (a : α) (f : α → Except String β) :
    (Except.ok a >>= f) = f a := rfl

theorem parses_expect (s : String) : Parses (expect s) [s] () := by
  intro tokens rest texts
  rcases tokens with _ | ⟨t, tail⟩
  · simp at texts
  · have ht : t.text = s := by simpa using congrArg List.head? texts
    have tail : tail = [] := by simpa using congrArg List.tail texts
    subst tail
    simp [expect, isNext, take, ht, StateT.bind, StateT.pure, get, getThe, set,
      StateT.set, bind, pure, Except.bind, Except.pure]

theorem parses_name (s : String) (valid : validName s = true) : Parses name [s] s := by
  intro tokens rest texts
  rcases tokens with _ | ⟨t, tail⟩
  · simp at texts
  · have ht : t.text = s := by simpa using congrArg List.head? texts
    have tail : tail = [] := by simpa using congrArg List.tail texts
    subst tail
    simp [name, take, ht, valid, StateT.bind, StateT.pure, get, getThe, set,
      StateT.set, bind, pure, Except.bind, Except.pure]

/-- Tokens for one unary chain, with the terminal token explicit. -/
def chainWords : List String → String → List String
  | [], terminal => [terminal]
  | n :: ns, terminal => [n, "<"] ++ chainWords ns terminal ++ [">"]

@[simp] theorem chainWords_length (names : List String) (terminal : String) :
    (chainWords names terminal).length = 3 * names.length + 1 := by
  induction names <;> simp_all [chainWords]; omega

private theorem valid_not_reserved {s : String} (valid : validName s = true) : s ∉ reserved := by
  unfold validName at valid
  split at valid
  · contradiction
  · simp only [Bool.and_eq_true, Bool.not_eq_true'] at valid
    simpa using valid.2

/-- The parser accepts an arbitrary valid unary chain at a budget greater
than its constructor depth. Coordinates and the remaining tokens are free. -/
theorem parses_type (allowVar : Bool) (names : List String) (tail : Tail)
    (valid : ∀ n ∈ names, validName n = true) (allowed : tail = .var → allowVar = true)
    (fuel : Nat) (enough : names.length < fuel) :
    Parses (type allowVar fuel)
      (chainWords names (if tail = .var then "x" else "Z")) ⟨names, tail⟩ := by
  induction names generalizing fuel with
  | nil =>
    cases fuel with
    | zero => simp at enough
    | succ fuel =>
      intro tokens rest texts
      cases tokens with
      | nil => simp [chainWords] at texts
      | cons t ts =>
        have ht : t.text = (if tail = .var then "x" else "Z") := by
          simpa [chainWords] using congrArg List.head? texts
        have empty : ts = [] := by simpa [chainWords] using congrArg List.tail texts
        subst ts
        cases tail <;>
          simp_all [type, isNext, expect, take, StateT.bind, StateT.pure, get, getThe, set,
            StateT.set, bind, pure, Except.bind, Except.pure]
  | cons n ns ih =>
    cases fuel with
    | zero => simp at enough
    | succ fuel =>
      have vn := valid n (by simp)
      have notReserved := valid_not_reserved vn
      have nz : n ≠ "Z" := by intro eq; exact notReserved (by simp [reserved, eq])
      have nx : n ≠ "x" := by intro eq; exact notReserved (by simp [reserved, eq])
      have na : n ≠ "answer" := by intro eq; exact notReserved (by simp [reserved, eq])
      have inner := ih (by intro name hn; exact valid name (by simp [hn])) fuel (by simpa using enough)
      have sequence : Parses (do
          let n ← name
          expect "<"
          let arg ← type allowVar fuel
          expect ">"
          pure (⟨n :: arg.ctors, arg.tail⟩ : Template))
          ([n] ++ (["<"] ++ (chainWords ns (if tail = .var then "x" else "Z") ++ ([">"] ++ []))))
          ⟨n :: ns, tail⟩ := by
        apply Parses.bind (parses_name n vn)
        apply Parses.bind (parses_expect "<")
        apply Parses.bind inner
        apply Parses.bind (parses_expect ">")
        exact Parses.pure _
      intro tokens rest texts
      cases tokens with
      | nil => simp [chainWords] at texts
      | cons t ts =>
        have ht : t.text = n := by simpa [chainWords] using congrArg List.head? texts
        have parsed := sequence (t :: ts) rest (by simpa [chainWords, List.append_assoc] using texts)
        simpa only [type, isNext, ht, nz, nx, na, beq_eq_false_iff_ne.mpr nz,
          beq_eq_false_iff_ne.mpr nx, beq_eq_false_iff_ne.mpr na,
          List.cons_append, StateT.bind, StateT.pure, get, getThe, state_get_tokens, bind,
          pure, Except.bind, Except.pure, List.head?_cons, Option.any_some, Bool.false_eq_true,
          ite_false] using parsed

def templateWords (t : Template) : List String :=
  chainWords t.ctors (if t.tail = .var then "x" else "Z")

def moreWords : List Template → List String
  | [] => []
  | t :: ts => [","] ++ templateWords t ++ moreWords ts

/-- Constructor-name validity and the depth bound needed for a superclass. -/
def TemplateFits (bound : Nat) (t : Template) : Prop :=
  (∀ n ∈ t.ctors, validName n = true) ∧ t.ctors.length < bound

private def moreThenOpen (bound fuel : Nat) : P (List Template) := do
  let bases ← moreBases bound fuel
  expect "{"
  pure bases

/-- The stopping brace is consumed explicitly, so the theorem places no
lookahead restriction on the arbitrary remaining suffix. -/
private theorem parses_moreThenOpen (bound : Nat) (bases : List Template)
    (valid : ∀ b ∈ bases, TemplateFits bound b) (fuel : Nat) (enough : bases.length < fuel) :
    Parses (moreThenOpen bound fuel) (moreWords bases ++ ["{"]) bases := by
  induction bases generalizing fuel with
  | nil =>
    cases fuel with
    | zero => simp at enough
    | succ fuel =>
      intro tokens rest texts
      cases tokens with
      | nil => simp [moreWords] at texts
      | cons t ts =>
        have ht : t.text = "{" := by simpa [moreWords] using congrArg List.head? texts
        have empty : ts = [] := by simpa [moreWords] using congrArg List.tail texts
        subst ts
        simp [moreThenOpen, moreBases, isNext, expect, take, ht, StateT.bind, StateT.pure,
          get, getThe, set, StateT.set, bind, pure, Except.bind, Except.pure]
  | cons b bs ih =>
    cases fuel with
    | zero => simp at enough
    | succ fuel =>
      have vb := valid b (by simp)
      have item := parses_type true b.ctors b.tail vb.1 (by simp) bound vb.2
      have inner := ih (by intro t ht; exact valid t (by simp [ht])) fuel (by simpa using enough)
      have sequence : Parses (do
          expect ","
          let b ← type true bound
          let bs ← moreThenOpen bound fuel
          pure (b :: bs))
          ([","] ++ (templateWords b ++ ((moreWords bs ++ ["{"]) ++ []))) (b :: bs) := by
        apply Parses.bind (parses_expect ",")
        apply Parses.bind item
        apply Parses.bind inner
        exact Parses.pure _
      intro tokens rest texts
      cases tokens with
      | nil => simp [moreWords] at texts
      | cons t ts =>
        have ht : t.text = "," := by simpa [moreWords] using congrArg List.head? texts
        have parsed := sequence (t :: ts) rest (by simpa [moreWords, List.append_assoc] using texts)
        simpa only [moreThenOpen, moreBases, isNext, ht, List.cons_append,
          run_bind, run_pure, get, getThe, get_tokens, state_get_tokens, ok_bind, bind_assoc,
          List.head?_cons, Option.any_some, beq_self_eq_true, ite_true] using parsed

def baseWords : List Template → List String
  | [] => []
  | b :: bs => ["extends"] ++ templateWords b ++ moreWords bs

def declWords (d : Decl) : List String :=
  ["interface", d.name, "<", "x", ">"] ++ baseWords d.bases ++ ["{", "}"]

private def declBody (bound : Nat) (n : String) : P Decl := do
  let bases ← if ← isNext "extends" then do
    expect "extends"
    let b ← type true bound
    let bs ← moreBases bound bound
    pure (b :: bs)
  else pure []
  expect "{"
  expect "}"
  pure ⟨n, bases⟩

private theorem parses_declBody (bound : Nat) (n : String) (bases : List Template)
    (valid : ∀ b ∈ bases, TemplateFits bound b) (enough : bases.length < bound) :
    Parses (declBody bound n) (baseWords bases ++ ["{", "}"]) ⟨n, bases⟩ := by
  cases bases with
  | nil =>
    have sequence : Parses (do expect "{"; expect "}"; pure (⟨n, []⟩ : Decl))
        (["{"] ++ (["}"] ++ [])) ⟨n, []⟩ := by
      apply Parses.bind (parses_expect "{")
      apply Parses.bind (parses_expect "}")
      exact Parses.pure _
    intro tokens rest texts
    cases tokens with
    | nil => simp [baseWords] at texts
    | cons t ts =>
      have ht : t.text = "{" := by simpa [baseWords] using congrArg List.head? texts
      have parsed := sequence (t :: ts) rest (by simpa [baseWords] using texts)
      simpa only [declBody, isNext, ht, List.cons_append, run_bind, run_pure,
        get, getThe, get_tokens, state_get_tokens, ok_bind, bind_assoc,
        List.head?_cons, Option.any_some, show ("{" == "extends") = false from rfl,
        Bool.false_eq_true, ite_false] using parsed
  | cons b bs =>
    have vb := valid b (by simp)
    have item := parses_type true b.ctors b.tail vb.1 (by simp) bound vb.2
    have more := parses_moreThenOpen bound bs
      (by intro t ht; exact valid t (by simp [ht])) bound (by simp_all; omega)
    have sequence : Parses (do
        expect "extends"
        let b ← type true bound
        let bs ← moreThenOpen bound bound
        expect "}"
        pure (⟨n, b :: bs⟩ : Decl))
        (["extends"] ++ (templateWords b ++ ((moreWords bs ++ ["{"]) ++ (["}"] ++ []))))
        ⟨n, b :: bs⟩ := by
      apply Parses.bind (parses_expect "extends")
      apply Parses.bind item
      apply Parses.bind more
      apply Parses.bind (parses_expect "}")
      exact Parses.pure _
    intro tokens rest texts
    cases tokens with
    | nil => simp [baseWords] at texts
    | cons t ts =>
      have ht : t.text = "extends" := by simpa [baseWords] using congrArg List.head? texts
      have parsed := sequence (t :: ts) rest (by simpa [baseWords, List.append_assoc] using texts)
      simpa only [declBody, moreThenOpen, isNext, ht, List.cons_append, run_bind, run_pure,
        get, getThe, get_tokens, state_get_tokens, ok_bind, bind_assoc,
        List.head?_cons, Option.any_some, beq_self_eq_true, ite_true] using parsed

def DeclFits (bound : Nat) (d : Decl) : Prop :=
  validName d.name = true ∧ (∀ b ∈ d.bases, TemplateFits bound b) ∧ d.bases.length < bound

/-- A full declaration round-trips, retaining superclass order. -/
theorem parses_decl (bound : Nat) (d : Decl) (valid : DeclFits bound d) :
    Parses (decl bound) (declWords d) d := by
  have body := parses_declBody bound d.name d.bases valid.2.1 valid.2.2
  have sequence : Parses (do
      expect "interface"
      let n ← name
      expect "<"
      expect "x"
      expect ">"
      declBody bound n)
      (["interface"] ++ ([d.name] ++ (["<"] ++ (["x"] ++ ([">"] ++
        (baseWords d.bases ++ ["{", "}"])))))) d := by
    apply Parses.bind (parses_expect "interface")
    apply Parses.bind (parses_name d.name valid.1)
    apply Parses.bind (parses_expect "<")
    apply Parses.bind (parses_expect "x")
    apply Parses.bind (parses_expect ">")
    exact body
  simpa only [decl, declBody, declWords, List.cons_append, List.nil_append,
    bind_assoc, pure_bind] using sequence

private def declsThenCheck (bound fuel : Nat) : P (List Decl) := do
  let ds ← decls bound fuel
  expect "check"
  pure ds

private theorem parses_declsThenCheck (bound : Nat) (classes : List Decl)
    (valid : ∀ d ∈ classes, DeclFits bound d) (fuel : Nat) (enough : classes.length < fuel) :
    Parses (declsThenCheck bound fuel) (classes.flatMap declWords ++ ["check"]) classes := by
  induction classes generalizing fuel with
  | nil =>
    cases fuel with
    | zero => simp at enough
    | succ fuel =>
      intro tokens rest texts
      cases tokens with
      | nil => simp at texts
      | cons t ts =>
        have ht : t.text = "check" := by simpa using congrArg List.head? texts
        have empty : ts = [] := by simpa using congrArg List.tail texts
        subst ts
        simp [declsThenCheck, decls, isNext, expect, take, ht, StateT.bind, StateT.pure,
          get, getThe, set, StateT.set, bind, pure, Except.bind, Except.pure]
  | cons d ds ih =>
    cases fuel with
    | zero => simp at enough
    | succ fuel =>
      have item := parses_decl bound d (valid d (by simp))
      have inner := ih (by intro t ht; exact valid t (by simp [ht])) fuel (by simpa using enough)
      have sequence : Parses (do
          let d ← decl bound
          let ds ← declsThenCheck bound fuel
          pure (d :: ds))
          (declWords d ++ ((ds.flatMap declWords ++ ["check"]) ++ [])) (d :: ds) := by
        apply Parses.bind item
        apply Parses.bind inner
        exact Parses.pure _
      intro tokens rest texts
      cases tokens with
      | nil => simp [declWords] at texts
      | cons t ts =>
        have ht : t.text = "interface" := by simpa [declWords] using congrArg List.head? texts
        have parsed := sequence (t :: ts) rest (by simpa [List.append_assoc] using texts)
        simpa only [declsThenCheck, decls, isNext, ht, List.cons_append,
          run_bind, run_pure, get, getThe, get_tokens, state_get_tokens, ok_bind, bind_assoc,
          List.head?_cons, Option.any_some, beq_self_eq_true, ite_true] using parsed

def programWords (p : Program) : List String :=
  ["zero", "Z", ";"] ++ p.classes.flatMap declWords ++ ["check"] ++
    chainWords p.query.lhs "Z" ++ ["<:"] ++ chainWords p.query.rhs "Z" ++ [";"]

private def programPrefix (bound : Nat) : P (List Decl × Template × Template) := do
  expect "zero"
  expect "Z"
  expect ";"
  let classes ← declsThenCheck bound bound
  let lhs ← type false bound
  expect "<:"
  let rhs ← type false bound
  expect ";"
  pure (classes, lhs, rhs)

private theorem parses_programPrefix (p : Program) (bound : Nat)
    (classes : ∀ d ∈ p.classes, DeclFits bound d) (count : p.classes.length < bound)
    (left : TemplateFits bound ⟨p.query.lhs, .zero⟩)
    (right : TemplateFits bound ⟨p.query.rhs, .zero⟩) :
    Parses (programPrefix bound) (programWords p)
      (p.classes, ⟨p.query.lhs, .zero⟩, ⟨p.query.rhs, .zero⟩) := by
  have ds := parses_declsThenCheck bound p.classes classes bound count
  have lhs := parses_type false p.query.lhs .zero left.1 (by simp) bound left.2
  have rhs := parses_type false p.query.rhs .zero right.1 (by simp) bound right.2
  unfold programPrefix programWords
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply Parses.bind (parses_expect "zero")
  apply Parses.bind (parses_expect "Z")
  apply Parses.bind (parses_expect ";")
  change Parses _ (p.classes.flatMap declWords ++ (["check"] ++
    (chainWords p.query.lhs "Z" ++ (["<:"] ++ (chainWords p.query.rhs "Z" ++ [";"]))))) _
  rw [← List.append_assoc (p.classes.flatMap declWords) ["check"]]
  apply Parses.bind ds
  apply Parses.bind lhs
  apply Parses.bind (parses_expect "<:")
  apply Parses.bind rhs
  simpa using Parses.bind (q := fun _ => pure _ ) (parses_expect ";") (Parses.pure _)

private def finish (parts : List Decl × Template × Template) : P Program := do
  let (classes, lhs, rhs) := parts
  unless (← get).isEmpty do fail "unexpected trailing token"
  if lhs.tail == .var && rhs.tail == .var then fail "only one answer hole is allowed"
  let answerSide := if lhs.tail == .var then some Side.lhs
    else if rhs.tail == .var then some Side.rhs else none
  pure { classes, query := ⟨lhs.ctors, rhs.ctors⟩, answerSide }

private theorem program_eq (bound : Nat) :
    program bound = (programPrefix bound >>= finish) := by
  simp only [program, programPrefix, finish, declsThenCheck, bind_assoc, pure_bind]

/-- Every well-named closed program with sufficient token budget is accepted
by the actual top-level parser, including its end-of-input check. -/
theorem parse_program (p : Program) (closed : p.answerSide = none) (bound : Nat)
    (classes : ∀ d ∈ p.classes, DeclFits bound d) (count : p.classes.length < bound)
    (left : TemplateFits bound ⟨p.query.lhs, .zero⟩)
    (right : TemplateFits bound ⟨p.query.rhs, .zero⟩)
    (tokens : List Token) (texts : tokens.map Token.text = programWords p) :
    program bound tokens = .ok (p, []) := by
  rw [program_eq, run_bind]
  have parsedPrefix := parses_programPrefix p bound classes count left right tokens [] texts
  simp only [List.append_nil] at parsedPrefix
  rw [parsedPrefix, ok_bind]
  have eq : (⟨p.classes, ⟨p.query.lhs, p.query.rhs⟩, none⟩ : Program) = p := by
    cases p with
    | mk classes query side => cases query; cases closed; rfl
  simpa [finish, get, getThe, StateT.bind, StateT.pure, bind, pure, Except.bind, Except.pure,
    show (Tail.zero == Tail.var) = false from rfl]
    using congrArg (fun p => (Except.ok (p, []) : Except String (Program × List Token))) eq

end Langlib.Computability.JavaGen.Source
