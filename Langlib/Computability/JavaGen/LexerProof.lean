import Langlib.Computability.JavaGen.Names
import Batteries.Tactic.OpenPrivate

/-! # Source realization through the ordinary lexer

The proof renderer separates tokens with spaces. It emits the existing
JavaGen syntax; no loader extension or hidden prepared state is involved.
-/

open private lexGo from Langlib.Languages.JavaGen.Parser

namespace Langlib.Computability.JavaGen.Source
open Langlib.JavaGen Langlib.JavaGen.Parser

/-- Emit ordinary source with an explicit separator after each token. -/
def tokenText (words : List String) : String :=
  String.join (words.map (fun word => word ++ " "))

private theorem start_ne {c d : Char} (start : identStart c = true) (bad : identStart d = false) :
    c ≠ d := by
  intro eq
  simp [eq, bad] at start

private theorem lex_identifier (c : Char) (cs rest : List Char)
    (start : identStart c = true) (letters : cs.all identRest = true)
    (fuel line column : Nat) (acc : List Token) :
    lexGo (fuel + 2) ((c :: cs) ++ ' ' :: rest) line column acc =
      lexGo fuel rest line (column + (c :: cs).length + 1)
        (⟨String.ofList (c :: cs), line, column⟩ :: acc) := by
  have hn := start_ne start (d := '\n') (by decide)
  have hs := start_ne start (d := '/') (by decide)
  have hl := start_ne start (d := '<') (by decide)
  have hsp := start_ne start (d := ' ') (by decide)
  have ht := start_ne start (d := '\t') (by decide)
  have hr := start_ne start (d := '\r') (by decide)
  have take : (cs ++ ' ' :: rest).takeWhile identRest = cs := by
    rw [List.takeWhile_append_of_pos (by simpa using letters)]
    simp [identRest, identStart]
  have drop : (cs ++ ' ' :: rest).dropWhile identRest = ' ' :: rest := by
    rw [List.dropWhile_append_of_pos (by simpa using letters)]
    simp [identRest, identStart]
  simp [lexGo, hs, hl, hsp, ht, hr, start, take, drop]

/-- Identifier spelling without the constructor-name reserved-word check:
keywords and the fixed binder are identifiers for lexing purposes. -/
def identifier (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => identStart c && cs.all identRest

def Lexical (s : String) : Prop :=
  identifier s = true ∨ s ∈ ["<", ">", "{", "}", ",", ";", "<:"]

instance (s : String) : Decidable (Lexical s) := inferInstanceAs (Decidable (_ ∨ _))

theorem lexical_name (s : String) (valid : validName s = true) : Lexical s := by
  left
  unfold validName at valid
  unfold identifier
  split at valid
  · contradiction
  · simp_all

theorem lexical_nonempty {s : String} (valid : Lexical s) : 0 < s.length := by
  rcases valid with ident | symbol
  · unfold identifier at ident
    split at ident
    · contradiction
    · simp [String.length, *]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at symbol
    rcases symbol with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Every emitted token, including `<:`, consumes exactly one lexer step,
followed by one step for its separating space. -/
private theorem lex_token (s : String) (valid : Lexical s) (rest : List Char)
    (fuel line column : Nat) (acc : List Token) :
    lexGo (fuel + 2) (s.toList ++ ' ' :: rest) line column acc =
      lexGo fuel rest line (column + s.length + 1) (⟨s, line, column⟩ :: acc) := by
  rcases valid with ident | symbol
  · unfold identifier at ident
    split at ident
    · contradiction
    · rename_i c cs spelling
      have eq : s = String.ofList (c :: cs) := by
        apply String.toList_inj.mp
        simpa using spelling
      simp only [Bool.and_eq_true] at ident
      simpa only [eq, String.toList_ofList, String.length_ofList] using
        lex_identifier c cs rest ident.1 ident.2 fuel line column acc
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at symbol
    rcases symbol with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

@[simp] theorem tokenText_nil : tokenText [] = "" := rfl

@[simp] theorem tokenText_cons (s : String) (ss : List String) :
    tokenText (s :: ss) = (s ++ " ") ++ tokenText ss := by simp [tokenText]

/-- The real source-length budget suffices, while all token coordinates are
retained by the lexer and ignored only in the statement of spelling. -/
private theorem lex_words (words : List String) (valid : ∀ s ∈ words, Lexical s)
    (fuel : Nat) (enough : (tokenText words).length < fuel)
    (line column : Nat) (acc : List Token) :
    ∃ tokens, lexGo fuel (tokenText words).toList line column acc = .ok (acc.reverse ++ tokens) ∧
      tokens.map Token.text = words := by
  induction words generalizing fuel column acc with
  | nil =>
    cases fuel with
    | zero => simp at enough
    | succ fuel => exact ⟨[], by simp [lexGo]; rfl, rfl⟩
  | cons s ss ih =>
    have vs := valid s (by simp)
    have nonempty := lexical_nonempty vs
    simp only [tokenText_cons, String.length_append] at enough
    cases fuel with
    | zero => omega
    | succ fuel =>
      cases fuel with
      | zero => have : " ".length = 1 := rfl; omega
      | succ fuel =>
        have room : (tokenText ss).length < fuel := by have : " ".length = 1 := rfl; omega
        obtain ⟨tokens, success, texts⟩ := ih (by intro t ht; exact valid t (by simp [ht])) fuel room
          (column + s.length + 1) (⟨s, line, column⟩ :: acc)
        refine ⟨⟨s, line, column⟩ :: tokens, ?_, by simp [texts]⟩
        simpa only [tokenText_cons, String.toList_append, List.append_assoc,
          show " ".toList = [' '] from rfl, List.singleton_append,
          lex_token s vs _ fuel line column acc, List.reverse_cons, List.append_assoc,
          List.singleton_append] using success

/-- Token-separated rendering is accepted by the unmodified lexer with its
actual source-length guard, for every valid token sequence. -/
theorem lex_tokenText (words : List String) (valid : ∀ s ∈ words, Lexical s) :
    ∃ tokens, Parser.lex (tokenText words) = .ok tokens ∧ tokens.map Token.text = words := by
  obtain ⟨tokens, success, texts⟩ := lex_words words valid ((tokenText words).length + 1)
    (by omega) 1 1 []
  exact ⟨tokens, success, texts⟩

end Langlib.Computability.JavaGen.Source
