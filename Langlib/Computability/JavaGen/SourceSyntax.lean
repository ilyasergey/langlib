import Langlib.Computability.JavaGen.ParserProof
import Langlib.Computability.JavaGen.LexerProof
import Langlib.Computability.JavaGen.GeneratedTable

/-! # A source-text round trip for every well-named closed program

The token renderer and parser proofs compose at the loader's actual budgets.
Validation remains the ordinary `prepare`, already proved total for generated
tables. Whitespace is the only difference from the compact pretty-printer.
-/

namespace Langlib.Computability.JavaGen.Source
open Langlib.JavaGen Langlib.JavaGen.Parser

/-- The parser requires legal constructor spellings; scope and inheritance
checks belong to the subsequent validator. -/
def WellNamed (p : Program) : Prop :=
  (∀ d ∈ p.classes, validName d.name = true ∧
    ∀ b ∈ d.bases, ∀ n ∈ b.ctors, validName n = true) ∧
  (∀ n ∈ p.query.lhs, validName n = true) ∧
  (∀ n ∈ p.query.rhs, validName n = true)

theorem chainWords_lexical (names : List String) (terminal : String)
    (valid : ∀ n ∈ names, validName n = true) (last : Lexical terminal) :
    ∀ w ∈ chainWords names terminal, Lexical w := by
  induction names with
  | nil => simpa [chainWords] using last
  | cons n ns ih =>
    simp only [chainWords, List.forall_mem_append, List.forall_mem_cons]
    exact ⟨⟨⟨lexical_name n (valid n (by simp)), by decide⟩,
      ih (by intro m hm; exact valid m (by simp [hm]))⟩, by decide⟩

theorem templateWords_lexical (t : Template) (valid : ∀ n ∈ t.ctors, validName n = true) :
    ∀ w ∈ templateWords t, Lexical w :=
  chainWords_lexical t.ctors _ valid (by split <;> decide)

theorem moreWords_lexical (bases : List Template)
    (valid : ∀ b ∈ bases, ∀ n ∈ b.ctors, validName n = true) :
    ∀ w ∈ moreWords bases, Lexical w := by
  induction bases with
  | nil => simp [moreWords]
  | cons b bs ih =>
    simp only [moreWords, List.forall_mem_append, List.forall_mem_cons]
    exact ⟨⟨by decide, templateWords_lexical b (valid b (by simp))⟩,
      ih (by intro t ht; exact valid t (by simp [ht]))⟩

theorem baseWords_lexical (bases : List Template)
    (valid : ∀ b ∈ bases, ∀ n ∈ b.ctors, validName n = true) :
    ∀ w ∈ baseWords bases, Lexical w := by
  cases bases with
  | nil => simp [baseWords]
  | cons b bs =>
    simp only [baseWords, List.forall_mem_append, List.forall_mem_cons]
    exact ⟨⟨by decide, templateWords_lexical b (valid b (by simp))⟩,
      moreWords_lexical bs (by intro t ht; exact valid t (by simp [ht]))⟩

theorem declWords_lexical (d : Decl) (valid : validName d.name = true)
    (bases : ∀ b ∈ d.bases, ∀ n ∈ b.ctors, validName n = true) :
    ∀ w ∈ declWords d, Lexical w := by
  simp only [declWords, List.forall_mem_append, List.forall_mem_cons]
  exact ⟨⟨⟨by decide, lexical_name d.name valid, by decide, by decide, by decide⟩,
    baseWords_lexical d.bases bases⟩, by decide, by decide⟩

theorem programWords_lexical (p : Program) (valid : WellNamed p) :
    ∀ w ∈ programWords p, Lexical w := by
  have classes : ∀ w ∈ p.classes.flatMap declWords, Lexical w := by
    intro w hw
    obtain ⟨d, hd, hw⟩ := List.mem_flatMap.mp hw
    exact declWords_lexical d (valid.1 d hd).1 (valid.1 d hd).2 w hw
  simp only [programWords, List.forall_mem_append, List.forall_mem_cons]
  exact ⟨⟨⟨⟨⟨⟨⟨by decide, by decide, by decide⟩, classes⟩, by decide⟩,
    chainWords_lexical _ _ valid.2.1 (by decide)⟩, by decide⟩,
    chainWords_lexical _ _ valid.2.2 (by decide)⟩, by decide⟩

private theorem moreWords_size (bases : List Template) :
    bases.length ≤ (moreWords bases).length ∧
    ∀ b ∈ bases, b.ctors.length < (moreWords bases).length := by
  induction bases with
  | nil => simp [moreWords]
  | cons b bs ih =>
    simp only [moreWords, List.length_append, List.length_cons, List.length_nil,
      templateWords, chainWords_length]
    constructor
    · omega
    · intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · omega
      · have := ih.2 t ht; omega

private theorem baseWords_size (bases : List Template) :
    bases.length ≤ (baseWords bases).length ∧
    ∀ b ∈ bases, b.ctors.length < (baseWords bases).length := by
  have same : (baseWords bases).length = (moreWords bases).length := by
    cases bases <;> simp [baseWords, moreWords]
  simpa only [same] using moreWords_size bases

private theorem declWords_size (d : Decl) :
    0 < (declWords d).length ∧ d.bases.length < (declWords d).length ∧
    ∀ b ∈ d.bases, b.ctors.length < (declWords d).length := by
  have size := baseWords_size d.bases
  simp only [declWords, List.length_append, List.length_cons, List.length_nil]
  refine ⟨by omega, by omega, ?_⟩
  intro b hb
  have := size.2 b hb
  omega

private theorem classes_size (classes : List Decl) :
    classes.length ≤ (classes.flatMap declWords).length ∧
    ∀ d ∈ classes, (declWords d).length ≤ (classes.flatMap declWords).length := by
  induction classes with
  | nil => simp
  | cons d ds ih =>
    have positive := (declWords_size d).1
    simp only [List.length_cons, List.flatMap_cons, List.length_append]
    constructor
    · omega
    · intro e he
      rcases List.mem_cons.mp he with rfl | he
      · omega
      · have := ih.2 e he; omega

/-- The ordinary parser's token-count-plus-one budget covers every nested
type, superclass list and declaration list in the rendered program. -/
theorem programWords_fits (p : Program) (valid : WellNamed p) :
    (∀ d ∈ p.classes, DeclFits ((programWords p).length + 1) d) ∧
    p.classes.length < (programWords p).length + 1 ∧
    TemplateFits ((programWords p).length + 1) ⟨p.query.lhs, .zero⟩ ∧
    TemplateFits ((programWords p).length + 1) ⟨p.query.rhs, .zero⟩ := by
  have total : (programWords p).length = 8 + (p.classes.flatMap declWords).length +
      3 * p.query.lhs.length + 3 * p.query.rhs.length := by
    simp [programWords, chainWords_length]; omega
  have size := classes_size p.classes
  refine ⟨?_, by omega, ⟨valid.2.1, by simp only [total]; omega⟩,
    ⟨valid.2.2, by simp only [total]; omega⟩⟩
  intro d hd
  have ds := size.2 d hd
  have bs := declWords_size d
  refine ⟨(valid.1 d hd).1, ?_, by omega⟩
  intro b hb
  exact ⟨(valid.1 d hd).2 b hb, by have := bs.2.2 b hb; omega⟩

/-- A token-separated spelling of a closed program in ordinary JavaGen syntax.
The existing compact `Program.render` remains available independently. -/
def sourceText (p : Program) : String := tokenText (programWords p)

/-- The unmodified lexer and parser recover the entire closed source AST.
Both use exactly the budgets chosen by `parseSyntax`. -/
theorem parseSyntax_sourceText (p : Program) (closed : p.answerSide = none) (valid : WellNamed p) :
    parseSyntax (sourceText p) = .ok p := by
  obtain ⟨tokens, lexed, texts⟩ := lex_tokenText (programWords p) (programWords_lexical p valid)
  have length : tokens.length = (programWords p).length := by
    simpa using congrArg List.length texts
  obtain ⟨classes, count, left, right⟩ := programWords_fits p valid
  have parsed := parse_program p closed ((programWords p).length + 1) classes count left right tokens texts
  simp only [parseSyntax, sourceText, lexed, bind, Except.bind, length, parsed]
  rfl

end Langlib.Computability.JavaGen.Source
