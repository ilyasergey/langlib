import Batteries.Tactic.OpenPrivate
import Langlib.Languages.Turpentine.Compile.Derived
import Langlib.Languages.Turpentine.Compile.Whitespace

/-!
# The hand-written Turpentine-to-Whitespace backend, proved correct

`Langlib/Languages/Turpentine/Compile/Derived.lean` builds verified Turpentine compilers by
composing `compileToURM` with a completeness witness. Those compilers are
correct by construction and nobody runs them. The compiler people run is the
hand-written backend in `Langlib/Languages/Turpentine/Compile/Whitespace.lean`, and
until now nothing was proved about it.

This file gives that backend a second `TurpentineCompiler WhitespaceLang`
inhabitant, `bespokeWhitespace`, so `Derived.agree` applies and the derived
compiler stops being an untested oracle for the hand-written one and becomes
a proved-equal one (`bespokeWhitespace_agrees_derived`).

## The covered fragment

The backend accepts all of Turpentine. This proof covers a sublanguage, and
`bespokeWhitespace.compile` rejects everything else, so the theorem's
hypothesis and the compiler's acceptance are the same predicate:

* declarations: scalar `int` and `bool` with no initialiser, names pairwise
  distinct, one of them `answer : int`;
* expressions: literals of either type (negative integers included),
  variables, `-` and `!`, and `+ - * == != < <= > >= && ||`;
* statements: `skip`, sequencing, assignment, `if`, `while`, `assert`.

`/` and `%` are left out (the backend's Euclidean correction branches on the
sign of the divisor, a separate arithmetic obligation), as are arrays and
every I/O statement. `docs/whitespace/compiler.md` records the reasoning.
Note what is *in*: subtraction, unary minus and negative integers, which the
certified URM fragment cannot express because a register holds a natural.
The two fragments are incomparable.

The unrestricted `Turpentine.Compile.Whitespace.compileSource`, which is what
`lake exe turpentine` runs, is untouched.

## Reaching the generator

`compileExpr`, `compileStmt` and the small emitters are `private` in the
backend, so this file opens them with Batteries' `open private`. That is
deliberate: the proof is about the code generator that ships, not about a
copy of it, and every equation it uses for those functions holds by `rfl`.

## The shape of the proof

`docs/verification.md` asks for a state relation, per-construct simulation
lemmas, and a composition step.

1. `Agrees` is the state relation: each declared variable's heap cell holds
   the encoding of its value.
2. `Emits` is an emission algebra over the generator's state monad, with one
   lemma per syntactic form.
3. `Clean` and `labelsOk_of_nodup` settle the labels: `labelOf` is injective,
   no counter is used twice, so `Whitespace.labelMap` sends every label to
   the position just past its own `label` instruction.
4. `simExpr` and `simStmt` are the per-construct simulations, composed with
   `Langlib.Common.Reaches`, which carries the fuel exactly.
5. `bespokeCompile_correct` is the end-to-end theorem.
-/

open private compileExpr compileStmt emit emits fresh addrOf emitTrap emitBool emitStr
  emitOobTrap from Langlib.Languages.Turpentine.Compile.Whitespace
open private pushStr from Langlib.Languages.Turpentine.Semantics

namespace Langlib.Turpentine.Certified.BespokeWhitespace

open Langlib.Common
open Langlib.Computability (WhitespaceLang)
open Langlib.Whitespace (Instr Prog Label)
open Langlib.Turpentine
open Langlib.Turpentine.Compile.Whitespace (Frame St M labelOf compileChecked slotSize Types)

/-! ## Labels are injective

`labelOf n` is the binary expansion of `n + 1`, `1` spelled `T` and `0`
spelled `S`. Reading the spelling back as a binary numeral recovers `n + 1`,
so distinct counters give distinct labels. Every argument about jump targets
below rests on this. -/

/-- Read a `T`/`S` spelling back as a binary numeral. -/
def binOfChars (cs : List Char) : Nat :=
  cs.foldl (fun acc c => 2 * acc + (if c = 'T' then 1 else 0)) 0

/-- The spelling used by `labelOf`. -/
def spell (c : Char) : Char := if c == '1' then 'T' else 'S'

theorem binOfChars_spell_toDigits (m : Nat) :
    binOfChars ((Nat.toDigits 2 m).map spell) = m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rw [Nat.toDigits_eq_if (by omega : 1 < 2)]
    split
    · rename_i hlt
      have hm : m = 0 ∨ m = 1 := by omega
      rcases hm with h | h <;> subst h <;> decide
    · rename_i hge
      have hdiv : m / 2 < m := Nat.div_lt_self (by omega) (by omega)
      have hIH := ih (m / 2) hdiv
      unfold binOfChars at hIH ⊢
      rw [List.map_append, List.foldl_append, hIH]
      have h2 : m % 2 = 0 ∨ m % 2 = 1 := by omega
      rcases h2 with h | h <;> rw [h] <;> simp [spell, Nat.digitChar] <;> omega

theorem labelOf_inj {j k : Nat} (h : labelOf j = labelOf k) : j = k := by
  have h0 := String.ofList_injective h
  have h1 : (Nat.toDigits 2 (j + 1)).map spell = (Nat.toDigits 2 (k + 1)).map spell := h0
  have h2 := congrArg binOfChars h1
  rw [binOfChars_spell_toDigits, binOfChars_spell_toDigits] at h2
  omega

/-! ## The emission algebra

The backend is a state monad over an instruction array and a label counter.
`Emits f c code c' a` says: run from counter `c`, `f` appends exactly `code`,
leaves the counter at `c'`, and returns `a`. The three lemmas below (unit,
bind, determinism) are all the composition this file needs. -/

/-- `f` appends exactly `code` and moves the label counter from `c` to `c'`,
returning `a`. Stated for every prefix already emitted, which is what makes
it compose. -/
def Emits {α : Type} (f : M α) (c : Nat) (code : List Instr) (c' : Nat) (a : α) : Prop :=
  ∀ out : List Instr,
    StateT.run f ⟨out.toArray, c⟩ = .ok (a, ⟨(out ++ code).toArray, c'⟩)

theorem Emits.pure {α : Type} (a : α) (c : Nat) : Emits (Pure.pure a) c [] c a := by
  intro out; simp only [List.append_nil]; rfl

theorem Emits.bind {α β : Type} {f : M α} {g : α → M β} {c c₁ c₂ : Nat}
    {code₁ code₂ : List Instr} {a : α} {b : β}
    (hf : Emits f c code₁ c₁ a) (hg : Emits (g a) c₁ code₂ c₂ b) :
    Emits (f >>= g) c (code₁ ++ code₂) c₂ b := by
  intro out
  rw [StateT.run_bind, hf out]
  show StateT.run (g a) ⟨(out ++ code₁).toArray, c₁⟩ = _
  rw [hg (out ++ code₁), List.append_assoc]

/-- The specialisation used constantly: two statements in sequence. -/
theorem Emits.seq {α : Type} {f : M PUnit} {g : M α} {c c₁ c₂ : Nat}
    {code₁ code₂ : List Instr} {a : α}
    (hf : Emits f c code₁ c₁ PUnit.unit) (hg : Emits g c₁ code₂ c₂ a) :
    Emits (f >>= fun _ => g) c (code₁ ++ code₂) c₂ a := Emits.bind hf hg

/-- Determinism: the emitted code and the final counter are functions of the
initial counter, so a decomposition derived one way matches any other. -/
theorem Emits.det {α : Type} {f : M α} {c c₁ c₂ : Nat} {code₁ code₂ : List Instr}
    {a₁ a₂ : α} (h₁ : Emits f c code₁ c₁ a₁) (h₂ : Emits f c code₂ c₂ a₂) :
    code₁ = code₂ ∧ c₁ = c₂ ∧ a₁ = a₂ := by
  have e := (h₁ []).symm.trans (h₂ [])
  simp only [Except.ok.injEq, Prod.mk.injEq, List.nil_append] at e
  obtain ⟨ha, hs⟩ := e
  have hs' : (⟨code₁.toArray, c₁⟩ : St) = ⟨code₂.toArray, c₂⟩ := hs
  have h3 := congrArg St.out hs'
  have h4 := congrArg St.next hs'
  exact ⟨by simpa using congrArg Array.toList h3, h4, ha⟩

theorem emits_emit (i : Instr) (c : Nat) : Emits (emit i) c [i] c PUnit.unit := by
  intro out
  show Except.ok (PUnit.unit, (⟨out.toArray.push i, c⟩ : St)) = _
  simp

theorem emits_emits (l : List Instr) (c : Nat) : Emits (emits l) c l c PUnit.unit := by
  induction l with
  | nil => intro out; simp only [List.append_nil]; rfl
  | cons i rest ih =>
    have h := Emits.seq (emits_emit i c) ih
    have he : (emits (i :: rest) : M PUnit) = (emit i >>= fun _ => emits rest) := rfl
    rw [he]
    simpa using h

theorem emits_fresh (c : Nat) : Emits fresh c [] (c + 1) (labelOf c) := by
  intro out
  simp only [List.append_nil]
  rfl

/-! ## Which labels a block defines

A generated block is *clean* between two counter values when every `label`
instruction in it is `labelOf k` for a `k` in that range and no label is
defined twice. Cleanliness composes along `++` because the ranges abut, and
it is what turns `labelMap`'s first-definition-wins rule into "every label
resolves to the position just after itself". -/

/-- The labels a block defines, in order. -/
def labelsOf : List Instr → List Label
  | [] => []
  | Instr.label l :: rest => l :: labelsOf rest
  | _ :: rest => labelsOf rest

theorem labelsOf_append (c₁ c₂ : List Instr) :
    labelsOf (c₁ ++ c₂) = labelsOf c₁ ++ labelsOf c₂ := by
  induction c₁ with
  | nil => rfl
  | cons i rest ih => cases i <;> simp [labelsOf, ih]

/-- A left inverse of `labelOf`, so a block's labels can be discussed as the
counter values they came from. -/
def unlabel (l : Label) : Nat := binOfChars l.toList - 1

theorem unlabel_labelOf (k : Nat) : unlabel (labelOf k) = k := by
  have h : unlabel (labelOf k) = binOfChars ((Nat.toDigits 2 (k + 1)).map spell) - 1 := by
    show binOfChars (String.ofList ((Nat.toDigits 2 (k + 1)).map spell)).toList - 1 = _
    rw [String.toList_ofList]
  rw [h, binOfChars_spell_toDigits]
  omega

/-- The counter values behind a block's labels, in order. -/
def labelIdxs (code : List Instr) : List Nat := (labelsOf code).map unlabel

theorem labelIdxs_append (c₁ c₂ : List Instr) :
    labelIdxs (c₁ ++ c₂) = labelIdxs c₁ ++ labelIdxs c₂ := by
  simp [labelIdxs, labelsOf_append]

theorem labelIdxs_label (k : Nat) : labelIdxs [Instr.label (labelOf k)] = [k] := by
  simp [labelIdxs, labelsOf, unlabel_labelOf]

/-- `code` defines only labels from counter values in `[lo, hi)`, and defines
none of them twice. Tracking the counter values rather than the label strings
is what lets blocks compose even though a `fresh` taken early can emit its
`label` late. -/
structure Clean (lo hi : Nat) (code : List Instr) : Prop where
  bounds : ∀ k ∈ labelIdxs code, lo ≤ k ∧ k < hi
  nodup : (labelIdxs code).Nodup

theorem Clean.labels_nodup {lo hi : Nat} {code : List Instr} (h : Clean lo hi code) :
    (labelsOf code).Nodup := List.Nodup.of_map unlabel h.nodup

theorem Clean.mono {lo hi lo' hi' : Nat} {code : List Instr} (h : Clean lo hi code)
    (h₁ : lo' ≤ lo) (h₂ : hi ≤ hi') : Clean lo' hi' code :=
  ⟨fun k hk => ⟨by have := (h.bounds k hk).1; omega, by have := (h.bounds k hk).2; omega⟩,
   h.nodup⟩

theorem Clean.ofNoLabels {lo hi : Nat} {code : List Instr} (h : labelIdxs code = []) :
    Clean lo hi code := ⟨by rw [h]; simp, by rw [h]; simp⟩

theorem Clean.ofEq {lo hi : Nat} {code : List Instr} {ks : List Nat}
    (he : labelIdxs code = ks) (hb : ∀ k ∈ ks, lo ≤ k ∧ k < hi) (hn : ks.Nodup) :
    Clean lo hi code := ⟨by rw [he]; exact hb, by rw [he]; exact hn⟩

theorem nodup_app {l₁ l₂ : List Nat} (h₁ : l₁.Nodup) (h₂ : l₂.Nodup)
    (hd : ∀ k, k ∈ l₁ → k ∈ l₂ → False) : (l₁ ++ l₂).Nodup :=
  List.Nodup.append h₁ h₂ (fun {a} ha hb => hd a ha hb)

/-- Two blocks whose counter ranges abut. -/
theorem Clean.appendUp {lo mid hi : Nat} {c₁ c₂ : List Instr}
    (hlo : lo ≤ mid) (hhi : mid ≤ hi)
    (h₁ : Clean lo mid c₁) (h₂ : Clean mid hi c₂) : Clean lo hi (c₁ ++ c₂) := by
  refine Clean.ofEq (labelIdxs_append c₁ c₂) ?_ ?_
  · intro k hk
    rcases List.mem_append.mp hk with hm | hm
    · have := h₁.bounds k hm; omega
    · have := h₂.bounds k hm; omega
  · refine nodup_app h₁.nodup h₂.nodup ?_
    intro k hk₁ hk₂
    have := h₁.bounds k hk₁
    have := h₂.bounds k hk₂
    omega

theorem clean_label (k : Nat) : Clean k (k + 1) [Instr.label (labelOf k)] :=
  Clean.ofEq (labelIdxs_label k) (by intro j hj; simp at hj; omega) (by simp)

/-! ## Placing code in the compiled array -/

/-- `code` occupies consecutive positions of `prog` from `p`. -/
def CodeAt (prog : Prog) (p : Nat) (code : List Instr) : Prop :=
  ∀ j, j < code.length → prog[p + j]? = code[j]?

theorem CodeAt.get {prog : Prog} {p : Nat} {code : List Instr} (h : CodeAt prog p code)
    (j : Nat) (hj : j < code.length) : prog[p + j]? = some code[j] := by
  rw [h j hj, List.getElem?_eq_getElem hj]

theorem CodeAt.left {prog : Prog} {p : Nat} {c₁ c₂ : List Instr}
    (h : CodeAt prog p (c₁ ++ c₂)) : CodeAt prog p c₁ := by
  intro j hj
  rw [h j (by simp; omega), List.getElem?_append_left hj]

theorem CodeAt.right {prog : Prog} {p : Nat} {c₁ c₂ : List Instr}
    (h : CodeAt prog p (c₁ ++ c₂)) : CodeAt prog (p + c₁.length) c₂ := by
  intro j hj
  rw [show p + c₁.length + j = p + (c₁.length + j) from by omega,
    h (c₁.length + j) (by simp; omega),
    List.getElem?_append_right (Nat.le_add_right _ _)]
  simp

theorem codeAt_of_eq {prog : Prog} {p : Nat} {c₁ c₂ : List Instr}
    (h : CodeAt prog p c₁) (he : c₂ = c₁) : CodeAt prog p c₂ := he ▸ h

/-- Every `label` inside `code` resolves to the position just after itself.
This is the only thing a jump lemma needs to know about `labelMap`. -/
def LabelsOk (labels : Std.HashMap Label Nat) (p : Nat) (code : List Instr) : Prop :=
  ∀ j l, code[j]? = some (Instr.label l) → labels[l]? = some (p + j + 1)

theorem LabelsOk.left {labels : Std.HashMap Label Nat} {p : Nat} {c₁ c₂ : List Instr}
    (h : LabelsOk labels p (c₁ ++ c₂)) : LabelsOk labels p c₁ := by
  intro j l hj
  have hj' : j < c₁.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hj
    simp at hj
  exact h j l (by rw [List.getElem?_append_left hj']; exact hj)

theorem LabelsOk.right {labels : Std.HashMap Label Nat} {p : Nat} {c₁ c₂ : List Instr}
    (h : LabelsOk labels p (c₁ ++ c₂)) : LabelsOk labels (p + c₁.length) c₂ := by
  intro j l hj
  have := h (c₁.length + j) l (by
    rw [List.getElem?_append_right (Nat.le_add_right _ _)]; simpa using hj)
  rwa [show p + (c₁.length + j) + 1 = p + c₁.length + j + 1 from by omega] at this

theorem labelsOk_of_eq {labels : Std.HashMap Label Nat} {p : Nat} {c₁ c₂ : List Instr}
    (h : LabelsOk labels p c₁) (he : c₂ = c₁) : LabelsOk labels p c₂ := he ▸ h

/-! ## From cleanliness to the label table -/

open Langlib.Computability.URMWhitespace (NoLabel labelGo labelMap_eq labelGo_first)

theorem noLabel_iff {l : Label} {code : List Instr} :
    NoLabel l code ↔ l ∉ labelsOf code := by
  induction code with
  | nil => simp [NoLabel, labelsOf]
  | cons i rest ih =>
    cases i <;> simp_all [NoLabel, labelsOf, List.mem_cons, eq_comm]

/-- **The label table of a clean program.** With no label defined twice,
`labelMap`'s first-definition rule gives every label the position just past
its own `label` instruction. -/
theorem labelsOk_of_nodup (W : List Instr) (h : (labelsOf W).Nodup) :
    LabelsOk (Langlib.Whitespace.labelMap W.toArray) 0 W := by
  intro j l hj
  have hjlt : j < W.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hj
    simp at hj
  have hsplit : W = W.take j ++ Instr.label l :: W.drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop j W]
    congr 1
    rw [List.drop_eq_getElem_cons hjlt]
    congr 1
    rw [List.getElem?_eq_getElem hjlt] at hj
    exact Option.some.inj hj
  have hlen : (W.take j).length = j := by rw [List.length_take]; omega
  have hnod : (labelsOf (W.take j) ++ l :: labelsOf (W.drop (j + 1))).Nodup := by
    conv at h => rw [hsplit]
    rwa [labelsOf_append, show labelsOf (Instr.label l :: W.drop (j + 1))
      = l :: labelsOf (W.drop (j + 1)) from rfl] at h
  have hnot : l ∉ labelsOf (W.take j) := by
    intro hmem
    exact (List.disjoint_of_nodup_append hnod) hmem (List.mem_cons_self ..)
  rw [labelMap_eq, List.toList_toArray]
  conv_lhs => rw [hsplit]
  rw [labelGo_first _ _ _ 0 ∅ (by simp) (noLabel_iff.mpr hnot), hlen]

/-! ## Single instructions

`Langlib/Computability/Whitespace.lean` already proves the atoms for `push`,
`label`, `store`, `retrieve`, `add`, `sub`, `jz` and `outnum`. These are the
ones this backend also needs. -/

open Langlib.Computability.URMWhitespace (reaches_push reaches_label reaches_store
  reaches_retrieve reaches_add reaches_sub reaches_jz_taken reaches_jz_untaken
  reaches_outNum exec_halt)

variable {prog : Prog} {labels : Std.HashMap Label Nat}

theorem reaches_dup (s : Whitespace.State) (n : Int) (st : List Int)
    (hst : s.stack = n :: st) (h : prog[s.pc]? = some Instr.dup) :
    Reaches (Whitespace.exec prog labels) s
      { s with pc := s.pc + 1, stack := n :: n :: st } :=
  Reaches.one fun _ => by simp only [Whitespace.exec, h, hst]

theorem reaches_drop (s : Whitespace.State) (n : Int) (st : List Int)
    (hst : s.stack = n :: st) (h : prog[s.pc]? = some Instr.drop) :
    Reaches (Whitespace.exec prog labels) s { s with pc := s.pc + 1, stack := st } :=
  Reaches.one fun _ => by simp only [Whitespace.exec, h, hst]

theorem reaches_mul (s : Whitespace.State) (a b : Int) (st : List Int)
    (hst : s.stack = b :: a :: st) (h : prog[s.pc]? = some Instr.mul) :
    Reaches (Whitespace.exec prog labels) s
      { s with pc := s.pc + 1, stack := (a * b) :: st } :=
  Reaches.one fun _ => by simp only [Whitespace.exec, h, hst]

theorem reaches_jump (s : Whitespace.State) (l : Label) (p' : Nat)
    (hl : labels[l]? = some p') (h : prog[s.pc]? = some (Instr.jump l)) :
    Reaches (Whitespace.exec prog labels) s { s with pc := p' } :=
  Reaches.one fun _ => by simp only [Whitespace.exec, h]; simp only [hl]

theorem reaches_jn_taken (s : Whitespace.State) (n : Int) (st : List Int) (l : Label)
    (p' : Nat) (hn : n < 0) (hst : s.stack = n :: st) (hl : labels[l]? = some p')
    (h : prog[s.pc]? = some (Instr.jn l)) :
    Reaches (Whitespace.exec prog labels) s { s with pc := p', stack := st } :=
  Reaches.one fun _ => by
    simp only [Whitespace.exec, h, hst]
    rw [if_pos hn]
    simp only [hl]

theorem reaches_jn_untaken (s : Whitespace.State) (n : Int) (st : List Int) (l : Label)
    (hn : ¬ n < 0) (hst : s.stack = n :: st) (h : prog[s.pc]? = some (Instr.jn l)) :
    Reaches (Whitespace.exec prog labels) s { s with pc := s.pc + 1, stack := st } :=
  Reaches.one fun _ => by
    simp only [Whitespace.exec, h, hst]
    rw [if_neg hn]

/-! ## Printing, byte by byte

The fragment's `print` statements are the first constructs whose code does
something a proof can see from outside the machine, so they need three
things nothing above them needed: how UTF-8 encoding behaves under string
append, what code `emitStr` emits, and what running that code does to the
output and the trace.

The last of those, `reaches_bytesCode`, deliberately does **not** name the
output bytes. It says only that the events are the bytes pushed; the output
is recovered from the trace by `Langlib/Languages/Whitespace/Trace.lean`,
which proves the two agree for every whitespace program. -/

/-- Two byte arrays with the same bytes are the same array. This is how the
proof gets back from a list of bytes, which is what a trace speaks in, to
the `ByteArray` an output is. -/
theorem bytes_ext {a b : ByteArray} (h : a.toList = b.toList) : a = b := by
  apply ByteArray.ext
  rw [ByteArray.toList_eq, ByteArray.toList_eq] at h
  exact Array.ext' h

/-- The empty string encodes to nothing. -/
@[simp] theorem emptyStr_toList : "".toUTF8.toList = [] := by
  rw [ByteArray.toList_eq]; rfl

/-- Appending nothing to the output is not appending. -/
@[simp] theorem append_emptyStr (b : ByteArray) : b ++ "".toUTF8 = b := by
  have h : "".toUTF8 = ByteArray.empty := ByteArray.ext rfl
  rw [h]
  exact ByteArray.append_empty

/-- UTF-8 encoding distributes over string append. -/
theorem toUTF8_append (s t : String) : (s ++ t).toUTF8 = s.toUTF8 ++ t.toUTF8 :=
  ByteArray.ext rfl

theorem toUTF8_toList_append (s t : String) :
    (s ++ t).toUTF8.toList = s.toUTF8.toList ++ t.toUTF8.toList := by
  rw [toUTF8_append, ByteArray.toList_append]

/-- Recording two runs of bytes is recording their concatenation. -/
theorem recOut_append (es : List Event) (bs cs : List UInt8) :
    Trace.recOut es (bs ++ cs) = Trace.recOut (Trace.recOut es bs) cs := by
  simp [Trace.recOut]

/-- Recording bytes prepends their events, most recent first. This is the
bridge between the interpreters' `recOut`, which is a `foldl` chosen to make
recording cheap, and the simulation's `Δ ++ events`, which is what
composes. -/
theorem recOut_eq_append (es : List Event) (bs : List UInt8) :
    Trace.recOut es bs = (Trace.ofOutput bs).reverse ++ es := by
  induction bs generalizing es with
  | nil => rfl
  | cons b bs ih =>
    show Trace.recOut (Event.out b :: es) bs = _
    rw [ih]
    simp [Trace.ofOutput]

/-- The code `emitStr` emits for a list of bytes: push, print, repeat. -/
def bytesCode (bs : List UInt8) : List Instr :=
  bs.flatMap fun b => [Instr.push (Int.ofNat b.toNat), Instr.outChar]

theorem bytesCode_append (bs cs : List UInt8) :
    bytesCode (bs ++ cs) = bytesCode bs ++ bytesCode cs := by
  simp [bytesCode]

theorem bytesCode_length (bs : List UInt8) : (bytesCode bs).length = 2 * bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [bytesCode] at ih ⊢; omega

theorem emits_emitStr (str : String) (c : Nat) :
    Emits (emitStr str) c (bytesCode str.toUTF8.toList) c PUnit.unit := by
  show Emits (str.toUTF8.toList.forM _) c _ c PUnit.unit
  generalize str.toUTF8.toList = bs
  induction bs with
  | nil => exact Emits.pure _ _
  | cons b bs ih =>
    show Emits (_ >>= fun _ => List.forM bs _) c _ c PUnit.unit
    rw [show bytesCode (b :: bs) = ([Instr.push (Int.ofNat b.toNat)] ++ [Instr.outChar])
        ++ bytesCode bs from by simp [bytesCode]]
    exact Emits.seq (Emits.seq (emits_emit _ c) (emits_emit _ c)) ih

/-! ## The covered fragment

The backend accepts all of Turpentine. This proof covers the sublanguage
below, and `bespokeWhitespace.compile` rejects everything else, so the
theorem's hypothesis and the compiler's acceptance are the same predicate.

* declarations: `int` and `bool` scalars with no initialiser, names
  pairwise distinct, one of them `answer : int`;
* expressions: literals of either type (negative integers included),
  variables, `-` and `!`, and `+ - * == != < <= > >= && ||`;
* statements: `skip`, sequencing, assignment, `if`, `while`, `assert`.

Left out, with the reason: `/` and `%` (the backend's Euclidean correction
branches on the sign of the divisor, which is a separate arithmetic
obligation), arrays and `len` (a second address space), and every I/O
statement (the specification `TurpentineHaltsWith` names a single `Nat` in
`answer` and runs on an empty input stream, so there is no place for a byte
stream to go). -/

/-- The operators the proof covers: everything except `/` and `%`. -/
def okOp : BinOp → Bool
  | .div | .mod => false
  | _ => true

/-- Expressions in the fragment, with the declared names in scope. -/
def okExpr (ns : List String) : Expr → Bool
  | .intLit _ => true
  | .boolLit _ => true
  | .var x => ns.contains x
  | .index _ _ => false
  | .len _ => false
  | .un _ e => okExpr ns e
  | .bin op a b => okOp op && okExpr ns a && okExpr ns b

/-- Does a runtime value have the type the declarations gave it? -/
def valHasTy : Value → Ty → Bool
  | .int _, .int => true
  | .bool _, .bool => true
  | .arr _, .array _ _ => true
  | _, _ => false

theorem valHasTy_default (t : Ty) : valHasTy (Turpentine.initEnv.default t) t = true := by
  cases t <;> rfl

/-- Type equality as a `Bool` the fragment check can use. `Ty` derives
`BEq` but no `LawfulBEq`, so this is a plain predicate that inverts. -/
def tyEq : Ty → Ty → Bool
  | .int, .int => true
  | .bool, .bool => true
  | _, _ => false

theorem tyEq_eq {a b : Ty} (h : tyEq a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | simp [tyEq] at h

/-- An assignment is in the fragment when its right-hand side has the
declared type of the variable.

This is the one place the fragment became *smaller* when `print` was
admitted, and it had to. The backend chooses between `outnum` and the
`true`/`false` branch from the expression's **static** type, while the
reference interpreter renders the **runtime** value; a program that stored
a bool in an `int` variable would print `true` where its compilation prints
`1`. Turpentine's own type checker rejects such a program, and now so does
this fragment, which is what lets the simulation carry the invariant that
the two types agree. -/
def okAssignTy (tys : Types) (x : String) (e : Expr) : Bool :=
  match tys[x]?, inferExpr tys e with
  | some tx, .ok te => tyEq tx te
  | _, _ => false

theorem okAssignTy_inv {tys : Types} {x : String} {e : Expr}
    (h : okAssignTy tys x e = true) :
    ∃ t, tys[x]? = some t ∧ inferExpr tys e = .ok t := by
  rw [okAssignTy] at h
  split at h
  · rename_i tx te hx he
    exact ⟨tx, hx, by rw [he, tyEq_eq h]⟩
  · simp at h

/-- The printed types the backend has code for. `print` is the one
construct whose compilation consults the typing context — it chooses
between `outnum` and the `true`/`false` branch — so the fragment check has
to consult it too, and `okStmt` carries the same map the frame does. -/
def okPrintTy (tys : Types) (e : Expr) : Bool :=
  match inferExpr tys e with
  | .ok .int => true
  | .ok .bool => true
  | _ => false

theorem okPrintTy_cases {tys : Types} {e : Expr} (h : okPrintTy tys e = true) :
    inferExpr tys e = .ok Ty.int ∨ inferExpr tys e = .ok Ty.bool := by
  rw [okPrintTy] at h
  split at h
  · rename_i ht; exact Or.inl ht
  · rename_i ht; exact Or.inr ht
  · simp at h

/-- Statements in the fragment. -/
def okStmt (ns : List String) (tys : Types) : Stmt → Bool
  | .skip => true
  | .seq a b => okStmt ns tys a && okStmt ns tys b
  | .assign x e => ns.contains x && okExpr ns e && okAssignTy tys x e
  | .ite c a b => okExpr ns c && okStmt ns tys a && okStmt ns tys b
  | .while c b => okExpr ns c && okStmt ns tys b
  | .assert e => okExpr ns e
  | .printExpr e _ => okExpr ns e && okPrintTy tys e
  | .printStr _ _ => true
  | _ => false

/-! ## The state relation

A Turpentine `int` is the heap cell holding the same integer; a `bool` is
`1` or `0`. `Agrees` is the whole invariant: whitespace has unbounded signed
cells and Turpentine has unbounded signed integers, so there is no
representation to prove anything about. -/

/-- How a Turpentine value sits in a heap cell. -/
def encV : Value → Int
  | .int n => n
  | .bool b => if b then 1 else 0
  | .arr _ => 0

/-- Every declared variable's cell holds its value, and the value has the
type the declaration gave it.

The second half is not about representation — `encV` erases it, since a
`bool` and the integers `0`/`1` are the same cell. It is there for `print`,
whose code the backend picks from the static type while the reference
interpreter renders the runtime value. Carrying it in `Agrees` rather than
in a second invariant is what keeps the simulation's shape: the only
statement that can break it is the one that already had to re-establish
`Agrees`. -/
def Agrees (ctx : Frame) (env : Std.HashMap String Value)
    (heap : Std.HashMap Int Int) : Prop :=
  ∀ (x : String) (a : Int), ctx.addrs[x]? = some a →
    ∀ v, env[x]? = some v →
      heap.getD a 0 = encV v ∧ ∀ t, ctx.types[x]? = some t → valHasTy v t = true

/-- The layout facts the proof needs: addresses are non-negative (whitespace
rejects negative ones) and distinct variables get distinct cells. -/
structure GoodFrame (ctx : Frame) : Prop where
  nonneg : ∀ (x : String) (a : Int), ctx.addrs[x]? = some a → 0 ≤ a
  inj : ∀ (x y : String) (a : Int), ctx.addrs[x]? = some a → ctx.addrs[y]? = some a → x = y

theorem Agrees.update {ctx : Frame} {env : Std.HashMap String Value}
    {heap : Std.HashMap Int Int} {x : String} {a : Int} {v : Value}
    (hg : GoodFrame ctx) (hA : Agrees ctx env heap) (hx : ctx.addrs[x]? = some a)
    (hv : ∀ t, ctx.types[x]? = some t → valHasTy v t = true) :
    Agrees ctx (env.insert x v) (heap.insert a (encV v)) := by
  intro y b hy w hw
  by_cases hxy : y = x
  · subst hxy
    rw [hx, Option.some.injEq] at hy
    subst hy
    rw [Std.HashMap.getElem?_insert, if_pos (by simp)] at hw
    rw [Std.HashMap.getD_insert, if_pos (by simp)]
    exact ⟨by rw [Option.some.inj hw], fun t ht => Option.some.inj hw ▸ hv t ht⟩
  · have hab : b ≠ a := by
      intro hc
      exact hxy (hg.inj y x a (hc ▸ hy) hx)
    rw [Std.HashMap.getElem?_insert, if_neg (by simpa using Ne.symm hxy)] at hw
    rw [Std.HashMap.getD_insert, if_neg (by simpa using Ne.symm hab)]
    exact hA y b hy w hw

/-- Every name in scope has a cell. -/
def Covers (ctx : Frame) (ns : List String) : Prop :=
  ∀ x ∈ ns, ∃ a, ctx.addrs[x]? = some a

/-! ## What the generator emits, construct by construct

One lemma per syntactic form, each read off the generator by `rfl` and then
composed with `Emits.bind`. They are used twice: once to show that a
fragment program emits *something* (`emitsExpr`, `emitsStmt`), and once
inside the simulation, to decompose the code a hypothesis hands back. -/

/-- The tail every comparison shares: a conditional jump, then the two
constants. `t` is the jump instruction, already pointed at `labelOf c`. -/
def boolTail (t : Instr) (c : Nat) : List Instr :=
  [t, Instr.push 0, Instr.jump (labelOf (c + 1)), Instr.label (labelOf c),
   Instr.push 1, Instr.label (labelOf (c + 1))]

theorem emits_addrOf {ctx : Frame} {x : String} {a : Int} (h : ctx.addrs[x]? = some a)
    (c : Nat) : Emits (addrOf ctx x) c [] c a := by
  have he : addrOf ctx x = (Pure.pure a : M Int) := by
    show (match ctx.addrs[x]? with
      | some a => pure a
      | none => throw _) = _
    rw [h]
  rw [he]
  exact Emits.pure a c

theorem emits_emitBool (mk : Label → M Unit) (c : Nat) (mkcode : List Instr) (c'' : Nat)
    (h : Emits (mk (labelOf c)) (c + 2) mkcode c'' PUnit.unit) :
    Emits (emitBool mk) c
      (mkcode ++ [Instr.push 0, Instr.jump (labelOf (c + 1)), Instr.label (labelOf c),
        Instr.push 1, Instr.label (labelOf (c + 1))]) c'' PUnit.unit := by
  have he : emitBool mk = (fresh >>= fun t => fresh >>= fun e => mk t >>= fun _ =>
      emits [Instr.push 0, Instr.jump e, Instr.label t, Instr.push 1, Instr.label e]) := rfl
  rw [he]
  have h1 := Emits.seq h (emits_emits [Instr.push 0, Instr.jump (labelOf (c + 1)),
    Instr.label (labelOf c), Instr.push 1, Instr.label (labelOf (c + 1))] c'')
  have h2 := Emits.bind (g := fun e => mk (labelOf c) >>= fun _ =>
      emits [Instr.push 0, Instr.jump e, Instr.label (labelOf c), Instr.push 1, Instr.label e])
    (emits_fresh (c + 1)) h1
  have h3 := Emits.bind (g := fun t => fresh >>= fun e => mk t >>= fun _ =>
      emits [Instr.push 0, Instr.jump e, Instr.label t, Instr.push 1, Instr.label e])
    (emits_fresh c) h2
  simpa using h3

/-- The comparison tail as one block. -/
theorem emits_cmpTail (mk : Label → Instr) (c : Nat) :
    Emits (emitBool fun t => emit (mk t)) c (boolTail (mk (labelOf c)) c) (c + 2)
      PUnit.unit := by
  have h := emits_emitBool (fun t => emit (mk t)) c [mk (labelOf c)] (c + 2)
    (emits_emit _ _)
  simpa [boolTail] using h

/-! ### Expressions -/

theorem emitsE_intLit (ctx : Frame) (n : Int) (c : Nat) :
    Emits (compileExpr ctx (.intLit n)) c [Instr.push n] c PUnit.unit := by
  show Emits (emit (Instr.push n)) c _ c _
  exact emits_emit _ _

theorem emitsE_boolLit (ctx : Frame) (b : Bool) (c : Nat) :
    Emits (compileExpr ctx (.boolLit b)) c [Instr.push (if b then 1 else 0)] c PUnit.unit := by
  show Emits (emit (Instr.push (if b then 1 else 0))) c _ c _
  exact emits_emit _ _

theorem emitsE_var {ctx : Frame} {x : String} {a : Int} (h : ctx.addrs[x]? = some a)
    (c : Nat) :
    Emits (compileExpr ctx (.var x)) c [Instr.push a, Instr.retrieve] c PUnit.unit := by
  have he : compileExpr ctx (.var x)
      = (addrOf ctx x >>= fun a => emits [Instr.push a, Instr.retrieve]) := rfl
  rw [he]
  simpa using Emits.bind (emits_addrOf h c) (emits_emits [Instr.push a, Instr.retrieve] c)

theorem emitsE_neg {ctx : Frame} {e : Expr} {c c' : Nat} {code : List Instr}
    (h : Emits (compileExpr ctx e) c code c' PUnit.unit) :
    Emits (compileExpr ctx (.un .neg e)) c ([Instr.push 0] ++ (code ++ [Instr.sub])) c'
      PUnit.unit := by
  have he : compileExpr ctx (.un .neg e)
      = (emit (Instr.push 0) >>= fun _ => compileExpr ctx e >>= fun _ => emit Instr.sub) := rfl
  rw [he]
  exact Emits.seq (emits_emit _ c) (Emits.seq h (emits_emit _ c'))

theorem emitsE_not {ctx : Frame} {e : Expr} {c c' : Nat} {code : List Instr}
    (h : Emits (compileExpr ctx e) c code c' PUnit.unit) :
    Emits (compileExpr ctx (.un .not e)) c ([Instr.push 1] ++ (code ++ [Instr.sub])) c'
      PUnit.unit := by
  have he : compileExpr ctx (.un .not e)
      = (emit (Instr.push 1) >>= fun _ => compileExpr ctx e >>= fun _ => emit Instr.sub) := rfl
  rw [he]
  exact Emits.seq (emits_emit _ c) (Emits.seq h (emits_emit _ c'))

/-- The three operators that are one whitespace instruction. -/
theorem emitsE_arith {ctx : Frame} {tgt e₁ e₂ : Expr} {i : Instr}
    {c c₁ c₂ : Nat} {ca cb : List Instr}
    (hop : compileExpr ctx tgt
      = (compileExpr ctx e₁ >>= fun _ => compileExpr ctx e₂ >>= fun _ => emit i))
    (ha : Emits (compileExpr ctx e₁) c ca c₁ PUnit.unit)
    (hb : Emits (compileExpr ctx e₂) c₁ cb c₂ PUnit.unit) :
    Emits (compileExpr ctx tgt) c (ca ++ (cb ++ [i])) c₂ PUnit.unit := by
  rw [hop]
  exact Emits.seq ha (Emits.seq hb (emits_emit _ c₂))

/-- The comparisons that subtract and then test the sign or zero, with the
operands in source order. -/
theorem emitsE_cmp {ctx : Frame} {tgt e₁ e₂ : Expr} {mk : Label → Instr}
    {c c₁ c₂ : Nat} {ca cb : List Instr}
    (hop : compileExpr ctx tgt
      = (compileExpr ctx e₁ >>= fun _ => compileExpr ctx e₂ >>= fun _ =>
          emit Instr.sub >>= fun _ => emitBool fun t => emit (mk t)))
    (ha : Emits (compileExpr ctx e₁) c ca c₁ PUnit.unit)
    (hb : Emits (compileExpr ctx e₂) c₁ cb c₂ PUnit.unit) :
    Emits (compileExpr ctx tgt) c
      (ca ++ (cb ++ ([Instr.sub] ++ boolTail (mk (labelOf c₂)) c₂))) (c₂ + 2) PUnit.unit := by
  rw [hop]
  exact Emits.seq ha (Emits.seq hb (Emits.seq (emits_emit _ c₂) (emits_cmpTail mk c₂)))

/-- `<=` and `>=`: subtract, subtract one, test the sign. -/
theorem emitsE_cmpLe {ctx : Frame} {tgt e₁ e₂ : Expr} {mk : Label → Instr}
    {c c₁ c₂ : Nat} {ca cb : List Instr}
    (hop : compileExpr ctx tgt
      = (compileExpr ctx e₁ >>= fun _ => compileExpr ctx e₂ >>= fun _ =>
          emits [Instr.sub, Instr.push 1, Instr.sub] >>= fun _ =>
            emitBool fun t => emit (mk t)))
    (ha : Emits (compileExpr ctx e₁) c ca c₁ PUnit.unit)
    (hb : Emits (compileExpr ctx e₂) c₁ cb c₂ PUnit.unit) :
    Emits (compileExpr ctx tgt) c
      (ca ++ (cb ++ ([Instr.sub, Instr.push 1, Instr.sub]
        ++ boolTail (mk (labelOf c₂)) c₂))) (c₂ + 2) PUnit.unit := by
  rw [hop]
  exact Emits.seq ha (Emits.seq hb (Emits.seq (emits_emits _ c₂) (emits_cmpTail mk c₂)))

theorem emitsE_ne {ctx : Frame} {a b : Expr} {c c₁ c₂ : Nat} {ca cb : List Instr}
    (ha : Emits (compileExpr ctx a) c ca c₁ PUnit.unit)
    (hb : Emits (compileExpr ctx b) c₁ cb c₂ PUnit.unit) :
    Emits (compileExpr ctx (.bin .ne a b)) c
      (ca ++ (cb ++ ([Instr.sub] ++
        [Instr.jz (labelOf c₂), Instr.push 1, Instr.jump (labelOf (c₂ + 1)),
         Instr.label (labelOf c₂), Instr.push 0, Instr.label (labelOf (c₂ + 1))])))
      (c₂ + 2) PUnit.unit := by
  have he : compileExpr ctx (.bin .ne a b)
      = (compileExpr ctx a >>= fun _ => compileExpr ctx b >>= fun _ =>
          emit Instr.sub >>= fun _ => fresh >>= fun f => fresh >>= fun e =>
            emits [Instr.jz f, Instr.push 1, Instr.jump e, Instr.label f, Instr.push 0,
              Instr.label e]) := rfl
  rw [he]
  refine Emits.seq ha (Emits.seq hb (Emits.seq (emits_emit _ c₂) ?_))
  have h2 := Emits.bind (g := fun e =>
      emits [Instr.jz (labelOf c₂), Instr.push 1, Instr.jump e, Instr.label (labelOf c₂),
        Instr.push 0, Instr.label e])
    (emits_fresh (c₂ + 1)) (emits_emits [Instr.jz (labelOf c₂), Instr.push 1,
      Instr.jump (labelOf (c₂ + 1)), Instr.label (labelOf c₂), Instr.push 0,
      Instr.label (labelOf (c₂ + 1))] (c₂ + 2))
  have h3 := Emits.bind (g := fun f => fresh >>= fun e =>
      emits [Instr.jz f, Instr.push 1, Instr.jump e, Instr.label f, Instr.push 0,
        Instr.label e])
    (emits_fresh c₂) h2
  simpa using h3

theorem emitsE_and {ctx : Frame} {a b : Expr} {c c₁ c₂ : Nat} {ca cb : List Instr}
    (ha : Emits (compileExpr ctx a) (c + 1) ca c₁ PUnit.unit)
    (hb : Emits (compileExpr ctx b) c₁ cb c₂ PUnit.unit) :
    Emits (compileExpr ctx (.bin .and a b)) c
      (ca ++ ([Instr.dup, Instr.jz (labelOf c), Instr.drop]
        ++ (cb ++ [Instr.label (labelOf c)]))) c₂ PUnit.unit := by
  have he : compileExpr ctx (.bin .and a b)
      = (fresh >>= fun e => compileExpr ctx a >>= fun _ =>
          emits [Instr.dup, Instr.jz e, Instr.drop] >>= fun _ =>
            compileExpr ctx b >>= fun _ => emit (Instr.label e)) := rfl
  rw [he]
  have h1 := Emits.seq ha (Emits.seq
    (emits_emits [Instr.dup, Instr.jz (labelOf c), Instr.drop] c₁)
    (Emits.seq hb (emits_emit (Instr.label (labelOf c)) c₂)))
  have h2 := Emits.bind (g := fun e => compileExpr ctx a >>= fun _ =>
      emits [Instr.dup, Instr.jz e, Instr.drop] >>= fun _ =>
        compileExpr ctx b >>= fun _ => emit (Instr.label e))
    (emits_fresh c) h1
  simpa using h2

theorem emitsE_or {ctx : Frame} {a b : Expr} {c c₁ c₂ : Nat} {ca cb : List Instr}
    (ha : Emits (compileExpr ctx a) (c + 2) ca c₁ PUnit.unit)
    (hb : Emits (compileExpr ctx b) c₁ cb c₂ PUnit.unit) :
    Emits (compileExpr ctx (.bin .or a b)) c
      (ca ++ ([Instr.jz (labelOf c), Instr.push 1, Instr.jump (labelOf (c + 1)),
          Instr.label (labelOf c)]
        ++ (cb ++ [Instr.label (labelOf (c + 1))]))) c₂ PUnit.unit := by
  have he : compileExpr ctx (.bin .or a b)
      = (fresh >>= fun second => fresh >>= fun e => compileExpr ctx a >>= fun _ =>
          emits [Instr.jz second, Instr.push 1, Instr.jump e, Instr.label second] >>= fun _ =>
            compileExpr ctx b >>= fun _ => emit (Instr.label e)) := rfl
  rw [he]
  have h1 := Emits.seq ha (Emits.seq
    (emits_emits [Instr.jz (labelOf c), Instr.push 1, Instr.jump (labelOf (c + 1)),
      Instr.label (labelOf c)] c₁)
    (Emits.seq hb (emits_emit (Instr.label (labelOf (c + 1))) c₂)))
  have h2 := Emits.bind (g := fun e => compileExpr ctx a >>= fun _ =>
      emits [Instr.jz (labelOf c), Instr.push 1, Instr.jump e, Instr.label (labelOf c)]
        >>= fun _ => compileExpr ctx b >>= fun _ => emit (Instr.label e))
    (emits_fresh (c + 1)) h1
  have h3 := Emits.bind (g := fun second => fresh >>= fun e =>
      compileExpr ctx a >>= fun _ =>
        emits [Instr.jz second, Instr.push 1, Instr.jump e, Instr.label second] >>= fun _ =>
          compileExpr ctx b >>= fun _ => emit (Instr.label e))
    (emits_fresh c) h2
  simpa using h3


/-- The newline, as the one byte it is. -/
theorem newline_bytes : "\n".toUTF8.toList = [10] := by
  rw [ByteArray.toList_eq]; rfl

/-- The bytes a `print`/`println` of a rendered value writes: the rendering,
then the newline if this was `println`. This is the source's own
`v.render ++ if nl then "\n" else ""`, read as bytes. -/
def outBytes (str : String) (nl : Bool) : List UInt8 :=
  (str ++ (if nl then "\n" else "")).toUTF8.toList

theorem outBytes_eq (str : String) (nl : Bool) :
    outBytes str nl = str.toUTF8.toList ++ (if nl then [10] else []) := by
  cases nl with
  | false =>
    show (str ++ "").toUTF8.toList = _
    rw [show str ++ "" = str from by simp]
    simp
  | true =>
    show (str ++ "\n").toUTF8.toList = _
    rw [toUTF8_toList_append, newline_bytes]
    simp

/-- The trailing newline, as bytes and as code. Keeping them the same shape
lets `print` and `println` run through one lemma instead of two. -/
def nlBytes (nl : Bool) : List UInt8 := if nl then [10] else []

def nlCode (nl : Bool) : List Instr := if nl then bytesCode [10] else []

theorem nlCode_eq (nl : Bool) : nlCode nl = bytesCode (nlBytes nl) := by
  cases nl <;> rfl

theorem outBytes_split (str : String) (nl : Bool) :
    outBytes str nl = str.toUTF8.toList ++ nlBytes nl := by
  rw [outBytes_eq]; cases nl <;> rfl

theorem bytesCode_outBytes (str : String) (nl : Bool) :
    bytesCode (outBytes str nl) = bytesCode str.toUTF8.toList ++ nlCode nl := by
  rw [outBytes_eq, bytesCode_append, nlCode]
  cases nl <;> simp [bytesCode]

/-- Printed bytes define no labels. -/
theorem labelsOf_bytesCode (bs : List UInt8) : labelsOf (bytesCode bs) = [] := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [show bytesCode (b :: bs)
        = [Instr.push (Int.ofNat b.toNat), Instr.outChar] ++ bytesCode bs from by
      simp [bytesCode], labelsOf_append, ih]
    rfl

theorem labelIdxs_bytesCode (bs : List UInt8) : labelIdxs (bytesCode bs) = [] := by
  rw [labelIdxs, labelsOf_bytesCode]; rfl

theorem labelIdxs_nlCode (nl : Bool) : labelIdxs (nlCode nl) = [] := by
  cases nl
  · rfl
  · exact labelIdxs_bytesCode _

theorem emitsS_printStr (ctx : Frame) (str : String) (nl : Bool) (c : Nat) :
    Emits (compileStmt ctx (.printStr str nl)) c (bytesCode (outBytes str nl)) c PUnit.unit := by
  have he : compileStmt ctx (.printStr str nl) = emitStr (str ++ (if nl then "\n" else "")) := by
    cases nl
    · exact congrArg emitStr (by simp)
    · rfl
  rw [he]
  exact emits_emitStr _ c

theorem emits_nl (nl : Bool) (c : Nat) :
    Emits (if nl then emitStr "\n" else Pure.pure PUnit.unit) c (nlCode nl) c PUnit.unit := by
  cases nl
  · exact Emits.pure _ _
  · show Emits (emitStr "\n") c (nlCode true) c PUnit.unit
    have : nlCode true = bytesCode "\n".toUTF8.toList := by rw [nlCode, newline_bytes]; simp
    rw [this]
    exact emits_emitStr _ c

theorem emitsS_printExpr_int {ctx : Frame} {e : Expr} {c c' : Nat} {ce : List Instr}
    (ht : inferExpr ctx.types e = .ok Ty.int) (nl : Bool)
    (hE : Emits (compileExpr ctx e) c ce c' PUnit.unit) :
    Emits (compileStmt ctx (.printExpr e nl)) c
      (ce ++ ([Instr.outNum] ++ nlCode nl)) c' PUnit.unit := by
  have h0 : compileStmt ctx (.printExpr e nl)
      = (match inferExpr ctx.types e with
         | .error m => throw s!"type error in a printed expression: {m}"
         | .ok .int => do
            compileExpr ctx e
            emit Instr.outNum
            if nl then emitStr "\n"
         | .ok .bool => do
            let f ← fresh
            let end_ ← fresh
            compileExpr ctx e
            emit (Instr.jz f)
            emitStr "true"
            emits [Instr.jump end_, Instr.label f]
            emitStr "false"
            emit (Instr.label end_)
            if nl then emitStr "\n"
         | .ok (.array _ _) => throw "internal: printing a whole array") := rfl
  have he : compileStmt ctx (.printExpr e nl)
      = (compileExpr ctx e >>= fun _ => emit Instr.outNum >>= fun _ =>
          (if nl then emitStr "\n" else Pure.pure PUnit.unit)) := by
    rw [h0, ht]
  rw [he]
  exact Emits.seq hE (Emits.seq (emits_emit _ c') (emits_nl nl c'))

/-- The `true`/`false` code, as bytes. These are the bytes the *source*
renders a boolean to as well, which is the whole content of the `print`
case for booleans. -/
def trueBytes : List UInt8 := "true".toUTF8.toList
def falseBytes : List UInt8 := "false".toUTF8.toList

theorem toString_true : toString true = "true" := rfl
theorem toString_false : toString false = "false" := rfl

theorem emitsS_printExpr_bool {ctx : Frame} {e : Expr} {c c' : Nat} {ce : List Instr}
    (ht : inferExpr ctx.types e = .ok Ty.bool) (nl : Bool)
    (hE : Emits (compileExpr ctx e) (c + 2) ce c' PUnit.unit) :
    Emits (compileStmt ctx (.printExpr e nl)) c
      (ce ++ ([Instr.jz (labelOf c)] ++ (bytesCode trueBytes ++
        ([Instr.jump (labelOf (c + 1)), Instr.label (labelOf c)] ++
          (bytesCode falseBytes ++ ([Instr.label (labelOf (c + 1))] ++ nlCode nl))))))
      c' PUnit.unit := by
  have h0 : compileStmt ctx (.printExpr e nl)
      = (match inferExpr ctx.types e with
         | .error m => throw s!"type error in a printed expression: {m}"
         | .ok .int => do
            compileExpr ctx e
            emit Instr.outNum
            if nl then emitStr "\n"
         | .ok .bool => do
            let f ← fresh
            let end_ ← fresh
            compileExpr ctx e
            emit (Instr.jz f)
            emitStr "true"
            emits [Instr.jump end_, Instr.label f]
            emitStr "false"
            emit (Instr.label end_)
            if nl then emitStr "\n"
         | .ok (.array _ _) => throw "internal: printing a whole array") := rfl
  have hd : compileStmt ctx (.printExpr e nl)
      = (fresh >>= fun f => fresh >>= fun end_ => compileExpr ctx e >>= fun _ =>
          emit (Instr.jz f) >>= fun _ => emitStr "true" >>= fun _ =>
            emits [Instr.jump end_, Instr.label f] >>= fun _ =>
              emitStr "false" >>= fun _ => emit (Instr.label end_) >>= fun _ =>
                (if nl then emitStr "\n" else Pure.pure PUnit.unit)) := by
    rw [h0, ht]
  rw [hd]
  have h1 := Emits.seq hE (Emits.seq (emits_emit (Instr.jz (labelOf c)) c')
    (Emits.seq (emits_emitStr "true" c') (Emits.seq
      (emits_emits [Instr.jump (labelOf (c + 1)), Instr.label (labelOf c)] c')
      (Emits.seq (emits_emitStr "false" c')
        (Emits.seq (emits_emit (Instr.label (labelOf (c + 1))) c') (emits_nl nl c'))))))
  have h2 := Emits.bind (g := fun end_ => compileExpr ctx e >>= fun _ =>
      emit (Instr.jz (labelOf c)) >>= fun _ => emitStr "true" >>= fun _ =>
        emits [Instr.jump end_, Instr.label (labelOf c)] >>= fun _ =>
          emitStr "false" >>= fun _ => emit (Instr.label end_) >>= fun _ =>
            (if nl then emitStr "\n" else Pure.pure PUnit.unit))
    (emits_fresh (c + 1)) h1
  have h3 := Emits.bind (g := fun f => fresh >>= fun end_ =>
      compileExpr ctx e >>= fun _ => emit (Instr.jz f) >>= fun _ =>
        emitStr "true" >>= fun _ =>
          emits [Instr.jump end_, Instr.label f] >>= fun _ =>
            emitStr "false" >>= fun _ => emit (Instr.label end_) >>= fun _ =>
              (if nl then emitStr "\n" else Pure.pure PUnit.unit))
    (emits_fresh c) h2
  simpa [trueBytes, falseBytes] using h3

/-! ### Cleanliness of the fixed tails -/

theorem clean_boolTail (mk : Label → Instr) (c : Nat)
    (hmk : labelIdxs [mk (labelOf c)] = []) :
    Clean c (c + 2) (boolTail (mk (labelOf c)) c) := by
  refine Clean.ofEq (ks := [c, c + 1]) ?_ ?_ ?_
  · have h : boolTail (mk (labelOf c)) c
        = [mk (labelOf c)] ++ ([Instr.push 0, Instr.jump (labelOf (c + 1))]
          ++ ([Instr.label (labelOf c)] ++ ([Instr.push 1]
            ++ [Instr.label (labelOf (c + 1))]))) := rfl
    rw [h]
    simp only [labelIdxs_append, hmk, labelIdxs_label, List.nil_append]
    rfl
  · intro k hk; simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with h | h <;> omega
  · simp

theorem clean_boolTail_jz (c : Nat) : Clean c (c + 2) (boolTail (Instr.jz (labelOf c)) c) :=
  clean_boolTail Instr.jz c rfl

theorem clean_boolTail_jn (c : Nat) : Clean c (c + 2) (boolTail (Instr.jn (labelOf c)) c) :=
  clean_boolTail Instr.jn c rfl

theorem clean_neTail (c : Nat) :
    Clean c (c + 2) [Instr.jz (labelOf c), Instr.push 1, Instr.jump (labelOf (c + 1)),
      Instr.label (labelOf c), Instr.push 0, Instr.label (labelOf (c + 1))] := by
  refine Clean.ofEq (ks := [c, c + 1]) ?_ ?_ ?_
  · simp [labelIdxs, labelsOf, unlabel_labelOf]
  · intro k hk; simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with h | h <;> omega
  · simp

theorem mem_of_contains {ns : List String} {x : String} (h : ns.contains x = true) :
    x ∈ ns := by simpa using h

/-! ### Every fragment expression emits something clean -/

theorem emitsExpr {ctx : Frame} {ns : List String} (hcov : Covers ctx ns) (e : Expr) :
    okExpr ns e = true → ∀ c : Nat,
      ∃ code c', Emits (compileExpr ctx e) c code c' PUnit.unit ∧ c ≤ c' ∧
        Clean c c' code := by
  induction e with
  | intLit n =>
    intro _ c
    exact ⟨_, c, emitsE_intLit ctx n c, Nat.le_refl c, Clean.ofNoLabels rfl⟩
  | boolLit b =>
    intro _ c
    exact ⟨_, c, emitsE_boolLit ctx b c, Nat.le_refl c, Clean.ofNoLabels rfl⟩
  | var x =>
    intro hok c
    obtain ⟨a, ha⟩ := hcov x (mem_of_contains (by simpa [okExpr] using hok))
    exact ⟨_, c, emitsE_var ha c, Nat.le_refl c, Clean.ofNoLabels rfl⟩
  | index x i => intro hok _; simp [okExpr] at hok
  | len x => intro hok _; simp [okExpr] at hok
  | un op e ih =>
    intro hok c
    obtain ⟨code, c', hE, hle, hcl⟩ := ih (by simpa [okExpr] using hok) c
    have hclean : Clean c c' ([Instr.push 0] ++ (code ++ [Instr.sub])) := by
      refine Clean.appendUp (Nat.le_refl c) hle (Clean.ofNoLabels rfl) ?_
      exact Clean.appendUp hle (Nat.le_refl c') hcl (Clean.ofNoLabels rfl)
    have hclean' : Clean c c' ([Instr.push 1] ++ (code ++ [Instr.sub])) := by
      refine Clean.appendUp (Nat.le_refl c) hle (Clean.ofNoLabels rfl) ?_
      exact Clean.appendUp hle (Nat.le_refl c') hcl (Clean.ofNoLabels rfl)
    cases op with
    | neg => exact ⟨_, c', emitsE_neg hE, hle, hclean⟩
    | not => exact ⟨_, c', emitsE_not hE, hle, hclean'⟩
  | bin op a b iha ihb =>
    intro hok c
    have hoka : okExpr ns a = true := by
      revert hok; simp only [okExpr, Bool.and_eq_true]; tauto
    have hokb : okExpr ns b = true := by
      revert hok; simp only [okExpr, Bool.and_eq_true]; tauto
    have hopok : okOp op = true := by
      revert hok; simp only [okExpr, Bool.and_eq_true]; tauto
    -- the shape shared by every operator that evaluates both operands in
    -- source order and then runs a fixed tail
    have straight : ∀ (tail : List Instr) (bump : Nat),
        (∀ (c₂ : Nat), Clean c₂ (c₂ + bump) tail) →
        (∀ (ca cb : List Instr) (c₁ c₂ : Nat),
          Emits (compileExpr ctx a) c ca c₁ PUnit.unit →
          Emits (compileExpr ctx b) c₁ cb c₂ PUnit.unit → True) → True := fun _ _ _ _ => trivial
    clear straight
    cases op with
    | div => simp [okOp] at hopok
    | mod => simp [okOp] at hopok
    | add =>
      obtain ⟨ca, c₁, hA, hleA, hclA⟩ := iha hoka c
      obtain ⟨cb, c₂, hB, hleB, hclB⟩ := ihb hokb c₁
      refine ⟨_, c₂, emitsE_arith (i := Instr.add) rfl hA hB, by omega, ?_⟩
      exact Clean.appendUp hleA hleB hclA
        (Clean.appendUp hleB (Nat.le_refl c₂) hclB (Clean.ofNoLabels rfl))
    | sub =>
      obtain ⟨ca, c₁, hA, hleA, hclA⟩ := iha hoka c
      obtain ⟨cb, c₂, hB, hleB, hclB⟩ := ihb hokb c₁
      refine ⟨_, c₂, emitsE_arith (i := Instr.sub) rfl hA hB, by omega, ?_⟩
      exact Clean.appendUp hleA hleB hclA
        (Clean.appendUp hleB (Nat.le_refl c₂) hclB (Clean.ofNoLabels rfl))
    | mul =>
      obtain ⟨ca, c₁, hA, hleA, hclA⟩ := iha hoka c
      obtain ⟨cb, c₂, hB, hleB, hclB⟩ := ihb hokb c₁
      refine ⟨_, c₂, emitsE_arith (i := Instr.mul) rfl hA hB, by omega, ?_⟩
      exact Clean.appendUp hleA hleB hclA
        (Clean.appendUp hleB (Nat.le_refl c₂) hclB (Clean.ofNoLabels rfl))
    | eq =>
      obtain ⟨ca, c₁, hA, hleA, hclA⟩ := iha hoka c
      obtain ⟨cb, c₂, hB, hleB, hclB⟩ := ihb hokb c₁
      refine ⟨_, c₂ + 2, emitsE_cmp (mk := Instr.jz) rfl hA hB, by omega, ?_⟩
      exact Clean.appendUp hleA (by omega) hclA
        (Clean.appendUp hleB (by omega) hclB
          (Clean.appendUp (Nat.le_refl c₂) (by omega) (Clean.ofNoLabels rfl)
            (clean_boolTail_jz c₂)))
    | lt =>
      obtain ⟨ca, c₁, hA, hleA, hclA⟩ := iha hoka c
      obtain ⟨cb, c₂, hB, hleB, hclB⟩ := ihb hokb c₁
      refine ⟨_, c₂ + 2, emitsE_cmp (mk := Instr.jn) rfl hA hB, by omega, ?_⟩
      exact Clean.appendUp hleA (by omega) hclA
        (Clean.appendUp hleB (by omega) hclB
          (Clean.appendUp (Nat.le_refl c₂) (by omega) (Clean.ofNoLabels rfl)
            (clean_boolTail_jn c₂)))
    | gt =>
      obtain ⟨cb, c₁, hB, hleB, hclB⟩ := ihb hokb c
      obtain ⟨ca, c₂, hA, hleA, hclA⟩ := iha hoka c₁
      refine ⟨_, c₂ + 2, emitsE_cmp (mk := Instr.jn) rfl hB hA, by omega, ?_⟩
      exact Clean.appendUp hleB (by omega) hclB
        (Clean.appendUp hleA (by omega) hclA
          (Clean.appendUp (Nat.le_refl c₂) (by omega) (Clean.ofNoLabels rfl)
            (clean_boolTail_jn c₂)))
    | le =>
      obtain ⟨ca, c₁, hA, hleA, hclA⟩ := iha hoka c
      obtain ⟨cb, c₂, hB, hleB, hclB⟩ := ihb hokb c₁
      refine ⟨_, c₂ + 2, emitsE_cmpLe (mk := Instr.jn) rfl hA hB, by omega, ?_⟩
      exact Clean.appendUp hleA (by omega) hclA
        (Clean.appendUp hleB (by omega) hclB
          (Clean.appendUp (Nat.le_refl c₂) (by omega) (Clean.ofNoLabels rfl)
            (clean_boolTail_jn c₂)))
    | ge =>
      obtain ⟨cb, c₁, hB, hleB, hclB⟩ := ihb hokb c
      obtain ⟨ca, c₂, hA, hleA, hclA⟩ := iha hoka c₁
      refine ⟨_, c₂ + 2, emitsE_cmpLe (mk := Instr.jn) rfl hB hA, by omega, ?_⟩
      exact Clean.appendUp hleB (by omega) hclB
        (Clean.appendUp hleA (by omega) hclA
          (Clean.appendUp (Nat.le_refl c₂) (by omega) (Clean.ofNoLabels rfl)
            (clean_boolTail_jn c₂)))
    | ne =>
      obtain ⟨ca, c₁, hA, hleA, hclA⟩ := iha hoka c
      obtain ⟨cb, c₂, hB, hleB, hclB⟩ := ihb hokb c₁
      refine ⟨_, c₂ + 2, emitsE_ne hA hB, by omega, ?_⟩
      exact Clean.appendUp hleA (by omega) hclA
        (Clean.appendUp hleB (by omega) hclB
          (Clean.appendUp (Nat.le_refl c₂) (by omega) (Clean.ofNoLabels rfl)
            (clean_neTail c₂)))
    | and =>
      obtain ⟨ca, c₁, hA, hleA, hclA⟩ := iha hoka (c + 1)
      obtain ⟨cb, c₂, hB, hleB, hclB⟩ := ihb hokb c₁
      refine ⟨_, c₂, emitsE_and hA hB, by omega, ?_⟩
      refine Clean.ofEq (ks := labelIdxs ca ++ (labelIdxs cb ++ [c])) ?_ ?_ ?_
      · simp only [labelIdxs_append, labelIdxs_label]
        rfl
      · intro k hk
        rcases List.mem_append.mp hk with hm | hm
        · have := hclA.bounds k hm; omega
        · rcases List.mem_append.mp hm with hm' | hm'
          · have := hclB.bounds k hm'; omega
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm'; omega
      · refine nodup_app hclA.nodup (nodup_app hclB.nodup (by simp) ?_) ?_
        · intro k h1 h2
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
          have := hclB.bounds k h1; omega
        · intro k h1 h2
          have := hclA.bounds k h1
          rcases List.mem_append.mp h2 with hm | hm
          · have := hclB.bounds k hm; omega
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm; omega
    | or =>
      obtain ⟨ca, c₁, hA, hleA, hclA⟩ := iha hoka (c + 2)
      obtain ⟨cb, c₂, hB, hleB, hclB⟩ := ihb hokb c₁
      refine ⟨_, c₂, emitsE_or hA hB, by omega, ?_⟩
      refine Clean.ofEq (ks := labelIdxs ca ++ ([c] ++ (labelIdxs cb ++ [c + 1]))) ?_ ?_ ?_
      · have hmid : labelIdxs [Instr.jz (labelOf c), Instr.push 1,
            Instr.jump (labelOf (c + 1)), Instr.label (labelOf c)] = [c] := by
          simp [labelIdxs, labelsOf, unlabel_labelOf]
        simp only [labelIdxs_append, labelIdxs_label, hmid]
      · intro k hk
        rcases List.mem_append.mp hk with hm | hm
        · have := hclA.bounds k hm; omega
        · rcases List.mem_append.mp hm with hm' | hm'
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm'; omega
          · rcases List.mem_append.mp hm' with hm'' | hm''
            · have := hclB.bounds k hm''; omega
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm''; omega
      · refine nodup_app hclA.nodup
          (nodup_app (by simp) (nodup_app hclB.nodup (by simp) ?_) ?_) ?_
        · intro k h1 h2
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
          have := hclB.bounds k h1; omega
        · intro k h1 h2
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h1
          rcases List.mem_append.mp h2 with hm | hm
          · have := hclB.bounds k hm; omega
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm; omega
        · intro k h1 h2
          have := hclA.bounds k h1
          rcases List.mem_append.mp h2 with hm | hm
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm; omega
          · rcases List.mem_append.mp hm with hm' | hm'
            · have := hclB.bounds k hm'; omega
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm'; omega



/-! ## Running the fixed tails

The comparison operators all end in the same six instructions: a conditional
jump, and the two constants it selects between. These lemmas run that tail
once and for all. -/

theorem reaches_cast {prog : Prog} {labels : Std.HashMap Label Nat}
    {s t t' : Whitespace.State} (h : Reaches (Whitespace.exec prog labels) s t)
    (he : t = t') : Reaches (Whitespace.exec prog labels) s t' := he ▸ h

theorem CodeAt.head {prog : Prog} {p : Nat} {i : Instr} {rest : List Instr}
    (h : CodeAt prog p (i :: rest)) : prog[p]? = some i := by
  have := h.get 0 (by simp)
  simpa using this

theorem CodeAt.right' {prog : Prog} {p q : Nat} {c₁ c₂ : List Instr}
    (h : CodeAt prog p (c₁ ++ c₂)) (hq : p + c₁.length = q) : CodeAt prog q c₂ := hq ▸ h.right

theorem LabelsOk.right' {labels : Std.HashMap Label Nat} {p q : Nat} {c₁ c₂ : List Instr}
    (h : LabelsOk labels p (c₁ ++ c₂)) (hq : p + c₁.length = q) :
    LabelsOk labels q c₂ := hq ▸ h.right

theorem LabelsOk.single {labels : Std.HashMap Label Nat} {p : Nat} {l : Label}
    (h : LabelsOk labels p [Instr.label l]) : labels[l]? = some (p + 1) := by
  have := h 0 l rfl
  simpa using this

theorem reaches_outChar (s : Whitespace.State) (n : Int) (st : List Int)
    (hst : s.stack = n :: st) (hlo : 0 ≤ n) (hhi : n ≤ 255)
    (h : prog[s.pc]? = some Instr.outChar) :
    Reaches (Whitespace.exec prog labels) s
      ({ s with pc := s.pc + 1, stack := st }.emit n.toNat.toUInt8) :=
  Reaches.one fun _ => by
    simp only [Whitespace.exec, h, hst]
    rw [if_pos (by simp [hlo, hhi] : (0 ≤ n && n ≤ 255) = true)]

example (b : UInt8) : (Int.ofNat b.toNat).toNat.toUInt8 = b := by simp

/-- **Printing a run of bytes.** The code `emitStr` emits walks the list,
pushing each byte and printing it, and leaves the stack as it found it. The
output it appends is not named: the caller recovers it from the trace. -/
theorem reaches_bytesCode (bs : List UInt8) (s : Whitespace.State)
    (hcode : CodeAt prog s.pc (bytesCode bs)) :
    ∃ out', out'.toList = s.output.toList ++ bs ∧
      Reaches (Whitespace.exec prog labels) s
        { s with pc := s.pc + 2 * bs.length, output := out',
                 events := Trace.recOut s.events bs } := by
  induction bs generalizing s with
  | nil => exact ⟨s.output, by simp, by simpa [Trace.recOut] using Reaches.refl _ s⟩
  | cons b bs ih =>
    have hc : CodeAt prog s.pc
        ([Instr.push (Int.ofNat b.toNat), Instr.outChar] ++ bytesCode bs) :=
      codeAt_of_eq hcode (by simp [bytesCode])
    have hb : (b.toNat : Int) ≤ 255 := by
      have := b.toNat_lt_size; simp [UInt8.size] at this; omega
    have step1 := reaches_push (prog := prog) (labels := labels) s
      (Int.ofNat b.toNat) hc.head
    have step2 : Reaches (Whitespace.exec prog labels)
        { s with pc := s.pc + 1, stack := (Int.ofNat b.toNat) :: s.stack }
        ({ s with pc := s.pc + 1 + 1 }.emit b) := by
      refine reaches_cast (reaches_outChar (prog := prog) (labels := labels)
        { s with pc := s.pc + 1, stack := (Int.ofNat b.toNat) :: s.stack }
        (Int.ofNat b.toNat) s.stack rfl (by simp) hb
        ((hc.right' (c₁ := [Instr.push (Int.ofNat b.toNat)]) (by simp)).head)) ?_
      simp [Whitespace.State.emit]
    obtain ⟨out', hout, hr⟩ := ih ({ s with pc := s.pc + 1 + 1 }.emit b)
      (by
        have := hc.right' (c₁ := [Instr.push (Int.ofNat b.toNat), Instr.outChar]) rfl
        simpa [Whitespace.State.emit] using this)
    refine ⟨out', by simpa [Whitespace.State.emit] using hout,
      reaches_cast (Reaches.trans step1 (Reaches.trans step2 hr)) ?_⟩
    simp only [Whitespace.State.emit, Whitespace.State.mk.injEq, Trace.recOut,
      List.foldl_cons, List.length_cons, true_and, and_true]
    omega

theorem reaches_boolTail {prog : Prog} {labels : Std.HashMap Label Nat}
    (mk : Label → Instr) (taken : Prop) [Decidable taken]
    (s : Whitespace.State) (z : Int) (st : List Int) (c : Nat)
    (hst : s.stack = z :: st)
    (hstep : ∀ (t : Whitespace.State) (p' : Nat), t.stack = z :: st →
      labels[labelOf c]? = some p' → prog[t.pc]? = some (mk (labelOf c)) →
      Reaches (Whitespace.exec prog labels) t
        (if taken then { t with pc := p', stack := st }
         else { t with pc := t.pc + 1, stack := st }))
    (hcode : CodeAt prog s.pc (boolTail (mk (labelOf c)) c))
    (hlab : LabelsOk labels s.pc (boolTail (mk (labelOf c)) c)) :
    Reaches (Whitespace.exec prog labels) s
      { s with pc := s.pc + 6, stack := (if taken then 1 else 0) :: st } := by
  have h0 : prog[s.pc]? = some (mk (labelOf c)) := by
    have := hcode.get 0 (by simp [boolTail]); simpa [boolTail] using this
  have h1 : prog[s.pc + 1]? = some (Instr.push 0) := by
    have := hcode.get 1 (by simp [boolTail]); simpa [boolTail] using this
  have h2 : prog[s.pc + 2]? = some (Instr.jump (labelOf (c + 1))) := by
    have := hcode.get 2 (by simp [boolTail]); simpa [boolTail] using this
  have h4 : prog[s.pc + 4]? = some (Instr.push 1) := by
    have := hcode.get 4 (by simp [boolTail]); simpa [boolTail] using this
  have h5 : prog[s.pc + 5]? = some (Instr.label (labelOf (c + 1))) := by
    have := hcode.get 5 (by simp [boolTail]); simpa [boolTail] using this
  have hL : labels[labelOf c]? = some (s.pc + 4) := by
    have := hlab 3 (labelOf c) rfl; simpa using this
  have hE : labels[labelOf (c + 1)]? = some (s.pc + 6) := by
    have := hlab 5 (labelOf (c + 1)) rfl; simpa using this
  by_cases ht : taken
  · have step1 := hstep s (s.pc + 4) hst hL h0
    rw [if_pos ht] at step1
    have step2 := reaches_push (prog := prog) (labels := labels)
      { s with pc := s.pc + 4, stack := st } 1 (by simpa using h4)
    have step3 := reaches_label (prog := prog) (labels := labels)
      { s with pc := s.pc + 4 + 1, stack := (1 : Int) :: st } (labelOf (c + 1))
      (by simpa using h5)
    refine reaches_cast (Reaches.trans step1 (Reaches.trans step2 step3)) ?_
    rw [if_pos ht]
  · have step1 := hstep s (s.pc + 4) hst hL h0
    rw [if_neg ht] at step1
    have step2 := reaches_push (prog := prog) (labels := labels)
      { s with pc := s.pc + 1, stack := st } 0 (by simpa using h1)
    have step3 := reaches_jump (prog := prog) (labels := labels)
      { s with pc := s.pc + 1 + 1, stack := (0 : Int) :: st } (labelOf (c + 1))
      (s.pc + 6) hE (by simpa using h2)
    refine reaches_cast (Reaches.trans step1 (Reaches.trans step2 step3)) ?_
    rw [if_neg ht]

theorem reaches_boolTail_jz {prog : Prog} {labels : Std.HashMap Label Nat}
    (s : Whitespace.State) (z : Int) (st : List Int) (c : Nat)
    (hst : s.stack = z :: st)
    (hcode : CodeAt prog s.pc (boolTail (Instr.jz (labelOf c)) c))
    (hlab : LabelsOk labels s.pc (boolTail (Instr.jz (labelOf c)) c)) :
    Reaches (Whitespace.exec prog labels) s
      { s with pc := s.pc + 6, stack := (if z = 0 then 1 else 0) :: st } := by
  refine reaches_boolTail Instr.jz (z = 0) s z st c hst ?_ hcode hlab
  intro t p' htst hl hi
  by_cases hz : z = 0
  · rw [if_pos hz]
    exact reaches_jz_taken t st (labelOf c) p' (by rw [htst, hz]) hl hi
  · rw [if_neg hz]
    exact reaches_jz_untaken t st (labelOf c) z hz htst hi

theorem reaches_boolTail_jn {prog : Prog} {labels : Std.HashMap Label Nat}
    (s : Whitespace.State) (z : Int) (st : List Int) (c : Nat)
    (hst : s.stack = z :: st)
    (hcode : CodeAt prog s.pc (boolTail (Instr.jn (labelOf c)) c))
    (hlab : LabelsOk labels s.pc (boolTail (Instr.jn (labelOf c)) c)) :
    Reaches (Whitespace.exec prog labels) s
      { s with pc := s.pc + 6, stack := (if z < 0 then 1 else 0) :: st } := by
  refine reaches_boolTail Instr.jn (z < 0) s z st c hst ?_ hcode hlab
  intro t p' htst hl hi
  by_cases hz : z < 0
  · rw [if_pos hz]
    exact reaches_jn_taken t z st (labelOf c) p' hz htst hl hi
  · rw [if_neg hz]
    exact reaches_jn_untaken t z st (labelOf c) hz htst hi

/-- `!=` uses the same six instructions with the two constants exchanged. -/
theorem reaches_neTail {prog : Prog} {labels : Std.HashMap Label Nat}
    (s : Whitespace.State) (z : Int) (st : List Int) (c : Nat)
    (hst : s.stack = z :: st)
    (hcode : CodeAt prog s.pc [Instr.jz (labelOf c), Instr.push 1,
      Instr.jump (labelOf (c + 1)), Instr.label (labelOf c), Instr.push 0,
      Instr.label (labelOf (c + 1))])
    (hlab : LabelsOk labels s.pc [Instr.jz (labelOf c), Instr.push 1,
      Instr.jump (labelOf (c + 1)), Instr.label (labelOf c), Instr.push 0,
      Instr.label (labelOf (c + 1))]) :
    Reaches (Whitespace.exec prog labels) s
      { s with pc := s.pc + 6, stack := (if z = 0 then 0 else 1) :: st } := by
  have h0 : prog[s.pc]? = some (Instr.jz (labelOf c)) := by
    have := hcode.get 0 (by simp); simpa using this
  have h1 : prog[s.pc + 1]? = some (Instr.push 1) := by
    have := hcode.get 1 (by simp); simpa using this
  have h2 : prog[s.pc + 2]? = some (Instr.jump (labelOf (c + 1))) := by
    have := hcode.get 2 (by simp); simpa using this
  have h4 : prog[s.pc + 4]? = some (Instr.push 0) := by
    have := hcode.get 4 (by simp); simpa using this
  have h5 : prog[s.pc + 5]? = some (Instr.label (labelOf (c + 1))) := by
    have := hcode.get 5 (by simp); simpa using this
  have hL : labels[labelOf c]? = some (s.pc + 4) := by
    have := hlab 3 (labelOf c) rfl; simpa using this
  have hE : labels[labelOf (c + 1)]? = some (s.pc + 6) := by
    have := hlab 5 (labelOf (c + 1)) rfl; simpa using this
  by_cases hz : z = 0
  · have step1 := reaches_jz_taken (prog := prog) (labels := labels) s st (labelOf c)
      (s.pc + 4) (by rw [hst, hz]) hL h0
    have step2 := reaches_push (prog := prog) (labels := labels)
      { s with pc := s.pc + 4, stack := st } 0 (by simpa using h4)
    have step3 := reaches_label (prog := prog) (labels := labels)
      { s with pc := s.pc + 4 + 1, stack := (0 : Int) :: st } (labelOf (c + 1))
      (by simpa using h5)
    refine reaches_cast (Reaches.trans step1 (Reaches.trans step2 step3)) ?_
    rw [if_pos hz]
  · have step1 := reaches_jz_untaken (prog := prog) (labels := labels) s st (labelOf c) z
      hz hst h0
    have step2 := reaches_push (prog := prog) (labels := labels)
      { s with pc := s.pc + 1, stack := st } 1 (by simpa using h1)
    have step3 := reaches_jump (prog := prog) (labels := labels)
      { s with pc := s.pc + 1 + 1, stack := (1 : Int) :: st } (labelOf (c + 1))
      (s.pc + 6) hE (by simpa using h2)
    refine reaches_cast (Reaches.trans step1 (Reaches.trans step2 step3)) ?_
    rw [if_neg hz]

/-! ## Inverting the reference evaluator

`evalExpr` evaluates a binary operator's operands and then combines them.
`evalBin` is that second half, split out so the case analysis over the
operators happens once. Each `_enc` lemma below says what the operator does
to the *encoded* values, which is exactly the shape the emitted code
computes. -/

theorem exc_pure {α : Type} (v : α) : (Pure.pure v : Except String α) = .ok v := rfl

theorem exc_throw {α : Type} (m : String) : (throw m : Except String α) = .error m := rfl

theorem exc_bind_ok {α β : Type} (v : α) (f : α → Except String β) :
    (Except.ok v >>= f) = f v := rfl

theorem exc_bind_err {α β : Type} (m : String) (f : α → Except String β) :
    ((Except.error m : Except String α) >>= f) = .error m := rfl

/-- The operators whose reference semantics evaluates both operands. -/
def straightOp : BinOp → Bool
  | .and | .or => false
  | _ => true

/-- The value-level half of `evalExpr` for a binary operator. -/
def evalBin (op : BinOp) (v₁ v₂ : Value) : Except String Value :=
  match v₁, v₂ with
  | .int a, .int b =>
    match op with
    | .add => return .int (a + b)
    | .sub => return .int (a - b)
    | .mul => return .int (a * b)
    | .div => if b == 0 then throw "division by zero" else return .int (a.ediv b)
    | .mod => if b == 0 then throw "modulo by zero" else return .int (a.emod b)
    | .eq => return .bool (a == b)
    | .ne => return .bool (a != b)
    | .lt => return .bool (a < b)
    | .le => return .bool (a ≤ b)
    | .gt => return .bool (a > b)
    | .ge => return .bool (a ≥ b)
    | _ => throw "ill-typed operation"
  | .bool a, .bool b =>
    match op with
    | .eq => return .bool (a == b)
    | .ne => return .bool (a != b)
    | _ => throw "ill-typed operation"
  | _, _ => throw "ill-typed operation"

theorem evalExpr_bin_eq (env : Std.HashMap String Value) (op : BinOp) (e₁ e₂ : Expr)
    (hop : straightOp op = true) :
    evalExpr env (.bin op e₁ e₂) =
      (evalExpr env e₁ >>= fun v₁ => evalExpr env e₂ >>= fun v₂ => evalBin op v₁ v₂) := by
  cases op <;> first | rfl | simp [straightOp] at hop

theorem evalExpr_bin_inv {env : Std.HashMap String Value} {op : BinOp} {e₁ e₂ : Expr}
    {v : Value} (hop : straightOp op = true) (h : evalExpr env (.bin op e₁ e₂) = .ok v) :
    ∃ v₁ v₂, evalExpr env e₁ = .ok v₁ ∧ evalExpr env e₂ = .ok v₂ ∧
      evalBin op v₁ v₂ = .ok v := by
  rw [evalExpr_bin_eq env op e₁ e₂ hop] at h
  cases h1 : evalExpr env e₁ with
  | error m => rw [h1, exc_bind_err] at h; simp at h
  | ok v₁ =>
    cases h2 : evalExpr env e₂ with
    | error m => rw [h1, h2, exc_bind_ok, exc_bind_err] at h; simp at h
    | ok v₂ =>
      rw [h1, h2, exc_bind_ok, exc_bind_ok] at h
      exact ⟨v₁, v₂, rfl, rfl, h⟩

theorem evalExpr_and_eq (env : Std.HashMap String Value) (e₁ e₂ : Expr) :
    evalExpr env (.bin .and e₁ e₂) =
      (evalExpr env e₁ >>= fun v₁ =>
        match v₁ with
        | .bool false => .ok (.bool false)
        | .bool true => evalExpr env e₂
        | _ => .error "ill-typed '&&'") := rfl

theorem evalExpr_or_eq (env : Std.HashMap String Value) (e₁ e₂ : Expr) :
    evalExpr env (.bin .or e₁ e₂) =
      (evalExpr env e₁ >>= fun v₁ =>
        match v₁ with
        | .bool true => .ok (.bool true)
        | .bool false => evalExpr env e₂
        | _ => .error "ill-typed '||'") := rfl

theorem evalExpr_var_inv {env : Std.HashMap String Value} {x : String} {v : Value}
    (h : evalExpr env (.var x) = .ok v) : env[x]? = some v := by
  rw [evalExpr] at h
  cases hw : env[x]? with
  | none => rw [hw] at h; simp at h
  | some w =>
    rw [hw] at h
    simp only [exc_pure, Except.ok.injEq] at h
    rw [h]

theorem evalExpr_neg_inv {env : Std.HashMap String Value} {e : Expr} {v : Value}
    (h : evalExpr env (.un .neg e) = .ok v) :
    ∃ w, evalExpr env e = .ok w ∧ encV v = 0 - encV w := by
  rw [evalExpr] at h
  cases he : evalExpr env e with
  | error m => rw [he, exc_bind_err] at h; simp at h
  | ok w =>
    rw [he, exc_bind_ok] at h
    cases w with
    | int n =>
      simp only [exc_pure, Except.ok.injEq] at h
      exact ⟨.int n, rfl, by rw [← h]; simp [encV]⟩
    | bool b => simp at h
    | arr a => simp at h

theorem evalExpr_not_inv {env : Std.HashMap String Value} {e : Expr} {v : Value}
    (h : evalExpr env (.un .not e) = .ok v) :
    ∃ w, evalExpr env e = .ok w ∧ encV v = 1 - encV w := by
  rw [evalExpr] at h
  cases he : evalExpr env e with
  | error m => rw [he, exc_bind_err] at h; simp at h
  | ok w =>
    rw [he, exc_bind_ok] at h
    cases w with
    | int n => simp at h
    | arr a => simp at h
    | bool b =>
      simp only [exc_pure, Except.ok.injEq] at h
      refine ⟨.bool b, rfl, ?_⟩
      rw [← h]; cases b <;> simp [encV]

/-! ### What each operator does to the encoded values -/

theorem encV_bool_eq_ite (b : Bool) (P : Prop) [Decidable P] (h : b = true ↔ P) :
    encV (.bool b) = if P then 1 else 0 := by
  by_cases hP : P
  · rw [if_pos hP, h.mpr hP]; rfl
  · rw [if_neg hP]
    cases b
    · rfl
    · exact absurd (h.mp rfl) hP

theorem encV_bool_ne_ite (b : Bool) (P : Prop) [Decidable P] (h : b = true ↔ P) :
    encV (.bool !b) = if P then 0 else 1 := by
  by_cases hP : P
  · rw [if_pos hP, h.mpr hP]; rfl
  · rw [if_neg hP]
    cases b
    · rfl
    · exact absurd (h.mp rfl) hP

theorem encV_bool_sub_eq_zero (a b : Bool) :
    (encV (.bool a) - encV (.bool b) = 0) ↔ (a = b) := by
  cases a <;> cases b <;> simp [encV]

theorem evalBin_add_enc {v₁ v₂ v : Value} (h : evalBin .add v₁ v₂ = .ok v) :
    encV v = encV v₁ + encV v₂ := by
  cases v₁ <;> cases v₂ <;>
    simp only [evalBin, exc_pure, exc_throw, reduceCtorEq, Except.ok.injEq] at h
  subst h; simp [encV]

theorem evalBin_sub_enc {v₁ v₂ v : Value} (h : evalBin .sub v₁ v₂ = .ok v) :
    encV v = encV v₁ - encV v₂ := by
  cases v₁ <;> cases v₂ <;>
    simp only [evalBin, exc_pure, exc_throw, reduceCtorEq, Except.ok.injEq] at h
  subst h; simp [encV]

theorem evalBin_mul_enc {v₁ v₂ v : Value} (h : evalBin .mul v₁ v₂ = .ok v) :
    encV v = encV v₁ * encV v₂ := by
  cases v₁ <;> cases v₂ <;>
    simp only [evalBin, exc_pure, exc_throw, reduceCtorEq, Except.ok.injEq] at h
  subst h; simp [encV]

theorem evalBin_lt_enc {v₁ v₂ v : Value} (h : evalBin .lt v₁ v₂ = .ok v) :
    encV v = (if encV v₁ - encV v₂ < 0 then 1 else 0) := by
  cases v₁ <;> cases v₂ <;>
    simp only [evalBin, exc_pure, exc_throw, reduceCtorEq, Except.ok.injEq] at h
  subst h
  exact encV_bool_eq_ite _ _ (by simp only [decide_eq_true_eq, encV]; omega)

theorem evalBin_le_enc {v₁ v₂ v : Value} (h : evalBin .le v₁ v₂ = .ok v) :
    encV v = (if encV v₁ - encV v₂ - 1 < 0 then 1 else 0) := by
  cases v₁ <;> cases v₂ <;>
    simp only [evalBin, exc_pure, exc_throw, reduceCtorEq, Except.ok.injEq] at h
  subst h
  exact encV_bool_eq_ite _ _ (by simp only [decide_eq_true_eq, encV]; omega)

theorem evalBin_gt_enc {v₁ v₂ v : Value} (h : evalBin .gt v₁ v₂ = .ok v) :
    encV v = (if encV v₂ - encV v₁ < 0 then 1 else 0) := by
  cases v₁ <;> cases v₂ <;>
    simp only [evalBin, exc_pure, exc_throw, reduceCtorEq, Except.ok.injEq] at h
  subst h
  exact encV_bool_eq_ite _ _ (by simp only [decide_eq_true_eq, encV]; omega)

theorem evalBin_ge_enc {v₁ v₂ v : Value} (h : evalBin .ge v₁ v₂ = .ok v) :
    encV v = (if encV v₂ - encV v₁ - 1 < 0 then 1 else 0) := by
  cases v₁ <;> cases v₂ <;>
    simp only [evalBin, exc_pure, exc_throw, reduceCtorEq, Except.ok.injEq] at h
  subst h
  exact encV_bool_eq_ite _ _ (by simp only [decide_eq_true_eq, encV]; omega)

theorem evalBin_eq_enc {v₁ v₂ v : Value} (h : evalBin .eq v₁ v₂ = .ok v) :
    encV v = (if encV v₁ - encV v₂ = 0 then 1 else 0) := by
  cases v₁ <;> cases v₂ <;>
    simp only [evalBin, exc_pure, exc_throw, reduceCtorEq, Except.ok.injEq] at h <;>
    subst h <;> refine encV_bool_eq_ite _ _ ?_ <;>
    first
      | (simp only [beq_iff_eq, encV]; omega)
      | (simp only [beq_iff_eq, encV_bool_sub_eq_zero])

theorem evalBin_ne_enc {v₁ v₂ v : Value} (h : evalBin .ne v₁ v₂ = .ok v) :
    encV v = (if encV v₁ - encV v₂ = 0 then 0 else 1) := by
  cases v₁ <;> cases v₂ <;>
    simp only [evalBin, exc_pure, exc_throw, reduceCtorEq, Except.ok.injEq] at h <;>
    subst h <;> refine encV_bool_ne_ite _ _ ?_ <;>
    first
      | (simp only [beq_iff_eq, encV]; omega)
      | (simp only [beq_iff_eq, encV_bool_sub_eq_zero])



/-! ### The static type is the runtime type

`print` is compiled from the expression's *static* type and interpreted
from the *runtime* value, so the two have to agree. On this fragment they
do, and for two different reasons depending on the expression.

Most of the work is done by the reference semantics itself: `evalBin`
throws on operands of the wrong shape, so an addition that produced a value
at all produced an integer, and a comparison a boolean, whatever the
context said. Only three forms need more. A variable's runtime type comes
from `Agrees`, which is why the invariant carries it; `&&` and `||` return
their right operand, so they need the induction hypothesis; and everything
else the fragment admits is a literal. -/

/-- `Ty`'s derived `BEq` is sound. It has no `LawfulBEq` instance, and
`inferExpr` compares types with `==`, so this is what lets a successful
inference be read as an equation. -/
theorem ty_of_beq : ∀ {a b : Ty}, (a == b) = true → a = b := by
  intro a
  induction a with
  | int => intro b h; cases b <;> first | rfl | exact Bool.noConfusion h
  | bool => intro b h; cases b <;> first | rfl | exact Bool.noConfusion h
  | array e n ih =>
    intro b h
    cases b
    · exact Bool.noConfusion h
    · exact Bool.noConfusion h
    · rename_i e' n'
      have h' : ((e == e') && (n == n')) = true := h
      rw [Bool.and_eq_true] at h'
      rw [ih h'.1, show n = n' from by simpa using h'.2]

/-- The type an operator's result has, when it has one. -/
def binResultTy : BinOp → Ty
  | .add | .sub | .mul | .div | .mod => .int
  | _ => .bool

theorem evalBin_hasTy {op : BinOp} {v₁ v₂ w : Value} (h : evalBin op v₁ v₂ = .ok w) :
    valHasTy w (binResultTy op) = true := by
  have close : ∀ {u : Value}, (Pure.pure u : Except String Value) = .ok w →
      valHasTy u (binResultTy op) = valHasTy w (binResultTy op) := by
    intro u hu; rw [exc_pure, Except.ok.injEq] at hu; rw [hu]
  cases v₁ <;> cases v₂ <;> cases op <;> (try rw [evalBin] at h) <;> (try split at h) <;>
    first
      | (rw [← close h]; rfl)
      | simp at h
      | simp

theorem inferExpr_bin_ty {tys : Types} {op : BinOp} {a b : Expr} {te : Ty}
    (h : inferExpr tys (.bin op a b) = .ok te) : te = binResultTy op := by
  rw [inferExpr] at h
  cases h₁ : inferExpr tys a with
  | error m => rw [h₁, exc_bind_err] at h; simp at h
  | ok t₁ =>
    cases h₂ : inferExpr tys b with
    | error m => rw [h₁, h₂, exc_bind_ok, exc_bind_err] at h; simp at h
    | ok t₂ =>
      rw [h₁, h₂, exc_bind_ok, exc_bind_ok] at h
      cases op <;> simp_all [binResultTy, exc_pure, ite_eq_iff]

theorem inferExpr_un_ty {tys : Types} {op : UnOp} {e : Expr} {te : Ty}
    (h : inferExpr tys (.un op e) = .ok te) :
    (op = .neg ∧ te = .int) ∨ (op = .not ∧ te = .bool) := by
  rw [inferExpr] at h
  cases h₁ : inferExpr tys e with
  | error m => rw [h₁, exc_bind_err] at h; simp at h
  | ok t =>
    rw [h₁, exc_bind_ok] at h
    cases op <;> cases t <;> simp_all [exc_pure]

/-- **The static type is the runtime type.** -/
theorem evalExpr_hasTy {ctx : Frame} {ns : List String} (hcov : Covers ctx ns)
    {env : Std.HashMap String Value} {heap : Std.HashMap Int Int}
    (hag : Agrees ctx env heap) :
    ∀ (e : Expr) (te : Ty) (w : Value), okExpr ns e = true →
      inferExpr ctx.types e = .ok te → Turpentine.evalExpr env e = .ok w →
        valHasTy w te = true := by
  have pure_eq : ∀ {u v : Value}, (Pure.pure u : Except String Value) = .ok v → u = v := by
    intro u v hu; rw [exc_pure, Except.ok.injEq] at hu; exact hu
  intro e
  induction e with
  | intLit n =>
    intro te w _ hi he
    rw [show inferExpr ctx.types (.intLit n) = .ok Ty.int from rfl] at hi
    rw [show Turpentine.evalExpr env (.intLit n) = .ok (Value.int n) from rfl] at he
    rw [← Except.ok.inj hi, ← Except.ok.inj he]
    rfl
  | boolLit b =>
    intro te w _ hi he
    rw [show inferExpr ctx.types (.boolLit b) = .ok Ty.bool from rfl] at hi
    rw [show Turpentine.evalExpr env (.boolLit b) = .ok (Value.bool b) from rfl] at he
    rw [← Except.ok.inj hi, ← Except.ok.inj he]
    rfl
  | var x =>
    intro te w hok hi he
    obtain ⟨a, ha⟩ := hcov x (mem_of_contains (by simpa [okExpr] using hok))
    have hw : env[x]? = some w := evalExpr_var_inv he
    have hty : ctx.types[x]? = some te := by
      rw [inferExpr] at hi
      cases hx : ctx.types[x]? with
      | none => rw [hx] at hi; simp at hi
      | some tt => cases tt <;> simp_all [exc_pure]
    exact (hag x a ha w hw).2 te hty
  | index x i _ => intro _ _ hok _ _; simp [okExpr] at hok
  | len x => intro _ _ hok _ _; simp [okExpr] at hok
  | un op e _ =>
    intro te w _ hi he
    rcases inferExpr_un_ty hi with ⟨hop, hte⟩ | ⟨hop, hte⟩ <;> subst hop <;> subst hte <;>
      (rw [Turpentine.evalExpr] at he
       cases h₁ : Turpentine.evalExpr env e with
       | error m => rw [h₁, exc_bind_err] at he; simp at he
       | ok u =>
         rw [h₁, exc_bind_ok] at he
         cases u <;> first | (rw [← pure_eq he]; rfl) | simp at he)
  | bin op a b iha ihb =>
    intro te w hok hi he
    have hte : te = binResultTy op := inferExpr_bin_ty hi
    subst hte
    cases hst : straightOp op with
    | true =>
      obtain ⟨v₁, v₂, -, -, hb⟩ := evalExpr_bin_inv hst he
      exact evalBin_hasTy hb
    | false =>
      have hoo : op = .and ∨ op = .or := by
        cases op <;> simp_all [straightOp]
      have hokb : okExpr ns b = true := by
        revert hok; simp only [okExpr, Bool.and_eq_true]; tauto
      have hib : inferExpr ctx.types b = .ok Ty.bool := by
        rw [inferExpr] at hi
        cases h₁ : inferExpr ctx.types a with
        | error m => rw [h₁, exc_bind_err] at hi; simp at hi
        | ok t₁ =>
          cases h₂ : inferExpr ctx.types b with
          | error m => rw [h₁, h₂, exc_bind_ok, exc_bind_err] at hi; simp at hi
          | ok t₂ =>
            rw [h₁, h₂, exc_bind_ok, exc_bind_ok] at hi
            rcases hoo with hop | hop <;> subst hop <;>
              (simp only [exc_pure, ite_eq_iff, Bool.and_eq_true] at hi
               rcases hi with ⟨⟨hc₁, hc₂⟩, -⟩ | ⟨-, hc⟩
               · rw [ty_of_beq hc₂]
               · exact absurd hc (by simp))
      rcases hoo with hop | hop <;> subst hop
      · rw [evalExpr_and_eq] at he
        cases h₁ : Turpentine.evalExpr env a with
        | error m => rw [h₁, exc_bind_err] at he; simp at he
        | ok v₁ =>
          rw [h₁, exc_bind_ok] at he
          cases v₁ with
          | int m => simp at he
          | arr m => simp at he
          | bool b₁ =>
            cases b₁ with
            | false => simp only [] at he; rw [← Except.ok.inj he]; rfl
            | true => exact ihb _ w hokb hib he
      · rw [evalExpr_or_eq] at he
        cases h₁ : Turpentine.evalExpr env a with
        | error m => rw [h₁, exc_bind_err] at he; simp at he
        | ok v₁ =>
          rw [h₁, exc_bind_ok] at he
          cases v₁ with
          | int m => simp at he
          | arr m => simp at he
          | bool b₁ =>
            cases b₁ with
            | true => simp only [] at he; rw [← Except.ok.inj he]; rfl
            | false => exact ihb _ w hokb hib he

/-! ## Reading the compiler's own front matter

`compileChecked` computes the address map with a `for` loop and then runs the
generator with a second one. These two definitions are those loops written
recursively; `compileChecked_unfold` is the (definitional) bridge. -/

/-- The address loop's body, as a function. -/
def layoutBody : (String × Ty × Option Expr) → (Std.HashMap String Int × Int) →
    Except String (ForInStep (Std.HashMap String Int × Int)) :=
  fun d st => pure (ForInStep.yield (st.1.insert d.1 st.2, st.2 + (slotSize d.2.1 : Int)))

/-- The address loop, as a recursive function. -/
def layoutGo : List (String × Ty × Option Expr) →
    (Std.HashMap String Int × Int) → (Std.HashMap String Int × Int)
  | [], acc => acc
  | d :: rest, acc =>
      layoutGo rest (acc.1.insert d.1 acc.2, acc.2 + (slotSize d.2.1 : Int))

theorem layout_forIn (l : List (String × Ty × Option Expr)) :
    ∀ acc, forIn (m := Except String) l acc layoutBody = pure (layoutGo l acc) := by
  induction l with
  | nil => intro acc; rfl
  | cons d rest ih => intro acc; rw [List.forIn_cons]; exact ih _

/-- The generator loop's body, as a function. -/
def genBody (ctx : Frame) : (String × Ty × Option Expr) → PUnit → M (ForInStep PUnit) :=
  fun d _ => do
    let a ← addrOf ctx d.1
    match d.2.1, d.2.2 with
      | .array _ n, _ => do
        forIn [:n] PUnit.unit (fun (k : Nat) (_ : PUnit) => do
          emits [Instr.push (a + (k : Int)), Instr.push 0, Instr.store]
          pure (ForInStep.yield PUnit.unit))
        pure (ForInStep.yield PUnit.unit)
      | _, some e => do
        emit (Instr.push a)
        compileExpr ctx e
        emit Instr.store
        pure (ForInStep.yield PUnit.unit)
      | _, none => do
        emits [Instr.push a, Instr.push 0, Instr.store]
        pure (ForInStep.yield PUnit.unit)

/-- **The backend, spelled out.** Definitionally the same function; the two
`for` loops are now named so they can be reasoned about. -/
theorem compileChecked_unfold (p : Program) (types : Types) :
    compileChecked p types =
      (do
        let r ← forIn (m := Except String) p.decls ((∅ : Std.HashMap String Int), (0 : Int))
          layoutBody
        let hasArrays := p.decls.any fun d => match d.2.1 with
          | .array _ _ => true
          | _ => false
        let ctx : Frame :=
          { addrs := r.1, types := types, tmpA := r.2, tmpB := r.2 + 1, tmpI := r.2 + 2,
            oob := "S" }
        let gen : M Unit := do
          forIn (m := M) p.decls PUnit.unit (genBody ctx)
          compileStmt ctx p.body
          emit Instr.halt
          if hasArrays = true then emitOobTrap ctx else pure ()
        let x ← StateT.run gen {}
        pure x.2.out) := rfl

/-! ## The layout is a good frame -/

/-- Scalar types: the only ones the covered fragment declares. -/
def scalarTy : Ty → Bool
  | .int | .bool => true
  | .array _ _ => false

theorem slotSize_scalar {t : Ty} (h : scalarTy t = true) : slotSize t = 1 := by
  cases t <;> first | rfl | simp [scalarTy] at h

/-- Addresses are non-negative, below the next free one, and distinct. -/
structure LayoutOk (m : Std.HashMap String Int) (i : Int) : Prop where
  nonneg : 0 ≤ i
  bound : ∀ (x : String) (a : Int), m[x]? = some a → 0 ≤ a ∧ a < i
  injv : ∀ (x y : String) (a : Int), m[x]? = some a → m[y]? = some a → x = y

theorem layoutGo_notMem (l : List (String × Ty × Option Expr)) :
    ∀ (acc : Std.HashMap String Int × Int) (x : String), x ∉ l.map (·.1) →
      (layoutGo l acc).1[x]? = acc.1[x]? := by
  induction l with
  | nil => intro acc x _; rfl
  | cons d rest ih =>
    intro acc x hx
    simp only [List.map_cons, List.mem_cons, not_or] at hx
    rw [layoutGo, ih _ x hx.2, Std.HashMap.getElem?_insert,
      if_neg (by simpa using fun h => hx.1 h.symm)]

theorem layoutGo_ok (l : List (String × Ty × Option Expr))
    (hsc : ∀ d ∈ l, scalarTy d.2.1 = true) (hnd : (l.map (·.1)).Nodup) :
    ∀ (m : Std.HashMap String Int) (i : Int), LayoutOk m i →
      (∀ d ∈ l, m[d.1]? = none) →
      LayoutOk (layoutGo l (m, i)).1 (layoutGo l (m, i)).2 ∧
      (∀ x ∈ l.map (·.1), ∃ a, (layoutGo l (m, i)).1[x]? = some a) := by
  induction l with
  | nil => intro m i hok _; exact ⟨hok, by simp⟩
  | cons d rest ih =>
    intro m i hok hfresh
    have hsc' : ∀ e ∈ rest, scalarTy e.2.1 = true :=
      fun e he => hsc e (List.mem_cons_of_mem _ he)
    have hnd' : (rest.map (·.1)).Nodup := by
      simp only [List.map_cons, List.nodup_cons] at hnd; exact hnd.2
    have hdnot : d.1 ∉ rest.map (·.1) := by
      simp only [List.map_cons, List.nodup_cons] at hnd; exact hnd.1
    have hsize : slotSize d.2.1 = 1 := slotSize_scalar (hsc d (List.mem_cons_self ..))
    have hi0 : (0 : Int) ≤ i := hok.nonneg
    have hok' : LayoutOk (m.insert d.1 i) (i + (slotSize d.2.1 : Int)) := by
      refine ⟨by rw [hsize]; omega, ?_, ?_⟩
      · intro x a hx
        rw [Std.HashMap.getElem?_insert] at hx
        by_cases hxd : (d.1 == x) = true
        · rw [if_pos hxd] at hx
          have hai : a = i := (Option.some.inj hx).symm
          subst hai
          exact ⟨hi0, by rw [hsize]; omega⟩
        · rw [if_neg hxd] at hx
          obtain ⟨h1, h2⟩ := hok.bound x a hx
          exact ⟨h1, by rw [hsize]; omega⟩
      · intro x y a hx hy
        rw [Std.HashMap.getElem?_insert] at hx hy
        by_cases hxd : (d.1 == x) = true
        · by_cases hyd : (d.1 == y) = true
          · rw [← eq_of_beq hxd, ← eq_of_beq hyd]
          · rw [if_pos hxd] at hx
            rw [if_neg hyd] at hy
            have hai : a = i := (Option.some.inj hx).symm
            subst hai
            have := (hok.bound y a hy).2
            omega
        · by_cases hyd : (d.1 == y) = true
          · rw [if_neg hxd] at hx
            rw [if_pos hyd] at hy
            have hai : a = i := (Option.some.inj hy).symm
            subst hai
            have := (hok.bound x a hx).2
            omega
          · rw [if_neg hxd] at hx
            rw [if_neg hyd] at hy
            exact hok.injv x y a hx hy
    have hfresh' : ∀ e ∈ rest, (m.insert d.1 i)[e.1]? = none := by
      intro e he
      rw [Std.HashMap.getElem?_insert, if_neg ?ne]
      · exact hfresh e (List.mem_cons_of_mem _ he)
      case ne =>
        simp only [beq_iff_eq]
        intro hc
        exact hdnot (hc ▸ List.mem_map_of_mem he)
    obtain ⟨hokR, hcovR⟩ := ih hsc' hnd' (m.insert d.1 i) (i + (slotSize d.2.1 : Int))
      hok' hfresh'
    refine ⟨by rw [layoutGo]; exact hokR, ?_⟩
    intro x hx
    simp only [List.map_cons, List.mem_cons] at hx
    rcases hx with hx | hx
    · subst hx
      refine ⟨i, ?_⟩
      rw [layoutGo, layoutGo_notMem rest _ _ hdnot, Std.HashMap.getElem?_insert,
        if_pos (by simp)]
    · obtain ⟨a, hax⟩ := hcovR x hx
      exact ⟨a, by rw [layoutGo]; exact hax⟩

/-! ## The typing context the proof supplies

`bespokeWhitespace` does not run `Turpentine.checkProgram`: its own fragment
check subsumes what the backend needs from a typing context, which is one
lookup, `answer : int`, to pick the `outnum` branch of `print`. -/

def typesGo : List (String × Ty × Option Expr) → Std.HashMap String Ty →
    Std.HashMap String Ty
  | [], m => m
  | d :: rest, m => typesGo rest (m.insert d.1 d.2.1)

theorem typesGo_notMem (l : List (String × Ty × Option Expr)) :
    ∀ (m : Std.HashMap String Ty) (x : String), x ∉ l.map (·.1) →
      (typesGo l m)[x]? = m[x]? := by
  induction l with
  | nil => intro m x _; rfl
  | cons d rest ih =>
    intro m x hx
    simp only [List.map_cons, List.mem_cons, not_or] at hx
    rw [typesGo, ih _ x hx.2, Std.HashMap.getElem?_insert,
      if_neg (by simpa using fun h => hx.1 h.symm)]

theorem typesGo_get (l : List (String × Ty × Option Expr)) (hnd : (l.map (·.1)).Nodup) :
    ∀ (m : Std.HashMap String Ty) (d : String × Ty × Option Expr), d ∈ l →
      (typesGo l m)[d.1]? = some d.2.1 := by
  induction l with
  | nil => intro m d hd; simp at hd
  | cons e rest ih =>
    intro m d hd
    have hnd' : (rest.map (·.1)).Nodup := by
      simp only [List.map_cons, List.nodup_cons] at hnd; exact hnd.2
    have hdnot : e.1 ∉ rest.map (·.1) := by
      simp only [List.map_cons, List.nodup_cons] at hnd; exact hnd.1
    rcases List.mem_cons.mp hd with hd | hd
    · subst hd
      rw [typesGo, typesGo_notMem rest _ d.1 hdnot, Std.HashMap.getElem?_insert,
        if_pos (by simp)]
    · rw [typesGo]
      exact ih hnd' _ d hd


/-! ## The declaration prologue

Every declaration in the fragment starts at its type's default, `0` for an
`int` and `false` for a `bool`, and both encode as the heap cell `0`. So the
prologue's only job is to leave the heap all zeros, which is what
`ZeroHeap` records. -/

/-- Every heap cell reads as `0`. -/
def ZeroHeap (heap : Std.HashMap Int Int) : Prop := ∀ a : Int, heap.getD a 0 = 0

theorem zeroHeap_empty : ZeroHeap ∅ := by intro a; simp

theorem ZeroHeap.insertZero {heap : Std.HashMap Int Int} (h : ZeroHeap heap) (a : Int) :
    ZeroHeap (heap.insert a 0) := by
  intro b
  rw [Std.HashMap.getD_insert]
  split
  · rfl
  · exact h b

theorem emits_declLoop (ctx : Frame) (hg : GoodFrame ctx) :
    ∀ (l : List (String × Ty × Option Expr)),
      (∀ d ∈ l, scalarTy d.2.1 = true) → (∀ d ∈ l, d.2.2 = none) →
      (∀ d ∈ l, ∃ a, ctx.addrs[d.1]? = some a) →
      ∀ (c : Nat), ∃ code,
        Emits (forIn (m := M) l PUnit.unit (genBody ctx)) c code c PUnit.unit ∧
        labelIdxs code = [] ∧
        ∀ (prog : Prog) (labels : Std.HashMap Label Nat) (s : Whitespace.State),
          CodeAt prog s.pc code → ZeroHeap s.heap →
          ∃ heap', Reaches (Whitespace.exec prog labels) s
              { s with pc := s.pc + code.length, heap := heap' } ∧ ZeroHeap heap' := by
  intro l
  induction l with
  | nil =>
    intro _ _ _ c
    refine ⟨[], ?_, rfl, ?_⟩
    · rw [List.forIn_nil]; exact Emits.pure _ _
    · intro prog labels s _ hz
      exact ⟨s.heap, reaches_cast (Reaches.refl _ s) (by simp), hz⟩
  | cons d rest ih =>
    intro hsc hno hcv c
    obtain ⟨x, t, ini⟩ := d
    have hini : ini = none := hno (x, t, ini) (List.mem_cons_self ..)
    subst hini
    have hsct : scalarTy t = true := hsc (x, t, none) (List.mem_cons_self ..)
    obtain ⟨a, ha⟩ := hcv (x, t, none) (List.mem_cons_self ..)
    obtain ⟨rcode, hrem, hrl, hrsim⟩ := ih
      (fun e he => hsc e (List.mem_cons_of_mem _ he))
      (fun e he => hno e (List.mem_cons_of_mem _ he))
      (fun e he => hcv e (List.mem_cons_of_mem _ he)) c
    have hgb : Emits (genBody ctx (x, t, none) PUnit.unit) c
        [Instr.push a, Instr.push 0, Instr.store] c (ForInStep.yield PUnit.unit) := by
      have he : genBody ctx (x, t, none) PUnit.unit
          = (addrOf ctx x >>= fun a =>
              emits [Instr.push a, Instr.push 0, Instr.store] >>= fun _ =>
                (Pure.pure (ForInStep.yield PUnit.unit) : M (ForInStep PUnit))) := by
        cases t with
        | int => rfl
        | bool => rfl
        | array e n => simp [scalarTy] at hsct
      rw [he]
      have hc := Emits.bind (g := fun a =>
          emits [Instr.push a, Instr.push 0, Instr.store] >>= fun _ =>
            (Pure.pure (ForInStep.yield PUnit.unit) : M (ForInStep PUnit)))
        (emits_addrOf ha c)
        (Emits.seq (emits_emits [Instr.push a, Instr.push 0, Instr.store] c)
          (Emits.pure (ForInStep.yield PUnit.unit) c))
      simpa using hc
    refine ⟨[Instr.push a, Instr.push 0, Instr.store] ++ rcode, ?_, ?_, ?_⟩
    · rw [List.forIn_cons]
      exact Emits.bind hgb hrem
    · rw [labelIdxs_append, hrl]
      rfl
    · intro prog labels s hcode hz
      have h1 : prog[s.pc + 1]? = some (Instr.push 0) := by
        have := hcode.get 1 (by simp); simpa using this
      have h2 : prog[s.pc + 2]? = some Instr.store := by
        have := hcode.get 2 (by simp); simpa using this
      have hrest : CodeAt prog (s.pc + 3) rcode := by
        have hr := hcode.right' (c₁ := [Instr.push a, Instr.push 0, Instr.store])
          (q := s.pc + 3) (by simp)
        exact hr
      have step1 := reaches_push (prog := prog) (labels := labels) s a hcode.head
      have step2 := reaches_push (prog := prog) (labels := labels)
        { s with pc := s.pc + 1, stack := a :: s.stack } 0 (by simpa using h1)
      have step3 := reaches_store (prog := prog) (labels := labels)
        { s with pc := s.pc + 1 + 1, stack := (0 : Int) :: a :: s.stack }
        a 0 s.stack rfl (hg.nonneg x a ha) (by simpa using h2)
      obtain ⟨heap', r, hz'⟩ := hrsim prog labels
        { s with pc := s.pc + 3, heap := s.heap.insert a 0 } hrest (hz.insertZero a)
      refine ⟨heap', ?_, hz'⟩
      have chain : Reaches (Whitespace.exec prog labels) s
          { s with pc := s.pc + 3 + rcode.length, heap := heap' } :=
        Reaches.trans step1 (Reaches.trans step2 (Reaches.trans step3 r))
      rw [show s.pc + 3 + rcode.length
          = s.pc + ([Instr.push a, Instr.push 0, Instr.store] ++ rcode).length from by
        simp only [List.length_append, List.length_cons, List.length_nil]; omega] at chain
      exact chain

/-! ## The initial environment

`Turpentine.initEnv` evaluates the declarations' initialisers in order. The
fragment has none, so it just installs the defaults, and every default
encodes as `0`. -/

def initBody : (String × Ty × Option Expr) → Std.HashMap String Value →
    Except String (ForInStep (Std.HashMap String Value)) :=
  fun d env =>
    match d.2.2 with
    | some e => evalExpr env e >>= fun v => Pure.pure (ForInStep.yield (env.insert d.1 v))
    | none =>
      Pure.pure (ForInStep.yield (env.insert d.1 (Turpentine.initEnv.default d.2.1)))

theorem initEnv_unfold (p : Program) :
    Turpentine.initEnv p =
      (forIn (m := Except String) p.decls (∅ : Std.HashMap String Value) initBody >>=
        fun env => Pure.pure env) := rfl

def initGo : List (String × Ty × Option Expr) → Std.HashMap String Value →
    Std.HashMap String Value
  | [], env => env
  | d :: rest, env => initGo rest (env.insert d.1 (Turpentine.initEnv.default d.2.1))

theorem initEnv_forIn (l : List (String × Ty × Option Expr))
    (hno : ∀ d ∈ l, d.2.2 = none) :
    ∀ env, forIn (m := Except String) l env initBody = pure (initGo l env) := by
  induction l with
  | nil => intro env; rfl
  | cons d rest ih =>
    intro env
    obtain ⟨x, t, ini⟩ := d
    have hini : ini = none := hno (x, t, ini) (List.mem_cons_self ..)
    subst hini
    rw [List.forIn_cons]
    exact ih (fun e he => hno e (List.mem_cons_of_mem _ he)) _

/-- Every value in the environment encodes as the heap cell `0`. -/
def AllZeroEnv (env : Std.HashMap String Value) : Prop :=
  ∀ (x : String) (v : Value), env[x]? = some v → encV v = 0

theorem allZeroEnv_empty : AllZeroEnv ∅ := by intro x v h; simp at h

theorem encV_default (t : Ty) : encV (Turpentine.initEnv.default t) = 0 := by
  cases t <;> rfl

theorem initGo_zero (l : List (String × Ty × Option Expr)) :
    ∀ env, AllZeroEnv env → AllZeroEnv (initGo l env) := by
  induction l with
  | nil => intro env h; exact h
  | cons d rest ih =>
    intro env h
    refine ih _ ?_
    intro y w hy
    rw [Std.HashMap.getElem?_insert] at hy
    split at hy
    · rw [← Option.some.inj hy]
      exact encV_default d.2.1
    · exact h y w hy

theorem agrees_of_zero {ctx : Frame} {env : Std.HashMap String Value}
    {heap : Std.HashMap Int Int} (hz : ZeroHeap heap) (he : AllZeroEnv env)
    (ht : ∀ (x : String) (t : Ty) (v : Value),
      ctx.types[x]? = some t → env[x]? = some v → valHasTy v t = true) :
    Agrees ctx env heap := by
  intro x a _ v hv
  exact ⟨by rw [hz a, he x v hv], fun t htx => ht x t v htx hv⟩

/-- The declarations set every variable to the default of its declared
type, so the environment the prologue leaves behind is well typed. Both
folds walk the same list in the same order, which is the whole content of
the induction. -/
theorem initGo_typesGo (l : List (String × Ty × Option Expr)) :
    ∀ (env : Std.HashMap String Value) (tys : Types),
      (∀ (x : String) (t : Ty) (v : Value),
        tys[x]? = some t → env[x]? = some v → valHasTy v t = true) →
      ∀ (x : String) (t : Ty) (v : Value),
        (typesGo l tys)[x]? = some t → (initGo l env)[x]? = some v →
          valHasTy v t = true := by
  induction l with
  | nil => intro env tys h x t v ht hv; exact h x t v ht hv
  | cons d rest ih =>
    intro env tys h
    refine ih _ _ ?_
    intro x t v ht hv
    by_cases hx : x = d.1
    · subst hx
      rw [Std.HashMap.getElem?_insert, if_pos (by simp)] at ht hv
      rw [← Option.some.inj ht, ← Option.some.inj hv]
      exact valHasTy_default _
    · rw [Std.HashMap.getElem?_insert, if_neg (by simpa using Ne.symm hx)] at ht hv
      exact h x t v ht hv

/-! ## The simulation, for expressions

`R` is `Agrees`: the heap holds each variable's value. An expression's code
runs from a stack-empty-enough state and leaves exactly one extra value on
the stack, the encoding of what the reference evaluator returns; nothing else
about the machine changes. -/

/-- The simulation property for one expression, as a named predicate: the
statement is long and it appears three times. -/
def SimE (ctx : Frame) (prog : Prog) (labels : Std.HashMap Label Nat) (e : Expr) : Prop :=
  ∀ (c : Nat) (code : List Instr) (c' : Nat),
    Emits (compileExpr ctx e) c code c' PUnit.unit →
    ∀ (s : Whitespace.State),
      CodeAt prog s.pc code → LabelsOk labels s.pc code →
      ∀ (env : Std.HashMap String Value) (v : Value),
        evalExpr env e = .ok v → Agrees ctx env s.heap →
        Reaches (Whitespace.exec prog labels) s
          { s with pc := s.pc + code.length, stack := encV v :: s.stack }

theorem boolTail_length (t : Instr) (c : Nat) : (boolTail t c).length = 6 := rfl

/-- Both operands of a non-short-circuit operator, left one first: the code
leaves them on the stack in that order. -/
theorem sim_twoOps {ctx : Frame} {prog : Prog} {labels : Std.HashMap Label Nat}
    {e₁ e₂ : Expr} (h₁ : SimE ctx prog labels e₁) (h₂ : SimE ctx prog labels e₂)
    {c₀ c₁ c₂ : Nat} {cx cy : List Instr}
    (hx : Emits (compileExpr ctx e₁) c₀ cx c₁ PUnit.unit)
    (hy : Emits (compileExpr ctx e₂) c₁ cy c₂ PUnit.unit)
    (s : Whitespace.State) (rest : List Instr)
    (hcode : CodeAt prog s.pc (cx ++ (cy ++ rest)))
    (hlab : LabelsOk labels s.pc (cx ++ (cy ++ rest)))
    (env : Std.HashMap String Value) (w₁ w₂ : Value)
    (hw₁ : evalExpr env e₁ = .ok w₁) (hw₂ : evalExpr env e₂ = .ok w₂)
    (hag : Agrees ctx env s.heap) :
    Reaches (Whitespace.exec prog labels) s
      { s with pc := s.pc + cx.length + cy.length,
               stack := encV w₂ :: encV w₁ :: s.stack } := by
  have step1 := h₁ c₀ cx c₁ hx s hcode.left hlab.left env w₁ hw₁ hag
  have step2 := h₂ c₁ cy c₂ hy
    { s with pc := s.pc + cx.length, stack := encV w₁ :: s.stack }
    ((hcode.right' (c₁ := cx) rfl).left) ((hlab.right' (c₁ := cx) rfl).left)
    env w₂ hw₂ hag
  exact Reaches.trans step1 step2

/-- The binary operators, split out of `simExpr` so that the case analysis
over the thirteen of them sits in a file section of its own. The two
hypotheses are exactly the induction hypotheses `simExpr` has to offer. -/
theorem simExpr_bin {ctx : Frame} {ns : List String} (hcov : Covers ctx ns)
    {prog : Prog} {labels : Std.HashMap Label Nat}
    (op : BinOp) (a b : Expr)
    (iha : okExpr ns a = true → SimE ctx prog labels a)
    (ihb : okExpr ns b = true → SimE ctx prog labels b) :
    okExpr ns (.bin op a b) = true → SimE ctx prog labels (.bin op a b) := by
  intro hok
  have hoka : okExpr ns a = true := by revert hok; simp only [okExpr, Bool.and_eq_true]; tauto
  have hokb : okExpr ns b = true := by revert hok; simp only [okExpr, Bool.and_eq_true]; tauto
  have hopok : okOp op = true := by revert hok; simp only [okExpr, Bool.and_eq_true]; tauto
  intro c code c' hem s hcode hlab env v heval hag
  cases op with
  | div => simp [okOp] at hopok
  | mod => simp [okOp] at hopok
  | add =>
    obtain ⟨ca, c₁, hEA, -, -⟩ := emitsExpr hcov a hoka c
    obtain ⟨cb, c₂, hEB, -, -⟩ := emitsExpr hcov b hokb c₁
    obtain ⟨hcd, -, -⟩ := Emits.det hem (emitsE_arith (i := Instr.add) rfl hEA hEB)
    subst hcd
    obtain ⟨w₁, w₂, hw₁, hw₂, hbin⟩ := evalExpr_bin_inv (by rfl) heval
    have base := sim_twoOps (iha hoka) (ihb hokb) hEA hEB s [Instr.add] hcode hlab
      env w₁ w₂ hw₁ hw₂ hag
    have hi : prog[s.pc + ca.length + cb.length]? = some Instr.add :=
      ((hcode.right' (c₁ := ca) rfl).right' (c₁ := cb) rfl).head
    have step3 := reaches_add (prog := prog) (labels := labels)
      { s with pc := s.pc + ca.length + cb.length, stack := encV w₂ :: encV w₁ :: s.stack }
      (encV w₁) (encV w₂) s.stack rfl hi
    have chain : Reaches (Whitespace.exec prog labels) s
        { s with pc := s.pc + ca.length + cb.length + 1,
                 stack := (encV w₁ + encV w₂) :: s.stack } := Reaches.trans base step3
    have hpc : s.pc + ca.length + cb.length + 1
        = s.pc + (ca ++ (cb ++ [Instr.add])).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]; omega
    rw [hpc, ← evalBin_add_enc hbin] at chain
    exact chain
  | sub =>
    obtain ⟨ca, c₁, hEA, -, -⟩ := emitsExpr hcov a hoka c
    obtain ⟨cb, c₂, hEB, -, -⟩ := emitsExpr hcov b hokb c₁
    obtain ⟨hcd, -, -⟩ := Emits.det hem (emitsE_arith (i := Instr.sub) rfl hEA hEB)
    subst hcd
    obtain ⟨w₁, w₂, hw₁, hw₂, hbin⟩ := evalExpr_bin_inv (by rfl) heval
    have base := sim_twoOps (iha hoka) (ihb hokb) hEA hEB s [Instr.sub] hcode hlab
      env w₁ w₂ hw₁ hw₂ hag
    have hi : prog[s.pc + ca.length + cb.length]? = some Instr.sub :=
      ((hcode.right' (c₁ := ca) rfl).right' (c₁ := cb) rfl).head
    have step3 := reaches_sub (prog := prog) (labels := labels)
      { s with pc := s.pc + ca.length + cb.length, stack := encV w₂ :: encV w₁ :: s.stack }
      (encV w₁) (encV w₂) s.stack rfl hi
    have chain : Reaches (Whitespace.exec prog labels) s
        { s with pc := s.pc + ca.length + cb.length + 1,
                 stack := (encV w₁ - encV w₂) :: s.stack } := Reaches.trans base step3
    have hpc : s.pc + ca.length + cb.length + 1
        = s.pc + (ca ++ (cb ++ [Instr.sub])).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]; omega
    rw [hpc, ← evalBin_sub_enc hbin] at chain
    exact chain
  | mul =>
    obtain ⟨ca, c₁, hEA, -, -⟩ := emitsExpr hcov a hoka c
    obtain ⟨cb, c₂, hEB, -, -⟩ := emitsExpr hcov b hokb c₁
    obtain ⟨hcd, -, -⟩ := Emits.det hem (emitsE_arith (i := Instr.mul) rfl hEA hEB)
    subst hcd
    obtain ⟨w₁, w₂, hw₁, hw₂, hbin⟩ := evalExpr_bin_inv (by rfl) heval
    have base := sim_twoOps (iha hoka) (ihb hokb) hEA hEB s [Instr.mul] hcode hlab
      env w₁ w₂ hw₁ hw₂ hag
    have hi : prog[s.pc + ca.length + cb.length]? = some Instr.mul :=
      ((hcode.right' (c₁ := ca) rfl).right' (c₁ := cb) rfl).head
    have step3 := reaches_mul (prog := prog) (labels := labels)
      { s with pc := s.pc + ca.length + cb.length, stack := encV w₂ :: encV w₁ :: s.stack }
      (encV w₁) (encV w₂) s.stack rfl hi
    have chain : Reaches (Whitespace.exec prog labels) s
        { s with pc := s.pc + ca.length + cb.length + 1,
                 stack := (encV w₁ * encV w₂) :: s.stack } := Reaches.trans base step3
    have hpc : s.pc + ca.length + cb.length + 1
        = s.pc + (ca ++ (cb ++ [Instr.mul])).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]; omega
    rw [hpc, ← evalBin_mul_enc hbin] at chain
    exact chain
  | eq =>
    obtain ⟨ca, c₁, hEA, -, -⟩ := emitsExpr hcov a hoka c
    obtain ⟨cb, c₂, hEB, -, -⟩ := emitsExpr hcov b hokb c₁
    obtain ⟨hcd, -, -⟩ := Emits.det hem (emitsE_cmp (mk := Instr.jz) rfl hEA hEB)
    subst hcd
    obtain ⟨w₁, w₂, hw₁, hw₂, hbin⟩ := evalExpr_bin_inv (by rfl) heval
    have base := sim_twoOps (iha hoka) (ihb hokb) hEA hEB s
      ([Instr.sub] ++ boolTail (Instr.jz (labelOf c₂)) c₂) hcode hlab env w₁ w₂ hw₁ hw₂ hag
    have htail := (hcode.right' (c₁ := ca) rfl).right' (c₁ := cb) rfl
    have hltail := (hlab.right' (c₁ := ca) rfl).right' (c₁ := cb) rfl
    have step3 := reaches_sub (prog := prog) (labels := labels)
      { s with pc := s.pc + ca.length + cb.length, stack := encV w₂ :: encV w₁ :: s.stack }
      (encV w₁) (encV w₂) s.stack rfl htail.left.head
    have step4 := reaches_boolTail_jz (prog := prog) (labels := labels)
      { s with pc := s.pc + ca.length + cb.length + 1,
               stack := (encV w₁ - encV w₂) :: s.stack }
      (encV w₁ - encV w₂) s.stack c₂ rfl
      (htail.right' (c₁ := [Instr.sub]) (by simp))
      (hltail.right' (c₁ := [Instr.sub]) (by simp))
    have chain : Reaches (Whitespace.exec prog labels) s
        { s with pc := s.pc + ca.length + cb.length + 1 + 6,
                 stack := (if encV w₁ - encV w₂ = 0 then 1 else 0) :: s.stack } :=
      Reaches.trans base (Reaches.trans step3 step4)
    have hpc : s.pc + ca.length + cb.length + 1 + 6
        = s.pc + (ca ++ (cb ++ ([Instr.sub] ++ boolTail (Instr.jz (labelOf c₂)) c₂))).length := by
      simp only [List.length_append, List.length_cons, List.length_nil, boolTail_length]
      omega
    rw [hpc, ← evalBin_eq_enc hbin] at chain
    exact chain
  | lt =>
    obtain ⟨ca, c₁, hEA, -, -⟩ := emitsExpr hcov a hoka c
    obtain ⟨cb, c₂, hEB, -, -⟩ := emitsExpr hcov b hokb c₁
    obtain ⟨hcd, -, -⟩ := Emits.det hem (emitsE_cmp (mk := Instr.jn) rfl hEA hEB)
    subst hcd
    obtain ⟨w₁, w₂, hw₁, hw₂, hbin⟩ := evalExpr_bin_inv (by rfl) heval
    have base := sim_twoOps (iha hoka) (ihb hokb) hEA hEB s
      ([Instr.sub] ++ boolTail (Instr.jn (labelOf c₂)) c₂) hcode hlab env w₁ w₂ hw₁ hw₂ hag
    have htail := (hcode.right' (c₁ := ca) rfl).right' (c₁ := cb) rfl
    have hltail := (hlab.right' (c₁ := ca) rfl).right' (c₁ := cb) rfl
    have step3 := reaches_sub (prog := prog) (labels := labels)
      { s with pc := s.pc + ca.length + cb.length, stack := encV w₂ :: encV w₁ :: s.stack }
      (encV w₁) (encV w₂) s.stack rfl htail.left.head
    have step4 := reaches_boolTail_jn (prog := prog) (labels := labels)
      { s with pc := s.pc + ca.length + cb.length + 1,
               stack := (encV w₁ - encV w₂) :: s.stack }
      (encV w₁ - encV w₂) s.stack c₂ rfl
      (htail.right' (c₁ := [Instr.sub]) (by simp))
      (hltail.right' (c₁ := [Instr.sub]) (by simp))
    have chain : Reaches (Whitespace.exec prog labels) s
        { s with pc := s.pc + ca.length + cb.length + 1 + 6,
                 stack := (if encV w₁ - encV w₂ < 0 then 1 else 0) :: s.stack } :=
      Reaches.trans base (Reaches.trans step3 step4)
    have hpc : s.pc + ca.length + cb.length + 1 + 6
        = s.pc + (ca ++ (cb ++ ([Instr.sub] ++ boolTail (Instr.jn (labelOf c₂)) c₂))).length := by
      simp only [List.length_append, List.length_cons, List.length_nil, boolTail_length]
      omega
    rw [hpc, ← evalBin_lt_enc hbin] at chain
    exact chain
  | gt =>
    obtain ⟨cb, c₁, hEB, -, -⟩ := emitsExpr hcov b hokb c
    obtain ⟨ca, c₂, hEA, -, -⟩ := emitsExpr hcov a hoka c₁
    obtain ⟨hcd, -, -⟩ := Emits.det hem (emitsE_cmp (mk := Instr.jn) rfl hEB hEA)
    subst hcd
    obtain ⟨w₁, w₂, hw₁, hw₂, hbin⟩ := evalExpr_bin_inv (by rfl) heval
    have base := sim_twoOps (ihb hokb) (iha hoka) hEB hEA s
      ([Instr.sub] ++ boolTail (Instr.jn (labelOf c₂)) c₂) hcode hlab env w₂ w₁ hw₂ hw₁ hag
    have htail := (hcode.right' (c₁ := cb) rfl).right' (c₁ := ca) rfl
    have hltail := (hlab.right' (c₁ := cb) rfl).right' (c₁ := ca) rfl
    have step3 := reaches_sub (prog := prog) (labels := labels)
      { s with pc := s.pc + cb.length + ca.length, stack := encV w₁ :: encV w₂ :: s.stack }
      (encV w₂) (encV w₁) s.stack rfl htail.left.head
    have step4 := reaches_boolTail_jn (prog := prog) (labels := labels)
      { s with pc := s.pc + cb.length + ca.length + 1,
               stack := (encV w₂ - encV w₁) :: s.stack }
      (encV w₂ - encV w₁) s.stack c₂ rfl
      (htail.right' (c₁ := [Instr.sub]) (by simp))
      (hltail.right' (c₁ := [Instr.sub]) (by simp))
    have chain : Reaches (Whitespace.exec prog labels) s
        { s with pc := s.pc + cb.length + ca.length + 1 + 6,
                 stack := (if encV w₂ - encV w₁ < 0 then 1 else 0) :: s.stack } :=
      Reaches.trans base (Reaches.trans step3 step4)
    have hpc : s.pc + cb.length + ca.length + 1 + 6
        = s.pc + (cb ++ (ca ++ ([Instr.sub] ++ boolTail (Instr.jn (labelOf c₂)) c₂))).length := by
      simp only [List.length_append, List.length_cons, List.length_nil, boolTail_length]
      omega
    rw [hpc, ← evalBin_gt_enc hbin] at chain
    exact chain
  | le =>
    obtain ⟨ca, c₁, hEA, -, -⟩ := emitsExpr hcov a hoka c
    obtain ⟨cb, c₂, hEB, -, -⟩ := emitsExpr hcov b hokb c₁
    obtain ⟨hcd, -, -⟩ := Emits.det hem (emitsE_cmpLe (mk := Instr.jn) rfl hEA hEB)
    subst hcd
    obtain ⟨w₁, w₂, hw₁, hw₂, hbin⟩ := evalExpr_bin_inv (by rfl) heval
    have base := sim_twoOps (iha hoka) (ihb hokb) hEA hEB s
      ([Instr.sub, Instr.push 1, Instr.sub] ++ boolTail (Instr.jn (labelOf c₂)) c₂)
      hcode hlab env w₁ w₂ hw₁ hw₂ hag
    have htail := (hcode.right' (c₁ := ca) rfl).right' (c₁ := cb) rfl
    have hltail := (hlab.right' (c₁ := ca) rfl).right' (c₁ := cb) rfl
    have hi0 : prog[s.pc + ca.length + cb.length]? = some Instr.sub := htail.left.head
    have hi1 : prog[s.pc + ca.length + cb.length + 1]? = some (Instr.push 1) := by
      have := htail.left.get 1 (by simp); simpa using this
    have hi2 : prog[s.pc + ca.length + cb.length + 2]? = some Instr.sub := by
      have := htail.left.get 2 (by simp); simpa using this
    have step3 := reaches_sub (prog := prog) (labels := labels)
      { s with pc := s.pc + ca.length + cb.length, stack := encV w₂ :: encV w₁ :: s.stack }
      (encV w₁) (encV w₂) s.stack rfl hi0
    have step4 := reaches_push (prog := prog) (labels := labels)
      { s with pc := s.pc + ca.length + cb.length + 1,
               stack := (encV w₁ - encV w₂) :: s.stack } 1 hi1
    have step5 := reaches_sub (prog := prog) (labels := labels)
      { s with pc := s.pc + ca.length + cb.length + 1 + 1,
               stack := (1 : Int) :: (encV w₁ - encV w₂) :: s.stack }
      (encV w₁ - encV w₂) 1 s.stack rfl (by simpa using hi2)
    have step6 := reaches_boolTail_jn (prog := prog) (labels := labels)
      { s with pc := s.pc + ca.length + cb.length + 1 + 1 + 1,
               stack := (encV w₁ - encV w₂ - 1) :: s.stack }
      (encV w₁ - encV w₂ - 1) s.stack c₂ rfl
      (by simpa using htail.right' (c₁ := [Instr.sub, Instr.push 1, Instr.sub]) (by simp))
      (by simpa using hltail.right' (c₁ := [Instr.sub, Instr.push 1, Instr.sub]) (by simp))
    have chain : Reaches (Whitespace.exec prog labels) s
        { s with pc := s.pc + ca.length + cb.length + 1 + 1 + 1 + 6,
                 stack := (if encV w₁ - encV w₂ - 1 < 0 then 1 else 0) :: s.stack } :=
      Reaches.trans base (Reaches.trans step3 (Reaches.trans step4
        (Reaches.trans step5 step6)))
    have hpc : s.pc + ca.length + cb.length + 1 + 1 + 1 + 6
        = s.pc + (ca ++ (cb ++ ([Instr.sub, Instr.push 1, Instr.sub]
            ++ boolTail (Instr.jn (labelOf c₂)) c₂))).length := by
      simp only [List.length_append, List.length_cons, List.length_nil, boolTail_length]
      omega
    rw [hpc, ← evalBin_le_enc hbin] at chain
    exact chain
  | ge =>
    obtain ⟨cb, c₁, hEB, -, -⟩ := emitsExpr hcov b hokb c
    obtain ⟨ca, c₂, hEA, -, -⟩ := emitsExpr hcov a hoka c₁
    obtain ⟨hcd, -, -⟩ := Emits.det hem (emitsE_cmpLe (mk := Instr.jn) rfl hEB hEA)
    subst hcd
    obtain ⟨w₁, w₂, hw₁, hw₂, hbin⟩ := evalExpr_bin_inv (by rfl) heval
    have base := sim_twoOps (ihb hokb) (iha hoka) hEB hEA s
      ([Instr.sub, Instr.push 1, Instr.sub] ++ boolTail (Instr.jn (labelOf c₂)) c₂)
      hcode hlab env w₂ w₁ hw₂ hw₁ hag
    have htail := (hcode.right' (c₁ := cb) rfl).right' (c₁ := ca) rfl
    have hltail := (hlab.right' (c₁ := cb) rfl).right' (c₁ := ca) rfl
    have hi0 : prog[s.pc + cb.length + ca.length]? = some Instr.sub := htail.left.head
    have hi1 : prog[s.pc + cb.length + ca.length + 1]? = some (Instr.push 1) := by
      have := htail.left.get 1 (by simp); simpa using this
    have hi2 : prog[s.pc + cb.length + ca.length + 2]? = some Instr.sub := by
      have := htail.left.get 2 (by simp); simpa using this
    have step3 := reaches_sub (prog := prog) (labels := labels)
      { s with pc := s.pc + cb.length + ca.length, stack := encV w₁ :: encV w₂ :: s.stack }
      (encV w₂) (encV w₁) s.stack rfl hi0
    have step4 := reaches_push (prog := prog) (labels := labels)
      { s with pc := s.pc + cb.length + ca.length + 1,
               stack := (encV w₂ - encV w₁) :: s.stack } 1 hi1
    have step5 := reaches_sub (prog := prog) (labels := labels)
      { s with pc := s.pc + cb.length + ca.length + 1 + 1,
               stack := (1 : Int) :: (encV w₂ - encV w₁) :: s.stack }
      (encV w₂ - encV w₁) 1 s.stack rfl (by simpa using hi2)
    have step6 := reaches_boolTail_jn (prog := prog) (labels := labels)
      { s with pc := s.pc + cb.length + ca.length + 1 + 1 + 1,
               stack := (encV w₂ - encV w₁ - 1) :: s.stack }
      (encV w₂ - encV w₁ - 1) s.stack c₂ rfl
      (by simpa using htail.right' (c₁ := [Instr.sub, Instr.push 1, Instr.sub]) (by simp))
      (by simpa using hltail.right' (c₁ := [Instr.sub, Instr.push 1, Instr.sub]) (by simp))
    have chain : Reaches (Whitespace.exec prog labels) s
        { s with pc := s.pc + cb.length + ca.length + 1 + 1 + 1 + 6,
                 stack := (if encV w₂ - encV w₁ - 1 < 0 then 1 else 0) :: s.stack } :=
      Reaches.trans base (Reaches.trans step3 (Reaches.trans step4
        (Reaches.trans step5 step6)))
    have hpc : s.pc + cb.length + ca.length + 1 + 1 + 1 + 6
        = s.pc + (cb ++ (ca ++ ([Instr.sub, Instr.push 1, Instr.sub]
            ++ boolTail (Instr.jn (labelOf c₂)) c₂))).length := by
      simp only [List.length_append, List.length_cons, List.length_nil, boolTail_length]
      omega
    rw [hpc, ← evalBin_ge_enc hbin] at chain
    exact chain
  | ne =>
    obtain ⟨ca, c₁, hEA, -, -⟩ := emitsExpr hcov a hoka c
    obtain ⟨cb, c₂, hEB, -, -⟩ := emitsExpr hcov b hokb c₁
    obtain ⟨hcd, -, -⟩ := Emits.det hem (emitsE_ne hEA hEB)
    subst hcd
    obtain ⟨w₁, w₂, hw₁, hw₂, hbin⟩ := evalExpr_bin_inv (by rfl) heval
    have base := sim_twoOps (iha hoka) (ihb hokb) hEA hEB s
      ([Instr.sub] ++ [Instr.jz (labelOf c₂), Instr.push 1, Instr.jump (labelOf (c₂ + 1)),
        Instr.label (labelOf c₂), Instr.push 0, Instr.label (labelOf (c₂ + 1))])
      hcode hlab env w₁ w₂ hw₁ hw₂ hag
    have htail := (hcode.right' (c₁ := ca) rfl).right' (c₁ := cb) rfl
    have hltail := (hlab.right' (c₁ := ca) rfl).right' (c₁ := cb) rfl
    have step3 := reaches_sub (prog := prog) (labels := labels)
      { s with pc := s.pc + ca.length + cb.length, stack := encV w₂ :: encV w₁ :: s.stack }
      (encV w₁) (encV w₂) s.stack rfl htail.left.head
    have step4 := reaches_neTail (prog := prog) (labels := labels)
      { s with pc := s.pc + ca.length + cb.length + 1,
               stack := (encV w₁ - encV w₂) :: s.stack }
      (encV w₁ - encV w₂) s.stack c₂ rfl
      (htail.right' (c₁ := [Instr.sub]) (by simp))
      (hltail.right' (c₁ := [Instr.sub]) (by simp))
    have chain : Reaches (Whitespace.exec prog labels) s
        { s with pc := s.pc + ca.length + cb.length + 1 + 6,
                 stack := (if encV w₁ - encV w₂ = 0 then 0 else 1) :: s.stack } :=
      Reaches.trans base (Reaches.trans step3 step4)
    have hpc : s.pc + ca.length + cb.length + 1 + 6
        = s.pc + (ca ++ (cb ++ ([Instr.sub] ++
            [Instr.jz (labelOf c₂), Instr.push 1, Instr.jump (labelOf (c₂ + 1)),
             Instr.label (labelOf c₂), Instr.push 0,
             Instr.label (labelOf (c₂ + 1))]))).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    rw [hpc, ← evalBin_ne_enc hbin] at chain
    exact chain
  | and =>
    obtain ⟨ca, c₁, hEA, -, -⟩ := emitsExpr hcov a hoka (c + 1)
    obtain ⟨cb, c₂, hEB, -, -⟩ := emitsExpr hcov b hokb c₁
    obtain ⟨hcd, -, -⟩ := Emits.det hem (emitsE_and hEA hEB)
    subst hcd
    have h2 := hcode.right' (c₁ := ca) rfl
    have hl2 := hlab.right' (c₁ := ca) rfl
    have hdup : prog[s.pc + ca.length]? = some Instr.dup := h2.left.head
    have hjz : prog[s.pc + ca.length + 1]? = some (Instr.jz (labelOf c)) := by
      have := h2.left.get 1 (by simp); simpa using this
    have hdrop : prog[s.pc + ca.length + 2]? = some Instr.drop := by
      have := h2.left.get 2 (by simp); simpa using this
    have h3 := h2.right' (c₁ := [Instr.dup, Instr.jz (labelOf c), Instr.drop])
      (q := s.pc + ca.length + 3) (by simp)
    have hl3 := hl2.right' (c₁ := [Instr.dup, Instr.jz (labelOf c), Instr.drop])
      (q := s.pc + ca.length + 3) (by simp)
    have hE : labels[labelOf c]? = some (s.pc + ca.length + 3 + cb.length + 1) :=
      (hl3.right' (c₁ := cb) rfl).single
    have hlbl : prog[s.pc + ca.length + 3 + cb.length]? = some (Instr.label (labelOf c)) :=
      (h3.right' (c₁ := cb) rfl).head
    have hpc : s.pc + ca.length + 3 + cb.length + 1
        = s.pc + (ca ++ ([Instr.dup, Instr.jz (labelOf c), Instr.drop]
            ++ (cb ++ [Instr.label (labelOf c)]))).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]; omega
    rw [evalExpr_and_eq] at heval
    cases hv1 : evalExpr env a with
    | error m => rw [hv1, exc_bind_err] at heval; simp at heval
    | ok w =>
      rw [hv1, exc_bind_ok] at heval
      cases w with
      | int n => simp at heval
      | arr elems => simp at heval
      | bool bb =>
        cases bb with
        | false =>
          have hv : v = .bool false := by simpa using heval.symm
          subst hv
          have step1 := (iha hoka) (c + 1) ca c₁ hEA s hcode.left hlab.left env
            (.bool false) hv1 hag
          have step2 := reaches_dup (prog := prog) (labels := labels)
            { s with pc := s.pc + ca.length, stack := (0 : Int) :: s.stack } 0 s.stack rfl hdup
          have step3 := reaches_jz_taken (prog := prog) (labels := labels)
            { s with pc := s.pc + ca.length + 1,
                     stack := (0 : Int) :: (0 : Int) :: s.stack }
            ((0 : Int) :: s.stack) (labelOf c) (s.pc + ca.length + 3 + cb.length + 1)
            rfl hE hjz
          have chain : Reaches (Whitespace.exec prog labels) s
              { s with pc := s.pc + ca.length + 3 + cb.length + 1,
                       stack := encV (Value.bool false) :: s.stack } :=
            Reaches.trans step1 (Reaches.trans step2 step3)
          rw [hpc] at chain
          exact chain
        | true =>
          have step1 := (iha hoka) (c + 1) ca c₁ hEA s hcode.left hlab.left env
            (.bool true) hv1 hag
          have step2 := reaches_dup (prog := prog) (labels := labels)
            { s with pc := s.pc + ca.length, stack := (1 : Int) :: s.stack } 1 s.stack rfl hdup
          have step3 := reaches_jz_untaken (prog := prog) (labels := labels)
            { s with pc := s.pc + ca.length + 1,
                     stack := (1 : Int) :: (1 : Int) :: s.stack }
            ((1 : Int) :: s.stack) (labelOf c) 1 (by decide) rfl hjz
          have step4 := reaches_drop (prog := prog) (labels := labels)
            { s with pc := s.pc + ca.length + 1 + 1, stack := (1 : Int) :: s.stack }
            1 s.stack rfl (by simpa using hdrop)
          have step5 := (ihb hokb) c₁ cb c₂ hEB
            { s with pc := s.pc + ca.length + 1 + 1 + 1, stack := s.stack }
            (by simpa using h3.left) (by simpa using hl3.left) env v heval hag
          have step6 := reaches_label (prog := prog) (labels := labels)
            { s with pc := s.pc + ca.length + 3 + cb.length, stack := encV v :: s.stack }
            (labelOf c) hlbl
          have chain : Reaches (Whitespace.exec prog labels) s
              { s with pc := s.pc + ca.length + 3 + cb.length + 1,
                       stack := encV v :: s.stack } :=
            Reaches.trans step1 (Reaches.trans step2 (Reaches.trans step3
              (Reaches.trans step4 (Reaches.trans step5 step6))))
          rw [hpc] at chain
          exact chain
  | or =>
    obtain ⟨ca, c₁, hEA, -, -⟩ := emitsExpr hcov a hoka (c + 2)
    obtain ⟨cb, c₂, hEB, -, -⟩ := emitsExpr hcov b hokb c₁
    obtain ⟨hcd, -, -⟩ := Emits.det hem (emitsE_or hEA hEB)
    subst hcd
    have h2 := hcode.right' (c₁ := ca) rfl
    have hl2 := hlab.right' (c₁ := ca) rfl
    have hjz : prog[s.pc + ca.length]? = some (Instr.jz (labelOf c)) := h2.left.head
    have hpush : prog[s.pc + ca.length + 1]? = some (Instr.push 1) := by
      have := h2.left.get 1 (by simp); simpa using this
    have hjump : prog[s.pc + ca.length + 2]? = some (Instr.jump (labelOf (c + 1))) := by
      have := h2.left.get 2 (by simp); simpa using this
    have hS : labels[labelOf c]? = some (s.pc + ca.length + 4) := by
      have := hl2.left 3 (labelOf c) rfl; simpa using this
    have h3 := h2.right' (c₁ := [Instr.jz (labelOf c), Instr.push 1,
      Instr.jump (labelOf (c + 1)), Instr.label (labelOf c)])
      (q := s.pc + ca.length + 4) (by simp)
    have hl3 := hl2.right' (c₁ := [Instr.jz (labelOf c), Instr.push 1,
      Instr.jump (labelOf (c + 1)), Instr.label (labelOf c)])
      (q := s.pc + ca.length + 4) (by simp)
    have hE : labels[labelOf (c + 1)]? = some (s.pc + ca.length + 4 + cb.length + 1) :=
      (hl3.right' (c₁ := cb) rfl).single
    have hlbl : prog[s.pc + ca.length + 4 + cb.length]? =
        some (Instr.label (labelOf (c + 1))) := (h3.right' (c₁ := cb) rfl).head
    have hpc : s.pc + ca.length + 4 + cb.length + 1
        = s.pc + (ca ++ ([Instr.jz (labelOf c), Instr.push 1,
            Instr.jump (labelOf (c + 1)), Instr.label (labelOf c)]
            ++ (cb ++ [Instr.label (labelOf (c + 1))]))).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]; omega
    rw [evalExpr_or_eq] at heval
    cases hv1 : evalExpr env a with
    | error m => rw [hv1, exc_bind_err] at heval; simp at heval
    | ok w =>
      rw [hv1, exc_bind_ok] at heval
      cases w with
      | int n => simp at heval
      | arr elems => simp at heval
      | bool bb =>
        cases bb with
        | true =>
          have hv : v = .bool true := by simpa using heval.symm
          subst hv
          have step1 := (iha hoka) (c + 2) ca c₁ hEA s hcode.left hlab.left env
            (.bool true) hv1 hag
          have step2 := reaches_jz_untaken (prog := prog) (labels := labels)
            { s with pc := s.pc + ca.length, stack := (1 : Int) :: s.stack }
            s.stack (labelOf c) 1 (by decide) rfl hjz
          have step3 := reaches_push (prog := prog) (labels := labels)
            { s with pc := s.pc + ca.length + 1, stack := s.stack } 1 (by simpa using hpush)
          have step4 := reaches_jump (prog := prog) (labels := labels)
            { s with pc := s.pc + ca.length + 1 + 1, stack := (1 : Int) :: s.stack }
            (labelOf (c + 1)) (s.pc + ca.length + 4 + cb.length + 1) hE (by simpa using hjump)
          have chain : Reaches (Whitespace.exec prog labels) s
              { s with pc := s.pc + ca.length + 4 + cb.length + 1,
                       stack := encV (Value.bool true) :: s.stack } :=
            Reaches.trans step1 (Reaches.trans step2 (Reaches.trans step3 step4))
          rw [hpc] at chain
          exact chain
        | false =>
          have step1 := (iha hoka) (c + 2) ca c₁ hEA s hcode.left hlab.left env
            (.bool false) hv1 hag
          have step2 := reaches_jz_taken (prog := prog) (labels := labels)
            { s with pc := s.pc + ca.length, stack := (0 : Int) :: s.stack }
            s.stack (labelOf c) (s.pc + ca.length + 4) rfl hS hjz
          have step3 := (ihb hokb) c₁ cb c₂ hEB
            { s with pc := s.pc + ca.length + 4, stack := s.stack }
            (by simpa using h3.left) (by simpa using hl3.left) env v heval hag
          have step4 := reaches_label (prog := prog) (labels := labels)
            { s with pc := s.pc + ca.length + 4 + cb.length, stack := encV v :: s.stack }
            (labelOf (c + 1)) hlbl
          have chain : Reaches (Whitespace.exec prog labels) s
              { s with pc := s.pc + ca.length + 4 + cb.length + 1,
                       stack := encV v :: s.stack } :=
            Reaches.trans step1 (Reaches.trans step2 (Reaches.trans step3 step4))
          rw [hpc] at chain
          exact chain

theorem simExpr {ctx : Frame} {ns : List String} (hcov : Covers ctx ns)
    (hg : GoodFrame ctx) {prog : Prog} {labels : Std.HashMap Label Nat} (e : Expr) :
    okExpr ns e = true → SimE ctx prog labels e := by
  induction e with
  | intLit n =>
    intro _ c code c' hem s hcode hlab env v heval hag
    obtain ⟨hcd, -, -⟩ := Emits.det hem (emitsE_intLit ctx n c)
    subst hcd
    rw [evalExpr, exc_pure] at heval
    have hv : v = .int n := (Except.ok.inj heval).symm
    subst hv
    have chain : Reaches (Whitespace.exec prog labels) s
        { s with pc := s.pc + 1, stack := n :: s.stack } :=
      reaches_push (prog := prog) (labels := labels) s n hcode.head
    have hpc : s.pc + 1 = s.pc + ([Instr.push n]).length := by simp
    rw [hpc] at chain
    exact chain
  | boolLit b =>
    intro _ c code c' hem s hcode hlab env v heval hag
    obtain ⟨hcd, -, -⟩ := Emits.det hem (emitsE_boolLit ctx b c)
    subst hcd
    rw [evalExpr, exc_pure] at heval
    have hv : v = .bool b := (Except.ok.inj heval).symm
    subst hv
    have chain : Reaches (Whitespace.exec prog labels) s
        { s with pc := s.pc + 1, stack := (if b then 1 else 0) :: s.stack } :=
      reaches_push (prog := prog) (labels := labels) s _ hcode.head
    have hpc : s.pc + 1 = s.pc + ([Instr.push (if b then (1:Int) else 0)]).length := by simp
    have hval : (if b then (1:Int) else 0) = encV (.bool b) := by cases b <;> rfl
    rw [hpc, hval] at chain
    exact chain
  | var x =>
    intro hok c code c' hem s hcode hlab env v heval hag
    obtain ⟨a, ha⟩ := hcov x (mem_of_contains (by simpa [okExpr] using hok))
    obtain ⟨hcd, -, -⟩ := Emits.det hem (emitsE_var ha c)
    subst hcd
    have hx := evalExpr_var_inv heval
    have hval : s.heap.getD a 0 = encV v := (hag x a ha v hx).1
    have h1 : prog[s.pc + 1]? = some Instr.retrieve := by
      have := hcode.get 1 (by simp); simpa using this
    have step1 := reaches_push (prog := prog) (labels := labels) s a hcode.head
    have step2 := reaches_retrieve (prog := prog) (labels := labels)
      { s with pc := s.pc + 1, stack := a :: s.stack } a s.stack rfl (hg.nonneg x a ha)
      (by simpa using h1)
    have chain : Reaches (Whitespace.exec prog labels) s
        { s with pc := s.pc + 1 + 1, stack := s.heap.getD a 0 :: s.stack } :=
      Reaches.trans step1 step2
    have hpc : s.pc + 1 + 1 = s.pc + ([Instr.push a, Instr.retrieve]).length := by simp
    rw [hpc, hval] at chain
    exact chain
  | index x i => intro hok; simp [okExpr] at hok
  | len x => intro hok; simp [okExpr] at hok
  | un op e ih =>
    intro hok c code c' hem s hcode hlab env v heval hag
    have hoke : okExpr ns e = true := by simpa [okExpr] using hok
    obtain ⟨ce, ce', hE, hle, hcl⟩ := emitsExpr hcov e hoke c
    have run : ∀ (k : Int) (w : Value), evalExpr env e = .ok w →
        prog[s.pc]? = some (Instr.push k) →
        CodeAt prog (s.pc + 1) ce → LabelsOk labels (s.pc + 1) ce →
        prog[s.pc + 1 + ce.length]? = some Instr.sub →
        Reaches (Whitespace.exec prog labels) s
          { s with pc := s.pc + 1 + ce.length + 1, stack := (k - encV w) :: s.stack } := by
      intro k w hw h0 hcE hlE hsub
      have step1 := reaches_push (prog := prog) (labels := labels) s k h0
      have step2 := ih hoke c ce ce' hE
        { s with pc := s.pc + 1, stack := k :: s.stack } hcE hlE env w hw hag
      have step3 := reaches_sub (prog := prog) (labels := labels)
        { s with pc := s.pc + 1 + ce.length, stack := encV w :: k :: s.stack }
        k (encV w) s.stack rfl hsub
      exact Reaches.trans step1 (Reaches.trans step2 step3)
    cases op with
    | neg =>
      obtain ⟨hcd, -, -⟩ := Emits.det hem (emitsE_neg hE)
      subst hcd
      obtain ⟨w, hw, henc⟩ := evalExpr_neg_inv heval
      have hcE : CodeAt prog (s.pc + 1) ce :=
        ((hcode.right' (c₁ := [Instr.push (0 : Int)]) (by simp)).left)
      have hlE : LabelsOk labels (s.pc + 1) ce :=
        ((hlab.right' (c₁ := [Instr.push (0 : Int)]) (by simp)).left)
      have hsub : prog[s.pc + 1 + ce.length]? = some Instr.sub :=
        (((hcode.right' (c₁ := [Instr.push (0 : Int)]) (by simp)).right'
          (c₁ := ce) rfl)).head
      have chain := run 0 w hw hcode.head hcE hlE hsub
      have hpc : s.pc + 1 + ce.length + 1
          = s.pc + ([Instr.push (0 : Int)] ++ (ce ++ [Instr.sub])).length := by
        simp only [List.length_append, List.length_cons, List.length_nil]; omega
      rw [hpc, ← henc] at chain
      exact chain
    | not =>
      obtain ⟨hcd, -, -⟩ := Emits.det hem (emitsE_not hE)
      subst hcd
      obtain ⟨w, hw, henc⟩ := evalExpr_not_inv heval
      have hcE : CodeAt prog (s.pc + 1) ce :=
        ((hcode.right' (c₁ := [Instr.push (1 : Int)]) (by simp)).left)
      have hlE : LabelsOk labels (s.pc + 1) ce :=
        ((hlab.right' (c₁ := [Instr.push (1 : Int)]) (by simp)).left)
      have hsub : prog[s.pc + 1 + ce.length]? = some Instr.sub :=
        (((hcode.right' (c₁ := [Instr.push (1 : Int)]) (by simp)).right'
          (c₁ := ce) rfl)).head
      have chain := run 1 w hw hcode.head hcE hlE hsub
      have hpc : s.pc + 1 + ce.length + 1
          = s.pc + ([Instr.push (1 : Int)] ++ (ce ++ [Instr.sub])).length := by
        simp only [List.length_append, List.length_cons, List.length_nil]; omega
      rw [hpc, ← henc] at chain
      exact chain
  | bin op a b iha ihb => exact simExpr_bin hcov op a b iha ihb

/-! ### Statements -/

theorem emitsS_skip (ctx : Frame) (c : Nat) :
    Emits (compileStmt ctx .skip) c [] c PUnit.unit := by
  show Emits (Pure.pure PUnit.unit) c [] c PUnit.unit
  exact Emits.pure _ _

theorem emitsS_seq {ctx : Frame} {a b : Stmt} {c c₁ c₂ : Nat} {ca cb : List Instr}
    (ha : Emits (compileStmt ctx a) c ca c₁ PUnit.unit)
    (hb : Emits (compileStmt ctx b) c₁ cb c₂ PUnit.unit) :
    Emits (compileStmt ctx (.seq a b)) c (ca ++ cb) c₂ PUnit.unit := by
  have he : compileStmt ctx (.seq a b)
      = (compileStmt ctx a >>= fun _ => compileStmt ctx b) := rfl
  rw [he]
  exact Emits.seq ha hb

theorem emitsS_assign {ctx : Frame} {x : String} {a : Int} {e : Expr} {c c' : Nat}
    {code : List Instr} (hx : ctx.addrs[x]? = some a)
    (he : Emits (compileExpr ctx e) c code c' PUnit.unit) :
    Emits (compileStmt ctx (.assign x e)) c
      ([] ++ ([Instr.push a] ++ (code ++ [Instr.store]))) c' PUnit.unit := by
  have hd : compileStmt ctx (.assign x e)
      = (addrOf ctx x >>= fun a => emit (Instr.push a) >>= fun _ =>
          compileExpr ctx e >>= fun _ => emit Instr.store) := rfl
  rw [hd]
  exact Emits.bind (g := fun a => emit (Instr.push a) >>= fun _ =>
      compileExpr ctx e >>= fun _ => emit Instr.store)
    (emits_addrOf hx c) (Emits.seq (emits_emit _ c) (Emits.seq he (emits_emit _ c')))

theorem emitsS_ite {ctx : Frame} {cnd : Expr} {t f : Stmt} {c c₁ c₂ c₃ : Nat}
    {cc ct cf : List Instr}
    (hc : Emits (compileExpr ctx cnd) (c + 2) cc c₁ PUnit.unit)
    (ht : Emits (compileStmt ctx t) c₁ ct c₂ PUnit.unit)
    (hf : Emits (compileStmt ctx f) c₂ cf c₃ PUnit.unit) :
    Emits (compileStmt ctx (.ite cnd t f)) c
      (cc ++ ([Instr.jz (labelOf c)] ++ (ct ++
        ([Instr.jump (labelOf (c + 1)), Instr.label (labelOf c)] ++
          (cf ++ [Instr.label (labelOf (c + 1))]))))) c₃ PUnit.unit := by
  have hd : compileStmt ctx (.ite cnd t f)
      = (fresh >>= fun els => fresh >>= fun end_ => compileExpr ctx cnd >>= fun _ =>
          emit (Instr.jz els) >>= fun _ => compileStmt ctx t >>= fun _ =>
            emits [Instr.jump end_, Instr.label els] >>= fun _ =>
              compileStmt ctx f >>= fun _ => emit (Instr.label end_)) := rfl
  rw [hd]
  have h1 := Emits.seq hc (Emits.seq (emits_emit (Instr.jz (labelOf c)) c₁)
    (Emits.seq ht (Emits.seq
      (emits_emits [Instr.jump (labelOf (c + 1)), Instr.label (labelOf c)] c₂)
      (Emits.seq hf (emits_emit (Instr.label (labelOf (c + 1))) c₃)))))
  have h2 := Emits.bind (g := fun end_ => compileExpr ctx cnd >>= fun _ =>
      emit (Instr.jz (labelOf c)) >>= fun _ => compileStmt ctx t >>= fun _ =>
        emits [Instr.jump end_, Instr.label (labelOf c)] >>= fun _ =>
          compileStmt ctx f >>= fun _ => emit (Instr.label end_))
    (emits_fresh (c + 1)) h1
  have h3 := Emits.bind (g := fun els => fresh >>= fun end_ =>
      compileExpr ctx cnd >>= fun _ => emit (Instr.jz els) >>= fun _ =>
        compileStmt ctx t >>= fun _ =>
          emits [Instr.jump end_, Instr.label els] >>= fun _ =>
            compileStmt ctx f >>= fun _ => emit (Instr.label end_))
    (emits_fresh c) h2
  simpa using h3

theorem emitsS_while {ctx : Frame} {cnd : Expr} {body : Stmt} {c c₁ c₂ : Nat}
    {cc cb : List Instr}
    (hc : Emits (compileExpr ctx cnd) (c + 2) cc c₁ PUnit.unit)
    (hb : Emits (compileStmt ctx body) c₁ cb c₂ PUnit.unit) :
    Emits (compileStmt ctx (.while cnd body)) c
      ([Instr.label (labelOf c)] ++ (cc ++ ([Instr.jz (labelOf (c + 1))] ++
        (cb ++ [Instr.jump (labelOf c), Instr.label (labelOf (c + 1))])))) c₂ PUnit.unit := by
  have hd : compileStmt ctx (.while cnd body)
      = (fresh >>= fun top => fresh >>= fun end_ => emit (Instr.label top) >>= fun _ =>
          compileExpr ctx cnd >>= fun _ => emit (Instr.jz end_) >>= fun _ =>
            compileStmt ctx body >>= fun _ =>
              emits [Instr.jump top, Instr.label end_]) := rfl
  rw [hd]
  have h1 := Emits.seq (emits_emit (Instr.label (labelOf c)) (c + 2))
    (Emits.seq hc (Emits.seq (emits_emit (Instr.jz (labelOf (c + 1))) c₁)
      (Emits.seq hb (emits_emits [Instr.jump (labelOf c),
        Instr.label (labelOf (c + 1))] c₂))))
  have h2 := Emits.bind (g := fun end_ => emit (Instr.label (labelOf c)) >>= fun _ =>
      compileExpr ctx cnd >>= fun _ => emit (Instr.jz end_) >>= fun _ =>
        compileStmt ctx body >>= fun _ =>
          emits [Instr.jump (labelOf c), Instr.label end_])
    (emits_fresh (c + 1)) h1
  have h3 := Emits.bind (g := fun top => fresh >>= fun end_ =>
      emit (Instr.label top) >>= fun _ => compileExpr ctx cnd >>= fun _ =>
        emit (Instr.jz end_) >>= fun _ => compileStmt ctx body >>= fun _ =>
          emits [Instr.jump top, Instr.label end_])
    (emits_fresh c) h2
  simpa using h3

theorem emitsS_assert {ctx : Frame} {e : Expr} {c c₁ : Nat} {ce : List Instr}
    (he : Emits (compileExpr ctx e) (c + 2) ce c₁ PUnit.unit) :
    Emits (compileStmt ctx (.assert e)) c
      (ce ++ ([Instr.jz (labelOf c), Instr.jump (labelOf (c + 1)), Instr.label (labelOf c)]
        ++ ([Instr.push (-1), Instr.retrieve] ++ [Instr.label (labelOf (c + 1))])))
      c₁ PUnit.unit := by
  have hd : compileStmt ctx (.assert e)
      = (fresh >>= fun bad => fresh >>= fun ok => compileExpr ctx e >>= fun _ =>
          emits [Instr.jz bad, Instr.jump ok, Instr.label bad] >>= fun _ =>
            emitTrap >>= fun _ => emit (Instr.label ok)) := rfl
  have htrap : (emitTrap : M Unit) = emits [Instr.push (-1), Instr.retrieve] := rfl
  rw [hd, htrap]
  have h1 := Emits.seq he (Emits.seq
    (emits_emits [Instr.jz (labelOf c), Instr.jump (labelOf (c + 1)),
      Instr.label (labelOf c)] c₁)
    (Emits.seq (emits_emits [Instr.push (-1), Instr.retrieve] c₁)
      (emits_emit (Instr.label (labelOf (c + 1))) c₁)))
  have h2 := Emits.bind (g := fun ok => compileExpr ctx e >>= fun _ =>
      emits [Instr.jz (labelOf c), Instr.jump ok, Instr.label (labelOf c)] >>= fun _ =>
        emits [Instr.push (-1), Instr.retrieve] >>= fun _ => emit (Instr.label ok))
    (emits_fresh (c + 1)) h1
  have h3 := Emits.bind (g := fun bad => fresh >>= fun ok =>
      compileExpr ctx e >>= fun _ =>
        emits [Instr.jz bad, Instr.jump ok, Instr.label bad] >>= fun _ =>
          emits [Instr.push (-1), Instr.retrieve] >>= fun _ => emit (Instr.label ok))
    (emits_fresh c) h2
  simpa using h3


/-! ### Every fragment statement emits something clean -/

theorem emitsStmt {ctx : Frame} {ns : List String} (hcov : Covers ctx ns) (st : Stmt) :
    okStmt ns ctx.types st = true → ∀ c : Nat,
      ∃ code c', Emits (compileStmt ctx st) c code c' PUnit.unit ∧ c ≤ c' ∧
        Clean c c' code := by
  induction st with
  | skip =>
    intro _ c
    exact ⟨_, c, emitsS_skip ctx c, Nat.le_refl c, Clean.ofNoLabels rfl⟩
  | seq a b iha ihb =>
    intro hok c
    have hoka : okStmt ns ctx.types a = true := by revert hok; simp only [okStmt, Bool.and_eq_true]; tauto
    have hokb : okStmt ns ctx.types b = true := by revert hok; simp only [okStmt, Bool.and_eq_true]; tauto
    obtain ⟨ca, c₁, hA, hleA, hclA⟩ := iha hoka c
    obtain ⟨cb, c₂, hB, hleB, hclB⟩ := ihb hokb c₁
    exact ⟨_, c₂, emitsS_seq hA hB, by omega, Clean.appendUp hleA hleB hclA hclB⟩
  | assign x e =>
    intro hok c
    have hx : ns.contains x = true := by revert hok; simp only [okStmt, Bool.and_eq_true]; tauto
    have he : okExpr ns e = true := by revert hok; simp only [okStmt, Bool.and_eq_true]; tauto
    obtain ⟨a, ha⟩ := hcov x (mem_of_contains hx)
    obtain ⟨code, c', hE, hle, hcl⟩ := emitsExpr hcov e he c
    refine ⟨_, c', emitsS_assign ha hE, hle, ?_⟩
    refine Clean.appendUp (Nat.le_refl c) hle (Clean.ofNoLabels rfl) ?_
    exact Clean.appendUp (Nat.le_refl c) hle (Clean.ofNoLabels rfl)
      (Clean.appendUp hle (Nat.le_refl c') hcl (Clean.ofNoLabels rfl))
  | ite cnd t f iht ihf =>
    intro hok c
    have hokc : okExpr ns cnd = true := by
      revert hok; simp only [okStmt, Bool.and_eq_true]; tauto
    have hokt : okStmt ns ctx.types t = true := by
      revert hok; simp only [okStmt, Bool.and_eq_true]; tauto
    have hokf : okStmt ns ctx.types f = true := by
      revert hok; simp only [okStmt, Bool.and_eq_true]; tauto
    obtain ⟨cc, c₁, hC, hleC, hclC⟩ := emitsExpr hcov cnd hokc (c + 2)
    obtain ⟨ct, c₂, hT, hleT, hclT⟩ := iht hokt c₁
    obtain ⟨cf, c₃, hF, hleF, hclF⟩ := ihf hokf c₂
    refine ⟨_, c₃, emitsS_ite hC hT hF, by omega, ?_⟩
    have hmid : labelIdxs [Instr.jump (labelOf (c + 1)), Instr.label (labelOf c)] = [c] := by
      simp [labelIdxs, labelsOf, unlabel_labelOf]
    refine Clean.ofEq
      (ks := labelIdxs cc ++ (labelIdxs ct ++ ([c] ++ (labelIdxs cf ++ [c + 1])))) ?_ ?_ ?_
    · simp only [labelIdxs_append, labelIdxs_label, hmid]
      rfl
    · intro k hk
      rcases List.mem_append.mp hk with hm | hm
      · have := hclC.bounds k hm; omega
      · rcases List.mem_append.mp hm with hm | hm
        · have := hclT.bounds k hm; omega
        · rcases List.mem_append.mp hm with hm | hm
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm; omega
          · rcases List.mem_append.mp hm with hm | hm
            · have := hclF.bounds k hm; omega
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm; omega
    · refine nodup_app hclC.nodup (nodup_app hclT.nodup
        (nodup_app (by simp) (nodup_app hclF.nodup (by simp) ?_) ?_) ?_) ?_
      · intro k h1 h2
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
        have := hclF.bounds k h1; omega
      · intro k h1 h2
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h1
        rcases List.mem_append.mp h2 with hm | hm
        · have := hclF.bounds k hm; omega
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm; omega
      · intro k h1 h2
        have := hclT.bounds k h1
        rcases List.mem_append.mp h2 with hm | hm
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm; omega
        · rcases List.mem_append.mp hm with hm | hm
          · have := hclF.bounds k hm; omega
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm; omega
      · intro k h1 h2
        have := hclC.bounds k h1
        rcases List.mem_append.mp h2 with hm | hm
        · have := hclT.bounds k hm; omega
        · rcases List.mem_append.mp hm with hm | hm
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm; omega
          · rcases List.mem_append.mp hm with hm | hm
            · have := hclF.bounds k hm; omega
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm; omega
  | «while» cnd body ihb =>
    intro hok c
    have hokc : okExpr ns cnd = true := by
      revert hok; simp only [okStmt, Bool.and_eq_true]; tauto
    have hokb : okStmt ns ctx.types body = true := by
      revert hok; simp only [okStmt, Bool.and_eq_true]; tauto
    obtain ⟨cc, c₁, hC, hleC, hclC⟩ := emitsExpr hcov cnd hokc (c + 2)
    obtain ⟨cb, c₂, hB, hleB, hclB⟩ := ihb hokb c₁
    refine ⟨_, c₂, emitsS_while hC hB, by omega, ?_⟩
    have hmid : labelIdxs [Instr.jump (labelOf c), Instr.label (labelOf (c + 1))] = [c + 1] := by
      simp [labelIdxs, labelsOf, unlabel_labelOf]
    refine Clean.ofEq
      (ks := [c] ++ (labelIdxs cc ++ (labelIdxs cb ++ [c + 1]))) ?_ ?_ ?_
    · simp only [labelIdxs_append, labelIdxs_label, hmid]
      rfl
    · intro k hk
      rcases List.mem_append.mp hk with hm | hm
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm; omega
      · rcases List.mem_append.mp hm with hm | hm
        · have := hclC.bounds k hm; omega
        · rcases List.mem_append.mp hm with hm | hm
          · have := hclB.bounds k hm; omega
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm; omega
    · refine nodup_app (by simp) (nodup_app hclC.nodup
        (nodup_app hclB.nodup (by simp) ?_) ?_) ?_
      · intro k h1 h2
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
        have := hclB.bounds k h1; omega
      · intro k h1 h2
        have := hclC.bounds k h1
        rcases List.mem_append.mp h2 with hm | hm
        · have := hclB.bounds k hm; omega
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm; omega
      · intro k h1 h2
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h1
        rcases List.mem_append.mp h2 with hm | hm
        · have := hclC.bounds k hm; omega
        · rcases List.mem_append.mp hm with hm | hm
          · have := hclB.bounds k hm; omega
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm; omega
  | «assert» e =>
    intro hok c
    have hoke : okExpr ns e = true := by simpa [okStmt] using hok
    obtain ⟨ce, c₁, hE, hleE, hclE⟩ := emitsExpr hcov e hoke (c + 2)
    refine ⟨_, c₁, emitsS_assert hE, by omega, ?_⟩
    have hmid : labelIdxs [Instr.jz (labelOf c), Instr.jump (labelOf (c + 1)),
        Instr.label (labelOf c)] = [c] := by
      simp [labelIdxs, labelsOf, unlabel_labelOf]
    refine Clean.ofEq (ks := labelIdxs ce ++ ([c] ++ [c + 1])) ?_ ?_ ?_
    · simp only [labelIdxs_append, labelIdxs_label, hmid]
      rfl
    · intro k hk
      rcases List.mem_append.mp hk with hm | hm
      · have := hclE.bounds k hm; omega
      · rcases List.mem_append.mp hm with hm | hm <;>
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hm <;> omega
    · refine nodup_app hclE.nodup (nodup_app (by simp) (by simp) ?_) ?_
      · intro k h1 h2
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h1 h2; omega
      · intro k h1 h2
        have := hclE.bounds k h1
        rcases List.mem_append.mp h2 with hm | hm <;>
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hm <;> omega
  | assignIndex x i e => intro hok _; simp [okStmt] at hok
  | readInt x => intro hok _; simp [okStmt] at hok
  | readByte x => intro hok _; simp [okStmt] at hok
  | readIntIndex x i => intro hok _; simp [okStmt] at hok
  | readByteIndex x i => intro hok _; simp [okStmt] at hok
  | printExpr e nl =>
    intro hok c
    have hoke : okExpr ns e = true := by
      revert hok; simp only [okStmt, Bool.and_eq_true]; tauto
    have hty : okPrintTy ctx.types e = true := by
      revert hok; simp only [okStmt, Bool.and_eq_true]; tauto
    rcases okPrintTy_cases hty with hint | hbool
    · obtain ⟨ce, c', hE, hle, hcl⟩ := emitsExpr hcov e hoke c
      refine ⟨_, c', emitsS_printExpr_int hint nl hE, hle, ?_⟩
      refine Clean.appendUp hle (Nat.le_refl c') hcl ?_
      exact Clean.ofNoLabels (by cases nl <;> rfl)
    · obtain ⟨ce, c', hE, hle, hcl⟩ := emitsExpr hcov e hoke (c + 2)
      refine ⟨_, c', emitsS_printExpr_bool hbool nl hE, by omega, ?_⟩
      have hmid : labelIdxs [Instr.jump (labelOf (c + 1)), Instr.label (labelOf c)] = [c] := by
        simp [labelIdxs, labelsOf, unlabel_labelOf]
      refine Clean.ofEq (ks := labelIdxs ce ++ ([c] ++ [c + 1])) ?_ ?_ ?_
      · simp only [labelIdxs_append, labelIdxs_label, hmid, labelIdxs_bytesCode,
          labelIdxs_nlCode, List.append_nil, List.nil_append]
        rfl
      · intro k hk
        rcases List.mem_append.mp hk with hm | hm
        · have := hcl.bounds k hm; omega
        · rcases List.mem_append.mp hm with hm | hm <;>
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hm <;> omega
      · refine nodup_app hcl.nodup (nodup_app (by simp) (by simp) ?_) ?_
        · intro k h1 h2
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h1 h2
          omega
        · intro k h1 h2
          have := hcl.bounds k h1
          rcases List.mem_append.mp h2 with hm | hm <;>
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hm <;> omega
  | printStr s nl =>
    intro _ c
    exact ⟨_, c, emitsS_printStr ctx s nl c, Nat.le_refl c,
      Clean.ofNoLabels (labelIdxs_bytesCode _)⟩
  | printByte e => intro hok _; simp [okStmt] at hok


/-! ## The simulation, for statements

A statement's code runs with the value stack untouched: it enters and leaves
empty of its own contribution. What changes is the heap, and the relation to
maintain is again `Agrees`.

The induction is the one `Langlib/Languages/Turpentine/Compile/URM.lean` uses: strong
induction on the source fuel, and inside it a structural induction on the
statement, because `seq` runs its first component at the same fuel while
`if` and `while` drop it by one. The extra piece here is the loop: a jump
back lands *after* the `label` instruction, so the induction hypothesis for
`while` cannot be applied at the block's own start. The `loop` lemma inside
the `while` case is stated at the entry point instead, one position in. -/

/-- The simulation property for one statement at one source fuel bound.

`Δ` is the run's I/O events, most recent first, and it is the *same* list on
both sides: the compiled code performs the events the source statement
performs, in the order it performs them. Only the fragment's `print`
statements make it non-empty. The target's output bytes are not named —
`Langlib/Languages/Whitespace/Trace.lean` recovers them from the trace, so
carrying them here would be carrying them twice. -/
def SimS (ctx : Frame) (prog : Prog) (labels : Std.HashMap Label Nat) (n : Nat)
    (st : Stmt) : Prop :=
  ∀ (c : Nat) (code : List Instr) (c' : Nat),
    Emits (compileStmt ctx st) c code c' PUnit.unit →
    ∀ (s : Whitespace.State),
      CodeAt prog s.pc code → LabelsOk labels s.pc code →
      ∀ (σ σ' : Turpentine.State),
        Turpentine.exec n st σ = (σ', Exit.halted) → Agrees ctx σ.env s.heap →
        ∃ (heap' : Std.HashMap Int Int) (str : String) (Δ : List Event),
          Reaches (Whitespace.exec prog labels) s
            { s with pc := s.pc + code.length, heap := heap',
                     output := s.output ++ str.toUTF8, events := Δ ++ s.events } ∧
          Agrees ctx σ'.env heap' ∧ σ'.events = Δ ++ σ.events

theorem simStmt {ctx : Frame} {ns : List String} (hcov : Covers ctx ns)
    (hg : GoodFrame ctx) {prog : Prog} {labels : Std.HashMap Label Nat} :
    ∀ (n : Nat) (st : Stmt), okStmt ns ctx.types st = true → SimS ctx prog labels n st := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
    cases n with
    | zero =>
      intro st _ c code c' hem s hcode hlab σ σ' hex hag
      rw [Turpentine.exec] at hex
      simp at hex
    | succ k =>
      intro st
      induction st with
      | skip =>
        intro _ c code c' hem s hcode hlab σ σ' hex hag
        obtain ⟨hcd, -, -⟩ := Emits.det hem (emitsS_skip ctx c)
        subst hcd
        rw [Turpentine.exec] at hex
        simp only [Prod.mk.injEq] at hex
        obtain ⟨hσ, -⟩ := hex
        subst hσ
        exact ⟨s.heap, "", [], reaches_cast (Reaches.refl _ s) (by simp), hag, rfl⟩
      | seq a b iha ihb =>
        intro hok c code c' hem s hcode hlab σ σ' hex hag
        have hoka : okStmt ns ctx.types a = true := by
          revert hok; simp only [okStmt, Bool.and_eq_true]; tauto
        have hokb : okStmt ns ctx.types b = true := by
          revert hok; simp only [okStmt, Bool.and_eq_true]; tauto
        obtain ⟨ca, c₁, hEA, -, -⟩ := emitsStmt hcov a hoka c
        obtain ⟨cb, c₂, hEB, -, -⟩ := emitsStmt hcov b hokb c₁
        obtain ⟨hcd, -, -⟩ := Emits.det hem (emitsS_seq hEA hEB)
        subst hcd
        rw [Turpentine.exec] at hex
        cases hea : Turpentine.exec (k + 1) a σ with
        | mk σ₂ ex =>
          cases ex with
          | outOfFuel => rw [hea] at hex; simp at hex
          | error m => rw [hea] at hex; simp at hex
          | halted =>
            rw [hea] at hex
            simp only at hex
            obtain ⟨h₂, str₂, Δ₂, r₂, ag₂, ev₂⟩ :=
              iha hoka c ca c₁ hEA s hcode.left hlab.left σ σ₂ hea hag
            obtain ⟨h₃, str₃, Δ₃, r₃, ag₃, ev₃⟩ := ihn k (by omega) b hokb c₁ cb c₂ hEB
              { s with pc := s.pc + ca.length, heap := h₂,
                       output := s.output ++ str₂.toUTF8, events := Δ₂ ++ s.events }
              (hcode.right' (c₁ := ca) rfl) (hlab.right' (c₁ := ca) rfl) σ₂ σ' hex ag₂
            refine ⟨h₃, str₂ ++ str₃, Δ₃ ++ Δ₂, ?_, ag₃,
              by rw [ev₃, ev₂, List.append_assoc]⟩
            have chain : Reaches (Whitespace.exec prog labels) s
                { s with pc := s.pc + ca.length + cb.length, heap := h₃,
                         output := s.output ++ (str₂ ++ str₃).toUTF8,
                         events := (Δ₃ ++ Δ₂) ++ s.events } :=
              reaches_cast (Reaches.trans r₂ r₃)
                (by simp [ByteArray.append_assoc])
            rw [show s.pc + ca.length + cb.length = s.pc + (ca ++ cb).length from by
              simp only [List.length_append]; omega] at chain
            exact chain
      | assign x e =>
        intro hok c code c' hem s hcode hlab σ σ' hex hag
        have hx : ns.contains x = true := by
          revert hok; simp only [okStmt, Bool.and_eq_true]; tauto
        have hoke : okExpr ns e = true := by
          revert hok; simp only [okStmt, Bool.and_eq_true]; tauto
        obtain ⟨a, ha⟩ := hcov x (mem_of_contains hx)
        obtain ⟨ce, ce', hE, -, -⟩ := emitsExpr hcov e hoke c
        obtain ⟨hcd, -, -⟩ := Emits.det hem (emitsS_assign ha hE)
        subst hcd
        have hcode' : CodeAt prog s.pc ([Instr.push a] ++ (ce ++ [Instr.store])) := by
          simpa using hcode
        have hlab' : LabelsOk labels s.pc ([Instr.push a] ++ (ce ++ [Instr.store])) := by
          simpa using hlab
        rw [Turpentine.exec] at hex
        cases hv : Turpentine.evalExpr σ.env e with
        | error m => rw [hv] at hex; simp at hex
        | ok w =>
          rw [hv] at hex
          simp only [Prod.mk.injEq] at hex
          obtain ⟨hσ, -⟩ := hex
          have step1 := reaches_push (prog := prog) (labels := labels) s a hcode'.head
          have step2 := simExpr hcov hg e hoke c ce ce' hE
            { s with pc := s.pc + 1, stack := a :: s.stack }
            ((hcode'.right' (c₁ := [Instr.push a]) (by simp)).left)
            ((hlab'.right' (c₁ := [Instr.push a]) (by simp)).left)
            σ.env w hv hag
          have hstore : prog[s.pc + 1 + ce.length]? = some Instr.store :=
            ((hcode'.right' (c₁ := [Instr.push a]) (by simp)).right' (c₁ := ce) rfl).head
          have step3 := reaches_store (prog := prog) (labels := labels)
            { s with pc := s.pc + 1 + ce.length, stack := encV w :: a :: s.stack }
            a (encV w) s.stack rfl (hg.nonneg x a ha) hstore
          refine ⟨s.heap.insert a (encV w), "", [], ?_, ?_, by rw [← hσ]; rfl⟩
          · have chain : Reaches (Whitespace.exec prog labels) s
                { s with pc := s.pc + 1 + ce.length + 1,
                         heap := s.heap.insert a (encV w),
                         output := s.output ++ "".toUTF8,
                         events := [] ++ s.events } :=
              reaches_cast (Reaches.trans step1 (Reaches.trans step2 step3)) (by simp)
            rw [show s.pc + 1 + ce.length + 1
                = s.pc + ([] ++ ([Instr.push a] ++ (ce ++ [Instr.store]))).length from by
              simp only [List.length_append, List.length_cons, List.length_nil,
                List.nil_append]; omega] at chain
            exact chain
          · rw [← hσ]
            have hoka : okAssignTy ctx.types x e = true := by
              revert hok; simp only [okStmt, Bool.and_eq_true]; tauto
            obtain ⟨tx, htx, hte⟩ := okAssignTy_inv hoka
            refine Agrees.update hg hag ha (fun u hu => ?_)
            rw [htx, Option.some.injEq] at hu
            subst hu
            exact evalExpr_hasTy hcov hag e tx w hoke hte hv
      | ite cnd t f iht ihf =>
        intro hok c code c' hem s hcode hlab σ σ' hex hag
        have hokc : okExpr ns cnd = true := by
          revert hok; simp only [okStmt, Bool.and_eq_true]; tauto
        have hokt : okStmt ns ctx.types t = true := by
          revert hok; simp only [okStmt, Bool.and_eq_true]; tauto
        have hokf : okStmt ns ctx.types f = true := by
          revert hok; simp only [okStmt, Bool.and_eq_true]; tauto
        obtain ⟨cc, c₁, hEC, -, -⟩ := emitsExpr hcov cnd hokc (c + 2)
        obtain ⟨ct, c₂, hET, -, -⟩ := emitsStmt hcov t hokt c₁
        obtain ⟨cf, c₃, hEF, -, -⟩ := emitsStmt hcov f hokf c₂
        obtain ⟨hcd, -, -⟩ := Emits.det hem (emitsS_ite hEC hET hEF)
        subst hcd
        have h2 := hcode.right' (c₁ := cc) rfl
        have hl2 := hlab.right' (c₁ := cc) rfl
        have hjz : prog[s.pc + cc.length]? = some (Instr.jz (labelOf c)) := h2.left.head
        have h3 := h2.right' (c₁ := [Instr.jz (labelOf c)])
          (q := s.pc + cc.length + 1) (by simp)
        have hl3 := hl2.right' (c₁ := [Instr.jz (labelOf c)])
          (q := s.pc + cc.length + 1) (by simp)
        have h4 := h3.right' (c₁ := ct) rfl
        have hl4 := hl3.right' (c₁ := ct) rfl
        have hjump : prog[s.pc + cc.length + 1 + ct.length]? =
            some (Instr.jump (labelOf (c + 1))) := h4.left.head
        have hels : labels[labelOf c]? = some (s.pc + cc.length + 1 + ct.length + 2) := by
          have := hl4.left 1 (labelOf c) rfl; simpa using this
        have h5 := h4.right' (c₁ := [Instr.jump (labelOf (c + 1)), Instr.label (labelOf c)])
          (q := s.pc + cc.length + 1 + ct.length + 2) (by simp)
        have hl5 := hl4.right' (c₁ := [Instr.jump (labelOf (c + 1)), Instr.label (labelOf c)])
          (q := s.pc + cc.length + 1 + ct.length + 2) (by simp)
        have hend : labels[labelOf (c + 1)]? =
            some (s.pc + cc.length + 1 + ct.length + 2 + cf.length + 1) :=
          (hl5.right' (c₁ := cf) rfl).single
        have hlbl : prog[s.pc + cc.length + 1 + ct.length + 2 + cf.length]? =
            some (Instr.label (labelOf (c + 1))) := (h5.right' (c₁ := cf) rfl).head
        have hpc : s.pc + cc.length + 1 + ct.length + 2 + cf.length + 1
            = s.pc + (cc ++ ([Instr.jz (labelOf c)] ++ (ct ++
                ([Instr.jump (labelOf (c + 1)), Instr.label (labelOf c)] ++
                  (cf ++ [Instr.label (labelOf (c + 1))]))))).length := by
          simp only [List.length_append, List.length_cons, List.length_nil]; omega
        rw [Turpentine.exec] at hex
        cases hv : Turpentine.evalExpr σ.env cnd with
        | error m => rw [hv] at hex; simp at hex
        | ok w =>
          cases w with
          | int m => rw [hv] at hex; simp at hex
          | arr elems => rw [hv] at hex; simp at hex
          | bool bb =>
            rw [hv] at hex
            have stepC := simExpr hcov hg cnd hokc (c + 2) cc c₁ hEC s
              hcode.left hlab.left σ.env (.bool bb) hv hag
            cases bb with
            | true =>
              simp only at hex
              obtain ⟨h₂, str₂, Δ₂, r₂, ag₂, ev₂⟩ := ihn k (by omega) t hokt c₁ ct c₂ hET
                { s with pc := s.pc + cc.length + 1, heap := s.heap }
                (by simpa using h3.left) (by simpa using hl3.left) σ σ' hex hag
              refine ⟨h₂, str₂, Δ₂, ?_, ag₂, ev₂⟩
              have step2 := reaches_jz_untaken (prog := prog) (labels := labels)
                { s with pc := s.pc + cc.length, stack := (1 : Int) :: s.stack }
                s.stack (labelOf c) 1 (by decide) rfl hjz
              have step4 := reaches_jump (prog := prog) (labels := labels)
                { s with pc := s.pc + cc.length + 1 + ct.length, heap := h₂,
                         output := s.output ++ str₂.toUTF8, events := Δ₂ ++ s.events }
                (labelOf (c + 1)) (s.pc + cc.length + 1 + ct.length + 2 + cf.length + 1)
                hend (by simpa using hjump)
              have chain : Reaches (Whitespace.exec prog labels) s
                  { s with pc := s.pc + cc.length + 1 + ct.length + 2 + cf.length + 1,
                           heap := h₂, output := s.output ++ str₂.toUTF8,
                           events := Δ₂ ++ s.events } :=
                reaches_cast
                  (Reaches.trans stepC (Reaches.trans step2 (Reaches.trans r₂ step4)))
                  (by simp)
              rw [hpc] at chain
              exact chain
            | false =>
              simp only at hex
              obtain ⟨h₂, str₂, Δ₂, r₂, ag₂, ev₂⟩ := ihn k (by omega) f hokf c₂ cf c₃ hEF
                { s with pc := s.pc + cc.length + 1 + ct.length + 2, heap := s.heap }
                (by simpa using h5.left) (by simpa using hl5.left) σ σ' hex hag
              refine ⟨h₂, str₂, Δ₂, ?_, ag₂, ev₂⟩
              have step2 := reaches_jz_taken (prog := prog) (labels := labels)
                { s with pc := s.pc + cc.length, stack := (0 : Int) :: s.stack }
                s.stack (labelOf c) (s.pc + cc.length + 1 + ct.length + 2) rfl hels hjz
              have step4 := reaches_label (prog := prog) (labels := labels)
                { s with pc := s.pc + cc.length + 1 + ct.length + 2 + cf.length,
                         heap := h₂, output := s.output ++ str₂.toUTF8,
                         events := Δ₂ ++ s.events }
                (labelOf (c + 1)) (by simpa using hlbl)
              have chain : Reaches (Whitespace.exec prog labels) s
                  { s with pc := s.pc + cc.length + 1 + ct.length + 2 + cf.length + 1,
                           heap := h₂, output := s.output ++ str₂.toUTF8,
                           events := Δ₂ ++ s.events } :=
                reaches_cast
                  (Reaches.trans stepC (Reaches.trans step2 (Reaches.trans r₂ step4)))
                  (by simp)
              rw [hpc] at chain
              exact chain
      | «while» cnd body ihbody =>
        intro hok c code c' hem s hcode hlab σ σ' hex hag
        have hokc : okExpr ns cnd = true := by
          revert hok; simp only [okStmt, Bool.and_eq_true]; tauto
        have hokb : okStmt ns ctx.types body = true := by
          revert hok; simp only [okStmt, Bool.and_eq_true]; tauto
        obtain ⟨cc, c₁, hEC, -, -⟩ := emitsExpr hcov cnd hokc (c + 2)
        obtain ⟨cb, c₂, hEB, -, -⟩ := emitsStmt hcov body hokb c₁
        obtain ⟨hcd, -, -⟩ := Emits.det hem (emitsS_while hEC hEB)
        subst hcd
        have htop : prog[s.pc]? = some (Instr.label (labelOf c)) := hcode.head
        have h2 := hcode.right' (c₁ := [Instr.label (labelOf c)]) (q := s.pc + 1) (by simp)
        have hl2 := hlab.right' (c₁ := [Instr.label (labelOf c)]) (q := s.pc + 1) (by simp)
        have hlTop : labels[labelOf c]? = some (s.pc + 1) := by
          have := hlab 0 (labelOf c) rfl; simpa using this
        have hjz : prog[s.pc + 1 + cc.length]? = some (Instr.jz (labelOf (c + 1))) :=
          (h2.right' (c₁ := cc) rfl).left.head
        have h3 := (h2.right' (c₁ := cc) rfl).right' (c₁ := [Instr.jz (labelOf (c + 1))])
          (q := s.pc + 1 + cc.length + 1) (by simp)
        have hl3 := (hl2.right' (c₁ := cc) rfl).right' (c₁ := [Instr.jz (labelOf (c + 1))])
          (q := s.pc + 1 + cc.length + 1) (by simp)
        have hjump : prog[s.pc + 1 + cc.length + 1 + cb.length]? =
            some (Instr.jump (labelOf c)) := (h3.right' (c₁ := cb) rfl).head
        have hlEnd : labels[labelOf (c + 1)]? =
            some (s.pc + 1 + cc.length + 1 + cb.length + 2) := by
          have := (hl3.right' (c₁ := cb) rfl) 1 (labelOf (c + 1)) rfl
          simpa using this
        have hpc : s.pc + 1 + cc.length + 1 + cb.length + 2
            = s.pc + ([Instr.label (labelOf c)] ++ (cc ++ ([Instr.jz (labelOf (c + 1))] ++
                (cb ++ [Instr.jump (labelOf c), Instr.label (labelOf (c + 1))])))).length := by
          simp only [List.length_append, List.length_cons, List.length_nil]; omega
        have loop : ∀ (m : Nat), m ≤ k + 1 →
            ∀ (τ τ' : Turpentine.State) (heap : Std.HashMap Int Int) (outp : ByteArray)
              (es : List Event),
              Turpentine.exec m (.while cnd body) τ = (τ', Exit.halted) →
              Agrees ctx τ.env heap →
              ∃ (heap' : Std.HashMap Int Int) (str : String) (Δ : List Event),
                Reaches (Whitespace.exec prog labels)
                  { s with pc := s.pc + 1, heap := heap, output := outp, events := es }
                  { s with pc := s.pc + 1 + cc.length + 1 + cb.length + 2, heap := heap',
                           output := outp ++ str.toUTF8, events := Δ ++ es } ∧
                Agrees ctx τ'.env heap' ∧ τ'.events = Δ ++ τ.events := by
          intro m
          induction m with
          | zero =>
            intro _ τ τ' heap outp es hex' _
            rw [Turpentine.exec] at hex'; simp at hex'
          | succ m ihm =>
            intro hm τ τ' heap outp es hex' hag'
            rw [Turpentine.exec] at hex'
            cases hv : Turpentine.evalExpr τ.env cnd with
            | error msg => rw [hv] at hex'; simp at hex'
            | ok w =>
              cases w with
              | int j => rw [hv] at hex'; simp at hex'
              | arr elems => rw [hv] at hex'; simp at hex'
              | bool bb =>
                rw [hv] at hex'
                have stepC := simExpr hcov hg cnd hokc (c + 2) cc c₁ hEC
                  { s with pc := s.pc + 1, heap := heap, output := outp, events := es }
                  (by simpa using h2.left) (by simpa using hl2.left)
                  τ.env (.bool bb) hv hag'
                cases bb with
                | false =>
                  simp only [Prod.mk.injEq] at hex'
                  obtain ⟨hτ, -⟩ := hex'
                  subst hτ
                  refine ⟨heap, "", [], ?_, hag', rfl⟩
                  have step2 := reaches_jz_taken (prog := prog) (labels := labels)
                    { s with pc := s.pc + 1 + cc.length, heap := heap, output := outp,
                             events := es, stack := (0 : Int) :: s.stack }
                    s.stack (labelOf (c + 1))
                    (s.pc + 1 + cc.length + 1 + cb.length + 2) rfl hlEnd
                    (by simpa using hjz)
                  exact reaches_cast (Reaches.trans stepC step2) (by simp)
                | true =>
                  cases heb : Turpentine.exec m body τ with
                  | mk τ₂ ex =>
                    cases ex with
                    | outOfFuel => rw [heb] at hex'; simp at hex'
                    | error msg => rw [heb] at hex'; simp at hex'
                    | halted =>
                      rw [heb] at hex'
                      simp only at hex'
                      obtain ⟨h₂, str₂, Δ₂, r₂, ag₂, ev₂⟩ :=
                        ihn m (by omega) body hokb c₁ cb c₂ hEB
                        { s with pc := s.pc + 1 + cc.length + 1, heap := heap,
                                 output := outp, events := es }
                        (by simpa using h3.left) (by simpa using hl3.left) τ τ₂ heb hag'
                      obtain ⟨h₃, str₃, Δ₃, r₃, ag₃, ev₃⟩ :=
                        ihm (by omega) τ₂ τ' h₂ (outp ++ str₂.toUTF8) (Δ₂ ++ es) hex' ag₂
                      refine ⟨h₃, str₂ ++ str₃, Δ₃ ++ Δ₂, ?_, ag₃,
                        by rw [ev₃, ev₂, List.append_assoc]⟩
                      have step2 := reaches_jz_untaken (prog := prog) (labels := labels)
                        { s with pc := s.pc + 1 + cc.length, heap := heap, output := outp,
                                 events := es, stack := (1 : Int) :: s.stack }
                        s.stack (labelOf (c + 1)) 1 (by decide) rfl (by simpa using hjz)
                      have step4 := reaches_jump (prog := prog) (labels := labels)
                        { s with pc := s.pc + 1 + cc.length + 1 + cb.length, heap := h₂,
                                 output := outp ++ str₂.toUTF8, events := Δ₂ ++ es }
                        (labelOf c) (s.pc + 1) hlTop (by simpa using hjump)
                      exact reaches_cast (Reaches.trans stepC (Reaches.trans step2
                        (Reaches.trans r₂ (Reaches.trans step4 r₃))))
                        (by simp [ByteArray.append_assoc])
        obtain ⟨heap', str, Δ, r, ag, ev⟩ :=
          loop (k + 1) (Nat.le_refl _) σ σ' s.heap s.output s.events hex hag
        refine ⟨heap', str, Δ, ?_, ag, ev⟩
        have step0 := reaches_label (prog := prog) (labels := labels) s (labelOf c) htop
        have chain : Reaches (Whitespace.exec prog labels) s
            { s with pc := s.pc + 1 + cc.length + 1 + cb.length + 2, heap := heap',
                     output := s.output ++ str.toUTF8, events := Δ ++ s.events } :=
          Reaches.trans (reaches_cast step0 (by simp)) r
        rw [hpc] at chain
        exact chain
      | «assert» e =>
        intro hok c code c' hem s hcode hlab σ σ' hex hag
        have hoke : okExpr ns e = true := by simpa [okStmt] using hok
        obtain ⟨ce, c₁, hE, -, -⟩ := emitsExpr hcov e hoke (c + 2)
        obtain ⟨hcd, -, -⟩ := Emits.det hem (emitsS_assert hE)
        subst hcd
        have h2 := hcode.right' (c₁ := ce) rfl
        have hl2 := hlab.right' (c₁ := ce) rfl
        have hjz : prog[s.pc + ce.length]? = some (Instr.jz (labelOf c)) := h2.left.head
        have hjump : prog[s.pc + ce.length + 1]? = some (Instr.jump (labelOf (c + 1))) := by
          have := h2.left.get 1 (by simp); simpa using this
        have hok' : labels[labelOf (c + 1)]? = some (s.pc + ce.length + 6) := by
          have := (h2.right' (c₁ := [Instr.jz (labelOf c), Instr.jump (labelOf (c + 1)),
            Instr.label (labelOf c)]) (q := s.pc + ce.length + 3) (by simp))
          have hl := (hl2.right' (c₁ := [Instr.jz (labelOf c), Instr.jump (labelOf (c + 1)),
            Instr.label (labelOf c)]) (q := s.pc + ce.length + 3) (by simp))
          have := (hl.right' (c₁ := [Instr.push (-1), Instr.retrieve])
            (q := s.pc + ce.length + 5) (by simp)).single
          simpa using this
        have hlbl : prog[s.pc + ce.length + 5]? = some (Instr.label (labelOf (c + 1))) := by
          have := ((h2.right' (c₁ := [Instr.jz (labelOf c), Instr.jump (labelOf (c + 1)),
            Instr.label (labelOf c)]) (q := s.pc + ce.length + 3) (by simp)).right'
            (c₁ := [Instr.push (-1), Instr.retrieve]) (q := s.pc + ce.length + 5) (by simp))
          exact this.head
        have hpc : s.pc + ce.length + 6
            = s.pc + (ce ++ ([Instr.jz (labelOf c), Instr.jump (labelOf (c + 1)),
                Instr.label (labelOf c)] ++ ([Instr.push (-1), Instr.retrieve]
                  ++ [Instr.label (labelOf (c + 1))]))).length := by
          simp only [List.length_append, List.length_cons, List.length_nil]; omega
        rw [Turpentine.exec] at hex
        cases hv : Turpentine.evalExpr σ.env e with
        | error m => rw [hv] at hex; simp at hex
        | ok w =>
          cases w with
          | int m => rw [hv] at hex; simp at hex
          | arr elems => rw [hv] at hex; simp at hex
          | bool bb =>
            rw [hv] at hex
            cases bb with
            | false => simp at hex
            | true =>
              simp only [Prod.mk.injEq] at hex
              obtain ⟨hσ, -⟩ := hex
              subst hσ
              refine ⟨s.heap, "", [], ?_, hag, rfl⟩
              have stepC := simExpr hcov hg e hoke (c + 2) ce c₁ hE s
                hcode.left hlab.left σ.env (.bool true) hv hag
              have step2 := reaches_jz_untaken (prog := prog) (labels := labels)
                { s with pc := s.pc + ce.length, stack := (1 : Int) :: s.stack }
                s.stack (labelOf c) 1 (by decide) rfl hjz
              have step3 := reaches_jump (prog := prog) (labels := labels)
                { s with pc := s.pc + ce.length + 1 }
                (labelOf (c + 1)) (s.pc + ce.length + 6) hok' (by simpa using hjump)
              have chain : Reaches (Whitespace.exec prog labels) s
                  { s with pc := s.pc + ce.length + 6, heap := s.heap,
                           output := s.output ++ "".toUTF8, events := [] ++ s.events } :=
                reaches_cast (Reaches.trans stepC (Reaches.trans step2 step3)) (by simp)
              rw [hpc] at chain
              exact chain
      | assignIndex x i e => intro hok; simp [okStmt] at hok
      | readInt x => intro hok; simp [okStmt] at hok
      | readByte x => intro hok; simp [okStmt] at hok
      | readIntIndex x i => intro hok; simp [okStmt] at hok
      | readByteIndex x i => intro hok; simp [okStmt] at hok
      | printExpr e nl =>
        intro hok c code c' hem s hcode hlab σ σ' hex hag
        have hoke : okExpr ns e = true := by
          revert hok; simp only [okStmt, Bool.and_eq_true]; tauto
        have hpt : okPrintTy ctx.types e = true := by
          revert hok; simp only [okStmt, Bool.and_eq_true]; tauto
        rw [Turpentine.exec] at hex
        cases hv : Turpentine.evalExpr σ.env e with
        | error m => rw [hv] at hex; simp at hex
        | ok w =>
          rw [hv] at hex
          simp only [Prod.mk.injEq] at hex
          obtain ⟨hσ, -⟩ := hex
          rcases okPrintTy_cases hpt with hint | hbool
          · -- `outnum`, then the newline if this was `println`
            obtain ⟨ce, ce', hE, -, -⟩ := emitsExpr hcov e hoke c
            obtain ⟨hcd, -, -⟩ := Emits.det hem (emitsS_printExpr_int hint nl hE)
            subst hcd
            have hwt : valHasTy w Ty.int = true :=
              evalExpr_hasTy hcov hag e Ty.int w hoke hint hv
            cases w with
            | bool b => simp [valHasTy] at hwt
            | arr a => simp [valHasTy] at hwt
            | int m =>
              have hcode' : CodeAt prog s.pc (ce ++ ([Instr.outNum] ++ nlCode nl)) := hcode
              have hstepE := simExpr hcov hg e hoke c ce ce' hE s
                hcode'.left hlab.left σ.env (.int m) hv hag
              have hnum : prog[s.pc + ce.length]? = some Instr.outNum :=
                ((hcode'.right' (c₁ := ce) rfl).left).head
              have hstepN := reaches_outNum (prog := prog) (labels := labels)
                { s with pc := s.pc + ce.length, stack := (m : Int) :: s.stack }
                m s.stack rfl (by simpa using hnum)
              have hcodeNL : CodeAt prog (s.pc + ce.length + 1) (bytesCode (nlBytes nl)) := by
                have := (hcode'.right' (c₁ := ce) rfl).right' (c₁ := [Instr.outNum]) rfl
                rw [← nlCode_eq]
                simpa using this
              obtain ⟨out', hout', hstepNL⟩ :=
                reaches_bytesCode (prog := prog) (labels := labels) (nlBytes nl)
                  ({ s with pc := s.pc + ce.length + 1 }.emitBytes (toString (m : Int)).toUTF8)
                  (by simpa [Whitespace.State.emitBytes] using hcodeNL)
              refine ⟨s.heap, Value.render (.int m) ++ (if nl then "\n" else ""),
                (Trace.ofOutput (outBytes (toString (m : Int)) nl)).reverse, ?_, ?_, ?_⟩
              · refine reaches_cast (Reaches.trans hstepE
                  (Reaches.trans (reaches_cast hstepN (by simp [Whitespace.State.emitBytes]))
                    hstepNL)) ?_
                have hout : out' = s.output
                    ++ (Value.render (Value.int m) ++ (if nl then "\n" else "")).toUTF8 :=
                  bytes_ext (by
                    rw [hout', ByteArray.toList_append]
                    simp only [Whitespace.State.emitBytes, ByteArray.toList_append]
                    rw [show (Value.render (Value.int m) ++ (if nl then "\n" else "")).toUTF8.toList
                        = outBytes (toString (m : Int)) nl from rfl, outBytes_split]
                    simp)
                rw [hout]
                simp only [Whitespace.State.emitBytes, Whitespace.State.mk.injEq,
                  recOut_eq_append, nlCode_eq]
                and_intros <;>
                  first
                    | trivial
                    | (simp only [List.length_append, List.length_cons, List.length_nil,
                        bytesCode_length]; omega)
                    | (rw [outBytes_split]; simp [Trace.ofOutput])
              · rw [← hσ]; exact hag
              · rw [← hσ]
                show Trace.recOut σ.events _ = _
                rw [recOut_eq_append]
                rfl
          · -- the `true`/`false` branch, then the newline
            obtain ⟨ce, ce', hE, -, -⟩ := emitsExpr hcov e hoke (c + 2)
            obtain ⟨hcd, -, -⟩ := Emits.det hem (emitsS_printExpr_bool hbool nl hE)
            subst hcd
            have hwt : valHasTy w Ty.bool = true :=
              evalExpr_hasTy hcov hag e Ty.bool w hoke hbool hv
            cases w with
            | int m => simp [valHasTy] at hwt
            | arr a => simp [valHasTy] at hwt
            | bool b =>
              have h2 := hcode.right' (c₁ := ce) rfl
              have hl2 := hlab.right' (c₁ := ce) rfl
              have hjz : prog[s.pc + ce.length]? = some (Instr.jz (labelOf c)) := h2.left.head
              have h3 := h2.right' (c₁ := [Instr.jz (labelOf c)])
                (q := s.pc + ce.length + 1) (by simp)
              have hl3 := hl2.right' (c₁ := [Instr.jz (labelOf c)])
                (q := s.pc + ce.length + 1) (by simp)
              have h4 := h3.right' (c₁ := bytesCode trueBytes)
                (q := s.pc + ce.length + 1 + 2 * trueBytes.length) (by rw [bytesCode_length])
              have hl4 := hl3.right' (c₁ := bytesCode trueBytes)
                (q := s.pc + ce.length + 1 + 2 * trueBytes.length) (by rw [bytesCode_length])
              have hjump : prog[s.pc + ce.length + 1 + 2 * trueBytes.length]? =
                  some (Instr.jump (labelOf (c + 1))) := h4.left.head
              have hlf : labels[labelOf c]? =
                  some (s.pc + ce.length + 1 + 2 * trueBytes.length + 2) := by
                have := hl4.left 1 (labelOf c) rfl; simpa using this
              have h5 := h4.right' (c₁ := [Instr.jump (labelOf (c + 1)), Instr.label (labelOf c)])
                (q := s.pc + ce.length + 1 + 2 * trueBytes.length + 2) (by simp)
              have hl5 := hl4.right' (c₁ := [Instr.jump (labelOf (c + 1)), Instr.label (labelOf c)])
                (q := s.pc + ce.length + 1 + 2 * trueBytes.length + 2) (by simp)
              have h6 := h5.right' (c₁ := bytesCode falseBytes)
                (q := s.pc + ce.length + 1 + 2 * trueBytes.length + 2 + 2 * falseBytes.length)
                (by rw [bytesCode_length])
              have hl6 := hl5.right' (c₁ := bytesCode falseBytes)
                (q := s.pc + ce.length + 1 + 2 * trueBytes.length + 2 + 2 * falseBytes.length)
                (by rw [bytesCode_length])
              have hlbl : prog[s.pc + ce.length + 1 + 2 * trueBytes.length + 2
                    + 2 * falseBytes.length]? = some (Instr.label (labelOf (c + 1))) :=
                h6.left.head
              have hend : labels[labelOf (c + 1)]? =
                  some (s.pc + ce.length + 1 + 2 * trueBytes.length + 2
                    + 2 * falseBytes.length + 1) := hl6.left.single
              have hcodeNL : CodeAt prog (s.pc + ce.length + 1 + 2 * trueBytes.length + 2
                  + 2 * falseBytes.length + 1) (bytesCode (nlBytes nl)) := by
                have := h6.right' (c₁ := [Instr.label (labelOf (c + 1))])
                  (q := s.pc + ce.length + 1 + 2 * trueBytes.length + 2
                    + 2 * falseBytes.length + 1) (by simp)
                rw [← nlCode_eq]; simpa using this
              have hstepE := simExpr hcov hg e hoke (c + 2) ce ce' hE s
                hcode.left hlab.left σ.env (.bool b) hv hag
              have hpcend : s.pc + ce.length + 1 + 2 * trueBytes.length + 2
                    + 2 * falseBytes.length + 1 + 2 * (nlBytes nl).length
                  = s.pc + (ce ++ ([Instr.jz (labelOf c)] ++ (bytesCode trueBytes ++
                      ([Instr.jump (labelOf (c + 1)), Instr.label (labelOf c)] ++
                        (bytesCode falseBytes ++
                          ([Instr.label (labelOf (c + 1))] ++ nlCode nl)))))).length := by
                simp only [List.length_append, List.length_cons, List.length_nil,
                  bytesCode_length, nlCode_eq]
                omega
              refine ⟨s.heap, Value.render (.bool b) ++ (if nl then "\n" else ""),
                (Trace.ofOutput (outBytes (toString b) nl)).reverse, ?_, ?_, ?_⟩
              · cases b with
                | true =>
                  obtain ⟨o₁, ho₁, r₁⟩ :=
                    reaches_bytesCode (prog := prog) (labels := labels) trueBytes
                      { s with pc := s.pc + ce.length + 1 } (by simpa using h3.left)
                  obtain ⟨o₂, ho₂, r₂⟩ :=
                    reaches_bytesCode (prog := prog) (labels := labels) (nlBytes nl)
                      { s with pc := s.pc + ce.length + 1 + 2 * trueBytes.length + 2
                                 + 2 * falseBytes.length + 1,
                               output := o₁,
                               events := Trace.recOut s.events trueBytes } hcodeNL
                  have step2 := reaches_jz_untaken (prog := prog) (labels := labels)
                    { s with pc := s.pc + ce.length, stack := (1 : Int) :: s.stack }
                    s.stack (labelOf c) 1 (by decide) rfl hjz
                  have step4 := reaches_jump (prog := prog) (labels := labels)
                    { s with pc := s.pc + ce.length + 1 + 2 * trueBytes.length,
                             output := o₁, events := Trace.recOut s.events trueBytes }
                    (labelOf (c + 1))
                    (s.pc + ce.length + 1 + 2 * trueBytes.length + 2
                      + 2 * falseBytes.length + 1) hend (by simpa using hjump)
                  refine reaches_cast (Reaches.trans hstepE (Reaches.trans step2
                    (Reaches.trans r₁ (Reaches.trans step4 r₂)))) ?_
                  have hout : o₂ = s.output
                      ++ (Value.render (Value.bool true) ++ (if nl then "\n" else "")).toUTF8 :=
                    bytes_ext (by
                      rw [ho₂, ho₁, ByteArray.toList_append,
                        show (Value.render (Value.bool true)
                            ++ (if nl then "\n" else "")).toUTF8.toList
                          = outBytes (toString true) nl from rfl, outBytes_split]
                      simp [trueBytes, toString_true])
                  rw [hout]
                  simp only [Whitespace.State.mk.injEq, recOut_eq_append]
                  and_intros <;>
                    first
                      | trivial
                      | omega
                      | (rw [outBytes_split]
                         simp [Trace.ofOutput, trueBytes, toString_true])
                | false =>
                  obtain ⟨o₁, ho₁, r₁⟩ :=
                    reaches_bytesCode (prog := prog) (labels := labels) falseBytes
                      { s with pc := s.pc + ce.length + 1 + 2 * trueBytes.length + 2 }
                      (by simpa using h5.left)
                  obtain ⟨o₂, ho₂, r₂⟩ :=
                    reaches_bytesCode (prog := prog) (labels := labels) (nlBytes nl)
                      { s with pc := s.pc + ce.length + 1 + 2 * trueBytes.length + 2
                                 + 2 * falseBytes.length + 1,
                               output := o₁,
                               events := Trace.recOut s.events falseBytes } hcodeNL
                  have step2 := reaches_jz_taken (prog := prog) (labels := labels)
                    { s with pc := s.pc + ce.length, stack := (0 : Int) :: s.stack }
                    s.stack (labelOf c)
                    (s.pc + ce.length + 1 + 2 * trueBytes.length + 2) rfl hlf hjz
                  have step4 := reaches_label (prog := prog) (labels := labels)
                    { s with pc := s.pc + ce.length + 1 + 2 * trueBytes.length + 2
                               + 2 * falseBytes.length,
                             output := o₁, events := Trace.recOut s.events falseBytes }
                    (labelOf (c + 1)) (by simpa using hlbl)
                  refine reaches_cast (Reaches.trans hstepE (Reaches.trans step2
                    (Reaches.trans r₁ (Reaches.trans step4 r₂)))) ?_
                  have hout : o₂ = s.output
                      ++ (Value.render (Value.bool false) ++ (if nl then "\n" else "")).toUTF8 :=
                    bytes_ext (by
                      rw [ho₂, ho₁, ByteArray.toList_append,
                        show (Value.render (Value.bool false)
                            ++ (if nl then "\n" else "")).toUTF8.toList
                          = outBytes (toString false) nl from rfl, outBytes_split]
                      simp [falseBytes, toString_false])
                  rw [hout]
                  simp only [Whitespace.State.mk.injEq, recOut_eq_append]
                  and_intros <;>
                    first
                      | trivial
                      | omega
                      | (rw [outBytes_split]
                         simp [Trace.ofOutput, falseBytes, toString_false])
              · rw [← hσ]; exact hag
              · rw [← hσ]
                show Trace.recOut σ.events _ = _
                rw [recOut_eq_append]
                rfl
      | printStr str nl =>
        intro _ c code c' hem s hcode hlab σ σ' hex hag
        obtain ⟨hcd, -, -⟩ := Emits.det hem (emitsS_printStr ctx str nl c)
        subst hcd
        rw [Turpentine.exec] at hex
        simp only [Prod.mk.injEq] at hex
        obtain ⟨hσ, -⟩ := hex
        obtain ⟨out', hout', r⟩ := reaches_bytesCode (outBytes str nl) s hcode
        refine ⟨s.heap, str ++ (if nl then "\n" else ""),
          (Trace.ofOutput (outBytes str nl)).reverse, ?_, ?_, ?_⟩
        · refine reaches_cast r ?_
          have hout : out' = s.output ++ (str ++ (if nl then "\n" else "")).toUTF8 :=
            bytes_ext (by rw [hout', ByteArray.toList_append]; rfl)
          rw [hout, recOut_eq_append, bytesCode_length]
        · rw [← hσ]; exact hag
        · rw [← hσ]
          show Trace.recOut σ.events _ = _
          rw [recOut_eq_append]
          rfl
      | printByte e => intro hok; simp [okStmt] at hok


/-! ## The compiler

`bespokeWhitespace.compile` is the hand-written backend's `compileChecked`,
gated by a fragment check and applied to the source program with one
statement appended: `print(answer)`. The appended statement is what turns the
specification's single `Nat` into something observable, since a Turpentine
program in the fragment prints nothing of its own.

The typing context is built here rather than by `Turpentine.checkProgram`.
The backend consults it in exactly one place, to choose between `outnum` and
the `true`/`false` branch of `print`, and the fragment check already
guarantees what that lookup needs. -/

/-- The variable the specification reads the answer out of. -/
def answerVar : String := "answer"

def declNames (p : Program) : List String := p.decls.map (·.1)

def okDecl (d : String × Ty × Option Expr) : Bool := scalarTy d.2.1 && d.2.2.isNone

def nodupB : List String → Bool
  | [] => true
  | x :: rest => !rest.contains x && nodupB rest

theorem nodupB_spec : ∀ {l : List String}, nodupB l = true → l.Nodup := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons x rest ih =>
    intro h
    rw [nodupB, Bool.and_eq_true] at h
    refine List.nodup_cons.mpr ⟨?_, ih h.2⟩
    intro hc
    have hcon : rest.contains x = true := by simpa using hc
    rw [hcon] at h
    simp at h

/-- `Ty` derives `BEq` but no `LawfulBEq`, so the check uses a plain
predicate that is easy to invert. -/
def isIntTy : Ty → Bool
  | .int => true
  | _ => false

theorem isIntTy_eq {t : Ty} (h : isIntTy t = true) : t = Ty.int := by
  cases t <;> first | rfl | simp [isIntTy] at h

def hasAnswerInt (p : Program) : Bool :=
  p.decls.any fun d => d.1 == answerVar && isIntTy d.2.1

/-- The typing context, read off the declarations. -/
def typesOf (p : Program) : Types := typesGo p.decls ∅

/-- The fragment check. Each rejection names what took the program outside
the part of the language this file proves the backend correct on. -/
def checkFragment (p : Program) : Except String Unit :=
  if !p.decls.all okDecl then
    .error "outside the verified whitespace fragment: every declaration must be a scalar \
      'int' or 'bool' with no initialiser"
  else if !nodupB (declNames p) then
    .error "outside the verified whitespace fragment: declaration names must be distinct"
  else if !hasAnswerInt p then
    .error "the verified whitespace fragment needs a declaration 'var answer : int;': \
      the specification names the answer by that variable"
  else if !okStmt (declNames p) (typesOf p) p.body then
    .error "outside the verified whitespace fragment: the body reads input, prints a \
      byte, uses an array, '/' or '%', or assigns a value of the wrong type"
  else .ok ()

/-! ### Reading the answer back, from a program that prints for itself

`Langlib.Computability.URMWhitespace.decodeOutput` reads the *whole* output
as a decimal numeral. That is right for the derived compilers, whose
programs print nothing but the answer, and wrong here as soon as the
fragment admits `print`: the answer would be buried in whatever the program
said first.

So the epilogue is `println(""); print(answer);` and the decoder reads the
digits after the **last** newline. This needs no extra restriction on the
fragment, because `toString (answer : Nat)` is all digits: the epilogue's
newline is provably the last byte of its kind in the output, whatever the
program printed before it. -/

/-- The characters after the last newline, or all of them if there is
none. -/
def afterLastNewline (cs : List Char) : List Char :=
  (cs.reverse.takeWhile (· != '\n')).reverse

/-- The decoder: the digits the epilogue printed, read as a decimal
numeral. -/
def decodeAnswer (b : ByteArray) : Option Nat :=
  match String.fromUTF8? b with
  | none => none
  | some s => Langlib.Computability.URMWhitespace.decodeDecimal (afterLastNewline s.toList)

/-- A digit is not a newline. -/
theorem digit_ne_nl {c : Char} (h : c.isDigit = true) : c ≠ '\n' := by
  intro hc
  rw [hc] at h
  exact absurd h (by decide)

/-- Every character of a decimal rendering is a digit. -/
theorem toDigits_isDigit (n : Nat) : ∀ c ∈ Nat.toDigits 10 n, c.isDigit = true := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [Nat.toDigits_eq_if (by omega)]
    split
    · rename_i hlt
      intro c hc
      rw [List.mem_singleton] at hc
      subst hc
      simp [Nat.isDigit_digitChar, hlt]
    · rename_i hge
      intro c hc
      rcases List.mem_append.mp hc with h | h
      · exact ih (n / 10) (Nat.div_lt_self (by omega) (by omega)) c h
      · rw [List.mem_singleton] at h
        subst h
        simp [Nat.isDigit_digitChar, Nat.mod_lt _ (by omega : 0 < 10)]

/-- `takeWhile` stops at the first element that fails, and nothing before it
does. -/
theorem takeWhile_upto {α : Type} {p : α → Bool} {x : α} {l₁ l₂ : List α}
    (hx : p x = false) (h : ∀ c ∈ l₁, p c = true) :
    (l₁ ++ x :: l₂).takeWhile p = l₁ := by
  induction l₁ with
  | nil => simp [hx]
  | cons a as ih =>
    have ha : p a = true := h a (by simp)
    simp only [List.cons_append, List.takeWhile_cons, ha, if_true]
    rw [ih (fun c hc => h c (by simp [hc]))]

/-- Digits after the last newline are the digits after *that* newline. -/
theorem afterLastNewline_digits (pre ds : List Char)
    (h : ∀ c ∈ ds, c.isDigit = true) :
    afterLastNewline (pre ++ '\n' :: ds) = ds := by
  have hrev : (pre ++ '\n' :: ds).reverse = ds.reverse ++ '\n' :: pre.reverse := by
    simp
  rw [afterLastNewline, hrev,
    takeWhile_upto (p := (· != '\n')) (by decide)
      (fun c hc => by
        have := h c (by simpa using List.mem_reverse.mp hc)
        simpa using digit_ne_nl this),
    List.reverse_reverse]

/-- **The decoder inverts the epilogue.** Whatever the program printed
first, the digits after the last newline are the answer. -/
theorem decodeAnswer_epilogue (pre : String) (n : Nat) :
    decodeAnswer ((pre ++ "\n" ++ toString ((n : Nat) : Int)).toUTF8) = some n := by
  have hstr : toString ((n : Nat) : Int) = Nat.repr n := by simp [Int.repr_eq_if]
  rw [decodeAnswer, Langlib.Computability.URMWhitespace.fromUTF8?_toUTF8, hstr]
  simp only []
  rw [show ((pre ++ "\n" ++ Nat.repr n).toList)
      = pre.toList ++ '\n' :: (Nat.repr n).toList from by
    rw [String.toList_append, String.toList_append]
    simp [show "\n".toList = ['\n'] from rfl]]
  rw [Nat.toList_repr, afterLastNewline_digits _ _ (toDigits_isDigit n),
    Langlib.Computability.URMWhitespace.decodeDecimal_toDigits]

/-- The source program with `println(""); print(answer);` appended: the
newline is what makes the answer findable in an output the program has
already written to. -/
def answerProgram (p : Program) : Program :=
  { p with body := .seq p.body (.seq (.printStr "" true)
      (.printExpr (.var answerVar) false)) }

/-- **The compiler.** The fragment check, then the hand-written backend. -/
def bespokeCompile (p : Program) : Except String Prog := do
  let _ ← checkFragment p
  Turpentine.Compile.Whitespace.compileChecked (answerProgram p) (typesOf p)

theorem checkFragment_ok {p : Program} (h : checkFragment p = .ok ()) :
    (∀ d ∈ p.decls, scalarTy d.2.1 = true) ∧ (∀ d ∈ p.decls, d.2.2 = none) ∧
    (declNames p).Nodup ∧
    (∃ d, d ∈ p.decls ∧ d.1 = answerVar ∧ d.2.1 = Ty.int) ∧
    okStmt (declNames p) (typesOf p) p.body = true := by
  rw [checkFragment] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · rename_i h1 h2 h3 h4
          simp only [Bool.not_eq_true'] at h1 h2 h3 h4
          have hall : ∀ d ∈ p.decls, okDecl d = true := by
            have : p.decls.all okDecl = true := by
              cases hb : p.decls.all okDecl
              · rw [hb] at h1; simp at h1
              · rfl
            exact fun d hd => (List.all_eq_true.mp this) d hd
          refine ⟨fun d hd => ?_, fun d hd => ?_, ?_, ?_, ?_⟩
          · have := hall d hd; rw [okDecl, Bool.and_eq_true] at this; exact this.1
          · have := hall d hd
            rw [okDecl, Bool.and_eq_true] at this
            exact Option.isNone_iff_eq_none.mp (by simpa using this.2)
          · refine nodupB_spec ?_
            cases hb : nodupB (declNames p)
            · rw [hb] at h2; simp at h2
            · rfl
          · have hb : hasAnswerInt p = true := by
              cases hb : hasAnswerInt p
              · rw [hb] at h3; simp at h3
              · rfl
            rw [hasAnswerInt, List.any_eq_true] at hb
            obtain ⟨d, hd, hcond⟩ := hb
            rw [Bool.and_eq_true, beq_iff_eq] at hcond
            exact ⟨d, hd, hcond.1, isIntTy_eq hcond.2⟩
          · cases hb : okStmt (declNames p) (typesOf p) p.body
            · rw [hb] at h4; simp at h4
            · rfl

theorem emitsS_printAnswer {ctx : Frame} {a : Int}
    (ha : ctx.addrs[answerVar]? = some a) (ht : ctx.types[answerVar]? = some Ty.int)
    (c : Nat) :
    Emits (compileStmt ctx (.printExpr (.var answerVar) false)) c
      ([Instr.push a, Instr.retrieve] ++ ([Instr.outNum] ++ [])) c PUnit.unit := by
  have hinfer : inferExpr ctx.types (.var answerVar) = .ok Ty.int := by
    rw [inferExpr, ht]; rfl
  have h0 : compileStmt ctx (.printExpr (.var answerVar) false)
      = (match inferExpr ctx.types (.var answerVar) with
         | .error m => throw s!"type error in a printed expression: {m}"
         | .ok .int => do
            compileExpr ctx (.var answerVar)
            emit Instr.outNum
            if false then emitStr "\n"
         | .ok .bool => do
            let f ← fresh
            let end_ ← fresh
            compileExpr ctx (.var answerVar)
            emit (Instr.jz f)
            emitStr "true"
            emits [Instr.jump end_, Instr.label f]
            emitStr "false"
            emit (Instr.label end_)
            if false then emitStr "\n"
         | .ok (.array _ _) => throw "internal: printing a whole array") := rfl
  have he : compileStmt ctx (.printExpr (.var answerVar) false)
      = (compileExpr ctx (.var answerVar) >>= fun _ =>
          emit Instr.outNum >>= fun _ => (Pure.pure PUnit.unit : M PUnit)) := by
    rw [h0, hinfer]; rfl
  rw [he]
  exact Emits.seq (emitsE_var ha c) (Emits.seq (emits_emit _ c) (Emits.pure _ c))

/-! ## The end-to-end theorem -/

/-- The answer convention, spelled out: within fuel `n`, `p` halts on empty
input with `result` in the variable `answer`. This is
`Langlib.Turpentine.Compile.URM.TurpentineHaltsWith`, repeated so that the
proof below does not depend on the certified pipeline's file. -/
def HaltsWithAnswer (p : Program) (n : Nat) (result : Nat) : Prop :=
  ∃ (env₀ : Std.HashMap String Value) (st : Turpentine.State),
    Turpentine.initEnv p = .ok env₀ ∧
    Turpentine.exec n p.body { env := env₀, input := Input.ofString "" } =
      (st, Exit.halted) ∧
    st.env[answerVar]? = some (Value.int (result : Int))


/-- The compile-time frame the backend builds for a program. -/
def frameOf (p : Program) (types : Types) : Frame :=
  { addrs := (layoutGo p.decls (∅, 0)).1, types := types,
    tmpA := (layoutGo p.decls (∅, 0)).2, tmpB := (layoutGo p.decls (∅, 0)).2 + 1,
    tmpI := (layoutGo p.decls (∅, 0)).2 + 2, oob := "S" }

/-- The generator the backend runs, for an array-free program. -/
def genOf (p : Program) (types : Types) : M Unit :=
  forIn (m := M) p.decls PUnit.unit (genBody (frameOf p types)) >>= fun _ =>
    compileStmt (frameOf p types) p.body >>= fun _ =>
      emit Instr.halt >>= fun _ => (Pure.pure PUnit.unit : M PUnit)

theorem compileChecked_of_gen (p : Program) (types : Types) (W : List Instr) (cf : Nat)
    (harr : (p.decls.any fun d => match d.2.1 with | .array _ _ => true | _ => false) = false)
    (hgen : Emits (genOf p types) 0 W cf PUnit.unit) :
    compileChecked p types = .ok W.toArray := by
  rw [compileChecked_unfold, layout_forIn]
  show ((StateT.run (forIn (m := M) p.decls PUnit.unit (genBody (frameOf p types)) >>= fun _ =>
      compileStmt (frameOf p types) p.body >>= fun _ =>
        emit Instr.halt >>= fun _ =>
          (if (p.decls.any fun d => match d.2.1 with | .array _ _ => true | _ => false) = true
           then emitOobTrap (frameOf p types) else Pure.pure PUnit.unit)) {}) >>=
      fun x => Pure.pure x.2.out) = .ok W.toArray
  rw [harr]
  have h : StateT.run (genOf p types) (⟨([] : List Instr).toArray, 0⟩ : St)
      = .ok (PUnit.unit, (⟨(([] : List Instr) ++ W).toArray, cf⟩ : St)) := hgen []
  simp only [List.nil_append] at h
  show (StateT.run (genOf p types) (⟨([] : List Instr).toArray, 0⟩ : St) >>=
      fun x => Pure.pure x.2.out) = .ok W.toArray
  rw [h]
  rfl

/-- **The theorem.** On a program the fragment check accepts, whenever the
source halts within some fuel bound with `result` in `answer`, the compiled
whitespace program halts, for some fuel bound, having printed whatever the
source printed and then `result` in decimal on a line of its own. -/
theorem bespokeCompile_correct (p : Program) (prog : Prog) (result n : Nat)
    (hc : bespokeCompile p = .ok prog) (hp : HaltsWithAnswer p n result) :
    ∃ m, (Whitespace.evalProg prog (Input.ofString "") m).exit = Exit.halted ∧
      decodeAnswer (Whitespace.evalProg prog (Input.ofString "") m).output = some result := by
  obtain ⟨env₀, st, hinit, hex, hans⟩ := hp
  have hcf : checkFragment p = .ok () := by
    cases hq : checkFragment p with
    | error msg =>
      rw [bespokeCompile, hq] at hc
      simp [exc_bind_err] at hc
    | ok u => rfl
  have hcomp : compileChecked (answerProgram p) (typesOf p) = .ok prog := by
    rw [bespokeCompile, hcf] at hc
    exact hc
  obtain ⟨hsc, hno, hnd, ⟨dA, hdA, hdAn, hdAt⟩, hokbody⟩ := checkFragment_ok hcf
  -- the frame
  have hlay := layoutGo_ok p.decls hsc hnd ∅ 0
    ⟨le_refl (0 : Int), by intro x a h; simp at h, by intro x y a h; simp at h⟩
    (by intro d _; simp)
  set ctx : Frame := frameOf (answerProgram p) (typesOf p) with hctx
  have hgf : GoodFrame ctx :=
    ⟨fun x a h => (hlay.1.bound x a h).1, fun x y a h₁ h₂ => hlay.1.injv x y a h₁ h₂⟩
  have hcov : Covers ctx (declNames p) := fun x hx => hlay.2 x hx
  have hcovd : ∀ d ∈ p.decls, ∃ a, ctx.addrs[d.1]? = some a :=
    fun d hd => hcov d.1 (List.mem_map_of_mem hd)
  obtain ⟨aA, haA⟩ := hcov answerVar (hdAn ▸ List.mem_map_of_mem hdA)
  have hAty : ctx.types[answerVar]? = some Ty.int := by
    have h := typesGo_get p.decls hnd ∅ dA hdA
    rw [hdAn, hdAt] at h
    exact h
  -- what the generator emits
  obtain ⟨dcode, hdem, hdlab, hdsim⟩ := emits_declLoop ctx hgf p.decls hsc hno hcovd 0
  obtain ⟨bcode, c₁, hbem, hble, hbcl⟩ := emitsStmt hcov p.body hokbody 0
  have hpem := emitsS_printAnswer haA hAty c₁
  have hnlem : Emits (compileStmt ctx (.printStr "" true)) c₁ (bytesCode [10]) c₁ PUnit.unit := by
    have h := emitsS_printStr ctx "" true c₁
    rwa [show outBytes "" true = [10] from by
      rw [outBytes_eq]; simp] at h
  have hsem : Emits (compileStmt ctx (answerProgram p).body) 0
      (bcode ++ (bytesCode [10]
        ++ ([Instr.push aA, Instr.retrieve] ++ ([Instr.outNum] ++ [])))) c₁ PUnit.unit :=
    emitsS_seq hbem (emitsS_seq hnlem hpem)
  have hWem : Emits (genOf (answerProgram p) (typesOf p)) 0
      (dcode ++ ((bcode ++ (bytesCode [10]
        ++ ([Instr.push aA, Instr.retrieve] ++ ([Instr.outNum] ++ []))))
        ++ ([Instr.halt] ++ []))) c₁ PUnit.unit :=
    Emits.seq hdem (Emits.seq hsem
      (Emits.seq (emits_emit Instr.halt c₁) (Emits.pure _ c₁)))
  have harr : ((answerProgram p).decls.any fun d =>
      match d.2.1 with | .array _ _ => true | _ => false) = false := by
    have hz : ∀ d ∈ p.decls,
        (match d.2.1 with | .array _ _ => true | _ => false) = false := by
      intro d hd
      have h := hsc d hd
      cases hty : d.2.1 with
      | int => rfl
      | bool => rfl
      | array e m => rw [hty] at h; simp [scalarTy] at h
    cases hb : (answerProgram p).decls.any fun d =>
        match d.2.1 with | .array _ _ => true | _ => false with
    | false => rfl
    | true =>
      rw [List.any_eq_true] at hb
      obtain ⟨d, hd, hdt⟩ := hb
      rw [hz d hd] at hdt
      simp at hdt
  have hprogeq : prog = (dcode ++ ((bcode ++ (bytesCode [10]
      ++ ([Instr.push aA, Instr.retrieve] ++ ([Instr.outNum] ++ []))))
      ++ ([Instr.halt] ++ []))).toArray := by
    have h := compileChecked_of_gen (answerProgram p) (typesOf p) _ c₁ harr hWem
    rw [hcomp] at h
    exact Except.ok.inj h
  subst hprogeq
  set pcode : List Instr := [Instr.push aA, Instr.retrieve] ++ ([Instr.outNum] ++ [])
    with hpcode
  set W : List Instr :=
    dcode ++ ((bcode ++ (bytesCode [10] ++ pcode)) ++ ([Instr.halt] ++ [])) with hW
  set labels := Whitespace.labelMap W.toArray with hlabels
  have hcodeW : CodeAt W.toArray 0 W := by intro j hj; simp
  have hclean : Clean 0 c₁ W := by
    refine Clean.appendUp (Nat.le_refl 0) (Nat.zero_le c₁) (Clean.ofNoLabels hdlab) ?_
    refine Clean.appendUp (Nat.zero_le c₁) (Nat.le_refl c₁) ?_ (Clean.ofNoLabels rfl)
    exact Clean.appendUp (Nat.zero_le c₁) (Nat.le_refl c₁) hbcl
      (Clean.ofNoLabels (by simp [bytesCode, labelIdxs, labelsOf, hpcode]))
  have hlabW : LabelsOk labels 0 W := labelsOk_of_nodup W hclean.labels_nodup
  -- the initial state
  set s₀ : Whitespace.State :=
    ⟨[], [], ∅, Input.ofString "", ByteArray.empty, 0, []⟩ with hs₀
  -- the prologue
  obtain ⟨heap₁, r₁, hz₁⟩ := hdsim W.toArray labels s₀ hcodeW.left zeroHeap_empty
  -- the environment the declarations leave behind
  have henv : initGo p.decls ∅ = env₀ := by
    rw [initEnv_unfold, initEnv_forIn p.decls hno] at hinit
    exact Except.ok.inj hinit
  have hag : Agrees ctx env₀ heap₁ :=
    agrees_of_zero hz₁ (henv ▸ initGo_zero p.decls ∅ allZeroEnv_empty)
      (fun x t v ht hv => initGo_typesGo p.decls ∅ ∅
        (by intro y u w hu _; simp at hu) x t v ht (henv ▸ hv))
  -- the body
  have hcodeB : CodeAt W.toArray (0 + dcode.length) bcode :=
    ((hcodeW.right' (c₁ := dcode) rfl).left).left
  have hlabB : LabelsOk labels (0 + dcode.length) bcode :=
    ((hlabW.right' (c₁ := dcode) rfl).left).left
  obtain ⟨heap₂, str, Δ, r₂, hag₂, -⟩ := simStmt hcov hgf n p.body hokbody 0 bcode c₁ hbem
    { s₀ with pc := 0 + dcode.length, heap := heap₁ } hcodeB hlabB
    { env := env₀, input := Input.ofString "" } st hex hag
  -- the answer, printed
  have hval : heap₂.getD aA 0 = (result : Int) := (hag₂ answerVar aA haA _ hans).1
  -- the epilogue: first its newline, which is what makes the answer findable
  have hcodeX : CodeAt W.toArray (0 + dcode.length + bcode.length) (bytesCode [10] ++ pcode) :=
    ((hcodeW.right' (c₁ := dcode) rfl).left).right' (c₁ := bcode) rfl
  obtain ⟨outNL, houtNL, rNL⟩ :=
    reaches_bytesCode (prog := W.toArray) (labels := labels) [10]
      { s₀ with pc := 0 + dcode.length + bcode.length, heap := heap₂,
                output := s₀.output ++ str.toUTF8, events := Δ ++ s₀.events }
      hcodeX.left
  -- then the answer itself, from the state the newline left behind
  have rNL' : Reaches (Whitespace.exec W.toArray labels)
      { s₀ with pc := 0 + dcode.length + bcode.length, heap := heap₂,
                output := s₀.output ++ str.toUTF8, events := Δ ++ s₀.events }
      { s₀ with pc := 0 + dcode.length + bcode.length + 2, heap := heap₂,
                output := outNL, events := Trace.recOut (Δ ++ s₀.events) [10] } :=
    reaches_cast rNL (by simp)
  have hcodeP : CodeAt W.toArray (0 + dcode.length + bcode.length + 2) pcode :=
    hcodeX.right' (c₁ := bytesCode [10]) (by simp [bytesCode])
  have hp0 : (W.toArray)[0 + dcode.length + bcode.length + 2]? = some (Instr.push aA) :=
    hcodeP.head
  have hp1 : (W.toArray)[0 + dcode.length + bcode.length + 2 + 1]? = some Instr.retrieve := by
    have := hcodeP.get 1 (by simp [hpcode]); simpa [hpcode] using this
  have hp2 : (W.toArray)[0 + dcode.length + bcode.length + 2 + 2]? = some Instr.outNum := by
    have := hcodeP.get 2 (by simp [hpcode]); simpa [hpcode] using this
  have hhalt : (W.toArray)[0 + dcode.length + bcode.length + 2 + 3]? = some Instr.halt := by
    have h := ((hcodeW.right' (c₁ := dcode) rfl).right'
      (c₁ := bcode ++ (bytesCode [10] ++ pcode))
      (q := 0 + dcode.length + bcode.length + 2 + 3)
      (by simp only [List.length_append, List.length_cons, List.length_nil, hpcode,
        bytesCode_length]; omega)).head
    exact h
  have step1 := reaches_push (prog := W.toArray) (labels := labels)
    { s₀ with pc := 0 + dcode.length + bcode.length + 2, heap := heap₂,
              output := outNL, events := Trace.recOut (Δ ++ s₀.events) [10] } aA hp0
  have step2 := reaches_retrieve (prog := W.toArray) (labels := labels)
    { s₀ with pc := 0 + dcode.length + bcode.length + 2 + 1, heap := heap₂,
              output := outNL, events := Trace.recOut (Δ ++ s₀.events) [10],
              stack := [aA] } aA [] rfl
    (hgf.nonneg answerVar aA haA) (by simpa using hp1)
  have step3 := reaches_outNum (prog := W.toArray) (labels := labels)
    { s₀ with pc := 0 + dcode.length + bcode.length + 2 + 1 + 1, heap := heap₂,
              output := outNL, events := Trace.recOut (Δ ++ s₀.events) [10],
              stack := [heap₂.getD aA 0] } (heap₂.getD aA 0) [] rfl (by simpa using hp2)
  have chain : Reaches (Whitespace.exec W.toArray labels) s₀
      { s₀ with pc := 0 + dcode.length + bcode.length + 2 + 3, heap := heap₂,
                output := outNL ++ (toString ((result : Nat) : Int)).toUTF8,
                events := Trace.recOut (Trace.recOut (Δ ++ s₀.events) [10])
                  ((toString ((result : Nat) : Int)).toUTF8).toList } := by
    have h := Reaches.trans r₁ (Reaches.trans r₂ (Reaches.trans rNL'
      (Reaches.trans step1 (Reaches.trans step2 step3))))
    rw [hval] at h
    exact h
  obtain ⟨cst, hcst⟩ := chain
  refine ⟨cst + 1, ?_⟩
  simp only [Whitespace.evalProg]
  rw [show ({ input := Input.ofString "" } : Whitespace.State) = s₀ from rfl]
  rw [show Whitespace.exec W.toArray (Whitespace.labelMap W.toArray) (cst + 1) s₀
      = Whitespace.exec W.toArray labels (cst + 1) s₀ from rfl, hcst 1,
    exec_halt (prog := W.toArray) (labels := labels) _ (by simpa using hhalt) 0]
  refine ⟨rfl, ?_⟩
  -- the output is what the program printed, then a newline, then the answer
  have houteq : outNL ++ (toString ((result : Nat) : Int)).toUTF8
      = (str ++ "\n" ++ toString ((result : Nat) : Int)).toUTF8 := by
    refine bytes_ext ?_
    rw [ByteArray.toList_append, houtNL, toUTF8_toList_append, toUTF8_toList_append,
      newline_bytes]
    simp [hs₀, ByteArray.toList_eq]
  rw [houteq]
  exact decodeAnswer_epilogue str result

end Langlib.Turpentine.Certified.BespokeWhitespace

namespace Langlib.Turpentine.Certified

open Langlib.Common
open Langlib.Computability (WhitespaceLang)
open Langlib.Turpentine.Compile.URM (TurpentineHaltsWith)
open Langlib.Turpentine.Compile (TurpentineCompiler derivedWhitespace)

/-- **The hand-written Turpentine-to-Whitespace backend, as a verified
compiler.** `compile` is `Langlib.Turpentine.Compile.Whitespace`'s own
`compileChecked`, gated by the fragment check of
`Langlib.Turpentine.Certified.BespokeWhitespace` and applied to the source
program with `print(answer)` appended.

The second inhabitant of `TurpentineCompiler WhitespaceLang`, and the first
one that is not derived from a completeness proof. -/
def bespokeWhitespace : TurpentineCompiler WhitespaceLang where
  compile := BespokeWhitespace.bespokeCompile
  encodeInput := Input.ofString ""
  decodeOutput := BespokeWhitespace.decodeAnswer
  correct := fun p prog result n hc hp =>
    BespokeWhitespace.bespokeCompile_correct p prog result n hc hp

/-- **The derived compiler is no longer an untested oracle.** On a Turpentine
program both compilers accept and a source run that halts with `result` in
`answer`, the hand-written backend and the compiler derived from
`whitespaceComplete` both halt and their outputs decode to the same answer.

This is `agree` instantiated at the two inhabitants; the content is the two
`correct` fields, one proved in `Langlib/Computability/Whitespace.lean` and
one proved here. -/
theorem bespokeWhitespace_agrees_derived (p : Turpentine.Program)
    (prog₁ prog₂ : ProgLang.Prog WhitespaceLang) (result n : Nat)
    (h₁ : bespokeWhitespace.compile p = .ok prog₁)
    (h₂ : derivedWhitespace.compile p = .ok prog₂)
    (hp : TurpentineHaltsWith p n result) :
    ∃ m₁ m₂,
      (ProgLang.run prog₁ bespokeWhitespace.encodeInput m₁).exit = Exit.halted ∧
      (ProgLang.run prog₂ derivedWhitespace.encodeInput m₂).exit = Exit.halted ∧
      bespokeWhitespace.decodeOutput
          (ProgLang.run prog₁ bespokeWhitespace.encodeInput m₁).output =
        derivedWhitespace.decodeOutput
          (ProgLang.run prog₂ derivedWhitespace.encodeInput m₂).output :=
  CertifiedCompiler.agree bespokeWhitespace derivedWhitespace p prog₁ prog₂ result n h₁ h₂ hp

end Langlib.Turpentine.Certified
