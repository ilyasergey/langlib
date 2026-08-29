import Langlib.Common.Fuel
import Langlib.Computability.Class
import Langlib.Computability.URM
import Langlib.Languages.Whitespace

/-!
# Whitespace is Turing complete

This file compiles an arbitrary unlimited register machine into Whitespace
and proves the simulation, giving the term `whitespaceComplete :
TuringComplete Whitespace` that is langlib's statement of the result.

## The translation

A URM register `r` is the Whitespace heap cell at address `r`. A URM
instruction at position `k` becomes a labelled straight-line block that
enters with an empty value stack, updates one heap cell (or tests two), and
leaves with an empty value stack. The compiled program is

    prologue          store the input vector into cells 0, 1, …
    block 0           [LF][Space][Space] label 0, then the code for P[0]
    block 1           …
    …
    epilogue          label "end", push 0, retrieve, outnum, end

Fallthrough between blocks is just the next block's label instruction; a
jump is `jz` to the target block's label. Jump targets at or past the end of
the URM program resolve to the epilogue's label, which is how the URM's
"the counter ran off the end" convention becomes Whitespace's `end`.

Block labels are `[Tab]` followed by `k` `[Space]`s, and the epilogue's
label is a single `[Space]`, so no block label collides with it.

## What is observable

The compiled program prints the contents of URM register 0 in decimal and
halts. `decodeOutput` is decimal parsing, so the simulation theorem says
"the compiled program prints the URM's answer".

## The shape of the proof

`Langlib.Common.Reaches` carries the fuel: `Reaches E s t` says that running
the interpreter from `s` costs a fixed amount of fuel and then continues
exactly as a run from `t` would. Every lemma below is of that form, they
compose by `Reaches.trans`, and no fuel monotonicity is needed because the
accounting is exact.

The state relation is `Matches`: the value stack and call stack are empty,
the heap agrees with the registers at every address, and the program counter
is at the entry of the block for the URM's counter.
-/

namespace Langlib.Computability.URMWhitespace

open Langlib.Common
open Langlib.Whitespace
open Cslib.URM (Program Regs State Step Steps HaltsWithResult)

/-! ## Labels -/

/-- The label of the block for URM instruction `k`: `[Tab]` then `k`
`[Space]`s. -/
def lbl (k : Nat) : Label := String.ofList ('T' :: List.replicate k 'S')

/-- The epilogue's label, a single `[Space]`. No `lbl` starts with one. -/
def lend : Label := String.ofList ['S']

theorem lbl_inj {j k : Nat} (h : lbl j = lbl k) : j = k := by
  have h1 := String.ofList_injective h
  have h2 : List.replicate j 'S' = List.replicate k 'S' := (List.cons.inj h1).2
  simpa using congrArg List.length h2

theorem lbl_ne (j k : Nat) (h : j ≠ k) : lbl j ≠ lbl k := fun he => h (lbl_inj he)

theorem lbl_ne_lend (k : Nat) : lbl k ≠ lend := by
  intro h
  have h1 := String.ofList_injective h
  simp at h1

/-- Where a URM jump target lands: the block for `q` when the program has
one, otherwise the epilogue. -/
def labelAt (n q : Nat) : Label := if q < n then lbl q else lend

/-! ## The compiler -/

/-- Straight-line Whitespace code for one URM instruction. Entered with an
empty value stack, leaves it empty. `n` is the URM program's length, needed
to resolve jump targets. -/
def instrCode (n : Nat) : Cslib.URM.Instr → List Instr
  | .Z r => [.push (r : Int), .push 0, .store]
  | .S r => [.push (r : Int), .push (r : Int), .retrieve, .push 1, .add, .store]
  | .T m r => [.push (r : Int), .push (m : Int), .retrieve, .store]
  | .J m r q =>
    [.push (m : Int), .retrieve, .push (r : Int), .retrieve, .sub, .jz (labelAt n q)]

/-- The length of `instrCode`, which does not depend on `n`. -/
def instrLen : Cslib.URM.Instr → Nat
  | .Z _ => 3
  | .S _ => 6
  | .T _ _ => 4
  | .J _ _ _ => 6

theorem instrCode_length (n : Nat) (i : Cslib.URM.Instr) :
    (instrCode n i).length = instrLen i := by
  cases i <;> rfl

/-- Load the input vector into heap cells `a`, `a+1`, … -/
def prologue : Nat → List Nat → List Instr
  | _, [] => []
  | a, v :: vs => .push (a : Int) :: .push (v : Int) :: .store :: prologue (a + 1) vs

/-- The labelled blocks for a run of URM instructions starting at index `k`. -/
def blocks (n : Nat) : Nat → List Cslib.URM.Instr → List Instr
  | _, [] => []
  | k, i :: rest => (Instr.label (lbl k) :: instrCode n i) ++ blocks n (k + 1) rest

/-- Print register 0 in decimal and stop. -/
def epilogue : List Instr :=
  [Instr.label lend, .push 0, .retrieve, .outNum, .halt]

/-- The compiled program, as a list. -/
def compileList (P : Program) (inputs : List Nat) : List Instr :=
  prologue 0 inputs ++ blocks P.length 0 P ++ epilogue

/-- The compiler. Total and runnable: `#eval (compile P inputs).size` works. -/
def compile (P : Program) (inputs : List Nat) : Prog :=
  (compileList P inputs).toArray

/-! ## Sizes and positions -/

/-- The size of the code emitted for a run of URM instructions. -/
def codeSize : List Cslib.URM.Instr → Nat
  | [] => 0
  | i :: rest => instrLen i + 1 + codeSize rest

theorem blocks_length (n k : Nat) (Q : List Cslib.URM.Instr) :
    (blocks n k Q).length = codeSize Q := by
  induction Q generalizing k with
  | nil => rfl
  | cons i rest ih =>
    simp only [blocks, codeSize, List.length_append, List.length_cons, ih,
      instrCode_length]
    try omega

theorem prologue_length (a : Nat) (vs : List Nat) :
    (prologue a vs).length = 3 * vs.length := by
  induction vs generalizing a with
  | nil => rfl
  | cons v vs ih => simp only [prologue, List.length_cons, ih, List.length_cons]; omega

theorem blocks_append (n k : Nat) (Q₁ Q₂ : List Cslib.URM.Instr) :
    blocks n k (Q₁ ++ Q₂) = blocks n k Q₁ ++ blocks n (k + Q₁.length) Q₂ := by
  induction Q₁ generalizing k with
  | nil => simp [blocks]
  | cons i rest ih =>
    simp only [List.cons_append, blocks, ih, List.append_assoc, List.length_cons,
      show k + 1 + rest.length = k + (rest.length + 1) from by omega]

theorem codeSize_append (Q₁ Q₂ : List Cslib.URM.Instr) :
    codeSize (Q₁ ++ Q₂) = codeSize Q₁ + codeSize Q₂ := by
  induction Q₁ with
  | nil => simp [codeSize]
  | cons i rest ih => simp only [List.cons_append, codeSize, ih]; omega

/-- Where the prologue ends. -/
def base (inputs : List Nat) : Nat := 3 * inputs.length

/-- The position of the `label` instruction that opens block `k`; for
`k = P.length` this is the epilogue's label. -/
def blockPos (P : Program) (inputs : List Nat) (k : Nat) : Nat :=
  base inputs + codeSize (P.take k)

/-- The position just past block `k`'s label, which is where a jump to that
block lands and where the block's straight-line code begins. -/
def entry (P : Program) (inputs : List Nat) (k : Nat) : Nat :=
  blockPos P inputs k + 1

theorem entry_succ (P : Program) (inputs : List Nat) (k : Nat) (hk : k < P.length) :
    entry P inputs k + instrLen P[k] + 1 = entry P inputs (k + 1) := by
  have hsplit : P.take (k + 1) = P.take k ++ [P[k]] :=
    List.take_succ_eq_append_getElem hk
  simp only [entry, blockPos, hsplit, codeSize_append, codeSize]
  omega


/-! ## The label table

`Langlib.Whitespace.labelMap` scans the program with a `for` loop and records
the position just past the first definition of each label. The lemmas below
turn that loop into a recursive function and then read off the entry for
every label the compiler emits. -/

/-- The recursive form of `labelMap`'s loop body. -/
def labelGo : List Instr → Nat → Std.HashMap Label Nat → Std.HashMap Label Nat
  | [], _, m => m
  | i :: rest, n, m =>
    labelGo rest (n + 1) (match i with
      | .label l => if (!m.contains l) = true then m.insert l (n + 1) else m
      | _ => m)

private theorem labelGo_forIn (L : List Instr) :
    ∀ (m : Std.HashMap Label Nat) (i : Nat),
    (forIn (m := Id) L (m, i) fun instr (st : Std.HashMap Label Nat × Nat) =>
        match instr with
        | Instr.label l =>
          if (!st.fst.contains l) = true then
            pure (ForInStep.yield (st.fst.insert l (st.snd + 1), st.snd + 1))
          else pure (ForInStep.yield (st.fst, st.snd + 1))
        | _ => pure (ForInStep.yield (st.fst, st.snd + 1))).fst = labelGo L i m := by
  induction L with
  | nil => intro m i; rfl
  | cons a rest ih =>
    intro m i
    simp only [List.forIn_cons, labelGo]
    cases a
    case label l =>
      dsimp only
      by_cases hc : (!m.contains l) = true
      · rw [if_pos hc, if_pos hc]; exact ih _ _
      · rw [if_neg hc, if_neg hc]; exact ih _ _
    all_goals exact ih _ _

theorem labelMap_eq (prog : Prog) : labelMap prog = labelGo prog.toList 0 ∅ := by
  unfold labelMap
  simp only [Id.run]
  rw [← Array.forIn_toList]
  exact labelGo_forIn prog.toList ∅ 0

/-- No `label l` instruction occurs in `c`. -/
def NoLabel (l : Label) (c : List Instr) : Prop := ∀ i ∈ c, i ≠ Instr.label l

theorem labelGo_append (L₁ : List Instr) :
    ∀ (L₂ : List Instr) (n : Nat) (m : Std.HashMap Label Nat),
      labelGo (L₁ ++ L₂) n m = labelGo L₂ (n + L₁.length) (labelGo L₁ n m) := by
  induction L₁ with
  | nil => intro L₂ n m; simp [labelGo]
  | cons i rest ih =>
    intro L₂ n m
    simp only [List.cons_append, labelGo, ih, List.length_cons,
      show n + (rest.length + 1) = n + 1 + rest.length from by omega]

/-- Scanning code that never defines `l` leaves `l`'s entry alone. -/
theorem labelGo_of_noLabel (L : List Instr) (l : Label) :
    ∀ (n : Nat) (m : Std.HashMap Label Nat), NoLabel l L → (labelGo L n m)[l]? = m[l]? := by
  induction L with
  | nil => intro n m _; rfl
  | cons i rest ih =>
    intro n m h
    have hrest : NoLabel l rest := fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [labelGo]
    cases i
    case label l' =>
      have hne : ¬ (l' == l) = true := by
        intro he
        exact h (Instr.label l') (List.mem_cons_self ..) (by rw [eq_of_beq he])
      dsimp only
      by_cases hc : (!m.contains l') = true
      · rw [if_pos hc, ih _ _ hrest, Std.HashMap.getElem?_insert, if_neg hne]
      · rw [if_neg hc, ih _ _ hrest]
    all_goals exact ih _ _ hrest

/-- Once `l` has an entry, later scanning never changes it. -/
theorem labelGo_of_contains (L : List Instr) (l : Label) :
    ∀ (n : Nat) (m : Std.HashMap Label Nat), m.contains l = true →
      (labelGo L n m)[l]? = m[l]? ∧ (labelGo L n m).contains l = true := by
  induction L with
  | nil => intro n m h; exact ⟨rfl, h⟩
  | cons i rest ih =>
    intro n m h
    simp only [labelGo]
    cases i
    case label l' =>
      dsimp only
      by_cases hc : (!m.contains l') = true
      · rw [if_pos hc]
        have hne : ¬ (l' == l) = true := by
          intro he
          have : m.contains l' = true := by rw [eq_of_beq he]; exact h
          simp [this] at hc
        have hcon : (m.insert l' (n + 1)).contains l = true := by
          simp only [Std.HashMap.contains_insert, h, Bool.or_true]
        have := ih (n + 1) (m.insert l' (n + 1)) hcon
        refine ⟨?_, this.2⟩
        rw [this.1, Std.HashMap.getElem?_insert, if_neg hne]
      · rw [if_neg hc]; exact ih _ _ h
    all_goals exact ih _ _ h

/-- The entry recorded for the first definition of `l`. -/
theorem labelGo_first (pre suf : List Instr) (l : Label) (n : Nat)
    (m : Std.HashMap Label Nat) (hm : m.contains l = false) (h : NoLabel l pre) :
    (labelGo (pre ++ Instr.label l :: suf) n m)[l]? = some (n + pre.length + 1) := by
  rw [labelGo_append]
  have h1 : (labelGo pre n m)[l]? = m[l]? := labelGo_of_noLabel pre l n m h
  have h1c : (labelGo pre n m).contains l = false := by
    rw [Std.HashMap.contains_eq_isSome_getElem?, h1,
      ← Std.HashMap.contains_eq_isSome_getElem?, hm]
  simp only [labelGo]
  rw [if_pos (by simp [h1c])]
  have hcon : ((labelGo pre n m).insert l (n + pre.length + 1)).contains l = true := by
    simp
  have := labelGo_of_contains suf l (n + pre.length + 1)
    ((labelGo pre n m).insert l (n + pre.length + 1)) hcon
  rw [this.1]
  simp

/-! ## Where each instruction sits -/

theorem NoLabel.nil (l : Label) : NoLabel l [] := by intro x hx; simp at hx

theorem NoLabel.cons {l : Label} {a : Instr} {c : List Instr}
    (h : a ≠ Instr.label l) (h' : NoLabel l c) : NoLabel l (a :: c) := by
  intro x hx
  cases List.mem_cons.mp hx with
  | inl he => exact he ▸ h
  | inr he => exact h' x he

theorem NoLabel.append {l : Label} {c₁ c₂ : List Instr}
    (h₁ : NoLabel l c₁) (h₂ : NoLabel l c₂) : NoLabel l (c₁ ++ c₂) := by
  intro x hx
  cases List.mem_append.mp hx with
  | inl he => exact h₁ x he
  | inr he => exact h₂ x he

theorem noLabel_instrCode (l : Label) (n : Nat) (i : Cslib.URM.Instr) :
    NoLabel l (instrCode n i) := by
  intro x hx hc
  subst hc
  cases i <;> simp [instrCode] at hx

theorem noLabel_prologue (l : Label) (vs : List Nat) :
    ∀ a : Nat, NoLabel l (prologue a vs) := by
  induction vs with
  | nil => intro a; exact NoLabel.nil l
  | cons v vs ih =>
    intro a
    exact NoLabel.cons (by simp) (NoLabel.cons (by simp) (NoLabel.cons (by simp) (ih (a + 1))))

theorem noLabel_blocks (n : Nat) (Q : List Cslib.URM.Instr) (l : Label) :
    ∀ k : Nat, (∀ t, t < Q.length → l ≠ lbl (k + t)) → NoLabel l (blocks n k Q) := by
  induction Q with
  | nil => intro k _; exact NoLabel.nil l
  | cons i rest ih =>
    intro k h
    refine NoLabel.append (NoLabel.cons ?_ (noLabel_instrCode l n i)) (ih (k + 1) ?_)
    · intro hc
      exact h 0 (by simp) (by rw [Nat.add_zero]; exact (Instr.label.inj hc).symm)
    · intro t ht hc
      exact h (t + 1) (by simp only [List.length_cons]; omega)
        (by rw [show k + (t + 1) = k + 1 + t from by omega]; exact hc)

/-! ## Cutting the program open -/

theorem blocks_split (n : Nat) (Q : List Cslib.URM.Instr) (k : Nat) (hk : k < Q.length) :
    blocks n 0 Q = blocks n 0 (Q.take k)
      ++ Instr.label (lbl k) :: (instrCode n Q[k] ++ blocks n (k + 1) (Q.drop (k + 1))) := by
  have hlen : (Q.take k).length = k := by
    rw [List.length_take]; omega
  conv_lhs => rw [← List.take_append_drop k Q]
  rw [blocks_append, List.drop_eq_getElem_cons hk, hlen, Nat.zero_add]
  simp only [blocks, List.cons_append, List.append_assoc]

theorem compileList_split (P : Program) (inputs : List Nat) (k : Nat) (hk : k < P.length) :
    compileList P inputs =
      (prologue 0 inputs ++ blocks P.length 0 (P.take k))
        ++ Instr.label (lbl k) :: (instrCode P.length P[k]
              ++ (blocks P.length (k + 1) (P.drop (k + 1)) ++ epilogue)) := by
  simp only [compileList, blocks_split P.length P k hk, List.append_assoc, List.cons_append]

theorem compileList_split_end (P : Program) (inputs : List Nat) :
    compileList P inputs =
      (prologue 0 inputs ++ blocks P.length 0 P)
        ++ Instr.label lend :: ([Instr.push 0, Instr.retrieve, Instr.outNum, Instr.halt] ++ []) := by
  simp only [compileList, epilogue, List.append_assoc, List.cons_append, List.append_nil]

theorem prefix_length (P : Program) (inputs : List Nat) (k : Nat) :
    (prologue 0 inputs ++ blocks P.length 0 (P.take k)).length = blockPos P inputs k := by
  simp only [List.length_append, prologue_length, blocks_length, blockPos, base]

theorem prefix_length_end (P : Program) (inputs : List Nat) :
    (prologue 0 inputs ++ blocks P.length 0 P).length = blockPos P inputs P.length := by
  simp only [List.length_append, prologue_length, blocks_length, blockPos, base,
    List.take_length]

/-! ## Reading instructions out of the compiled array -/

/-- `CodeAt prog p code`: `code` occupies consecutive positions from `p`. -/
def CodeAt (prog : Prog) (p : Nat) (code : List Instr) : Prop :=
  ∀ j, j < code.length → prog[p + j]? = code[j]?

private theorem getElem?_split (pre suf : List Instr) (j : Nat) :
    (pre ++ suf).toArray[pre.length + j]? = suf[j]? := by
  simp only [List.getElem?_toArray]
  rw [List.getElem?_append_right (Nat.le_add_right _ _)]
  simp

theorem getElem?_at_split {prog : Prog} {pre : List Instr} {a : Instr} {suf : List Instr}
    (h : prog = (pre ++ a :: suf).toArray) : prog[pre.length]? = some a := by
  rw [h]
  have := getElem?_split pre (a :: suf) 0
  simpa using this

theorem codeAt_of_split {prog : Prog} {pre : List Instr} {a : Instr} {code rest : List Instr}
    (h : prog = (pre ++ a :: (code ++ rest)).toArray) :
    CodeAt prog (pre.length + 1) code := by
  intro j hj
  rw [h, show pre.length + 1 + j = pre.length + (j + 1) from by omega,
    getElem?_split pre (a :: (code ++ rest)) (j + 1)]
  simp only [List.getElem?_cons_succ]
  exact List.getElem?_append_left hj

theorem CodeAt.get {prog : Prog} {p : Nat} {code : List Instr} (h : CodeAt prog p code)
    (j : Nat) (hj : j < code.length) : prog[p + j]? = some code[j] := by
  rw [h j hj, List.getElem?_eq_getElem hj]
