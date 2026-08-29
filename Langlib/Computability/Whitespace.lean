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
open Cslib.URM (Program Regs Step Steps HaltsWithResult)

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

/-! ## The label table of the compiled program -/

theorem labels_lbl (P : Program) (inputs : List Nat) (k : Nat) (hk : k < P.length) :
    (labelMap (compile P inputs))[lbl k]? = some (entry P inputs k) := by
  rw [labelMap_eq, compile, List.toList_toArray, compileList_split P inputs k hk,
    labelGo_first _ _ _ 0 ∅ (by simp) ?nolab, prefix_length]
  case nolab =>
    refine NoLabel.append (noLabel_prologue _ _ 0) (noLabel_blocks _ _ _ 0 ?_)
    intro t ht hc
    have hle : (P.take k).length ≤ k := by rw [List.length_take]; omega
    have : t < k := by omega
    have := lbl_inj hc
    omega
  simp [entry]

theorem labels_lend (P : Program) (inputs : List Nat) :
    (labelMap (compile P inputs))[lend]? = some (entry P inputs P.length) := by
  rw [labelMap_eq, compile, List.toList_toArray, compileList_split_end P inputs,
    labelGo_first _ _ _ 0 ∅ (by simp) ?nolab, prefix_length_end]
  case nolab =>
    refine NoLabel.append (noLabel_prologue _ _ 0) (noLabel_blocks _ _ _ 0 ?_)
    intro t _ hc
    exact lbl_ne_lend (0 + t) hc.symm
  simp [entry]

theorem labels_target (P : Program) (inputs : List Nat) (q : Nat) :
    (labelMap (compile P inputs))[labelAt P.length q]? =
      some (entry P inputs (min q P.length)) := by
  unfold labelAt
  split
  · rename_i h
    rw [labels_lbl P inputs q h, Nat.min_eq_left (Nat.le_of_lt h)]
  · rename_i h
    rw [labels_lend, Nat.min_eq_right (Nat.le_of_not_lt h)]

/-! ## Single-instruction execution lemmas

Each of these says: the interpreter spends one unit of fuel and moves to a
specific state. They are the atoms the block lemmas are built from. -/

variable {prog : Prog} {labels : Std.HashMap Label Nat}

theorem reaches_push (s : Whitespace.State) (v : Int)
    (h : prog[s.pc]? = some (Instr.push v)) :
    Reaches (exec prog labels) s { s with pc := s.pc + 1, stack := v :: s.stack } :=
  Reaches.one fun f => by simp only [exec, h]

theorem reaches_label (s : Whitespace.State) (l : Label)
    (h : prog[s.pc]? = some (Instr.label l)) :
    Reaches (exec prog labels) s { s with pc := s.pc + 1 } :=
  Reaches.one fun f => by simp only [exec, h]

theorem reaches_store (s : Whitespace.State) (a v : Int) (st : List Int)
    (hst : s.stack = v :: a :: st) (ha : 0 ≤ a) (h : prog[s.pc]? = some Instr.store) :
    Reaches (exec prog labels) s
      { s with pc := s.pc + 1, stack := st, heap := s.heap.insert a v } :=
  Reaches.one fun f => by simp only [exec, h, hst]; rw [if_neg (by omega)]

theorem reaches_retrieve (s : Whitespace.State) (a : Int) (st : List Int)
    (hst : s.stack = a :: st) (ha : 0 ≤ a) (h : prog[s.pc]? = some Instr.retrieve) :
    Reaches (exec prog labels) s
      { s with pc := s.pc + 1, stack := s.heap.getD a 0 :: st } :=
  Reaches.one fun f => by simp only [exec, h, hst]; rw [if_neg (by omega)]

theorem reaches_add (s : Whitespace.State) (a b : Int) (st : List Int)
    (hst : s.stack = b :: a :: st) (h : prog[s.pc]? = some Instr.add) :
    Reaches (exec prog labels) s { s with pc := s.pc + 1, stack := (a + b) :: st } :=
  Reaches.one fun f => by simp only [exec, h, hst]

theorem reaches_sub (s : Whitespace.State) (a b : Int) (st : List Int)
    (hst : s.stack = b :: a :: st) (h : prog[s.pc]? = some Instr.sub) :
    Reaches (exec prog labels) s { s with pc := s.pc + 1, stack := (a - b) :: st } :=
  Reaches.one fun f => by simp only [exec, h, hst]

theorem reaches_jz_taken (s : Whitespace.State) (st : List Int) (l : Label) (p' : Nat)
    (hst : s.stack = 0 :: st) (hl : labels[l]? = some p')
    (h : prog[s.pc]? = some (Instr.jz l)) :
    Reaches (exec prog labels) s { s with pc := p', stack := st } :=
  Reaches.one fun f => by simp only [exec, h, hst]; simp only [hl]; simp

theorem reaches_jz_untaken (s : Whitespace.State) (st : List Int) (l : Label) (v : Int)
    (hv : v ≠ 0) (hst : s.stack = v :: st) (h : prog[s.pc]? = some (Instr.jz l)) :
    Reaches (exec prog labels) s { s with pc := s.pc + 1, stack := st } :=
  Reaches.one fun f => by
    simp only [exec, h, hst]
    rw [if_neg (by simpa using hv)]

theorem reaches_outNum (s : Whitespace.State) (n : Int) (st : List Int)
    (hst : s.stack = n :: st) (h : prog[s.pc]? = some Instr.outNum) :
    Reaches (exec prog labels) s
      { s with pc := s.pc + 1, stack := st, output := s.output ++ (toString n).toUTF8 } :=
  Reaches.one fun f => by simp only [exec, h, hst]

theorem exec_halt (s : Whitespace.State) (h : prog[s.pc]? = some Instr.halt) (f : Nat) :
    exec prog labels (f + 1) s = ({ s with pc := s.pc + 1 }, Exit.halted) := by
  simp only [exec, h]

/-! ## The state relation -/

/-- The heap holds each register's value at the register's own address. -/
def HeapMatches (heap : Std.HashMap Int Int) (regs : Regs) : Prop :=
  ∀ r : Nat, heap.getD (r : Int) 0 = (regs r : Int)

theorem heapMatches_write {heap : Std.HashMap Int Int} {regs : Regs}
    (h : HeapMatches heap regs) (r v : Nat) :
    HeapMatches (heap.insert (r : Int) (v : Int)) (regs.write r v) := by
  intro r'
  rw [Std.HashMap.getD_insert]
  by_cases hr : r' = r
  · subst hr
    simp [Cslib.URM.Regs.write]
  · rw [if_neg (by simp only [beq_iff_eq]; omega), h r', Cslib.URM.Regs.write,
      Function.update_of_ne hr]

/-! ## The simulation invariant

A URM configuration `s` corresponds to
the Whitespace state `⟨[], calls, heap, inp, out, entry P inputs (min s.pc
P.length)⟩` with `HeapMatches heap s.regs`: both stacks empty, the heap in
step with the registers, and the counter at the entry of the current block.
It is spelled out in the lemmas below rather than named, so that the states
appear as explicit records and the fuel arithmetic stays visible. -/

/-! ## Reading a whole block, terminating label included -/

theorem blocks_tail_head (P : Program) (k : Nat) (hk : k < P.length) :
    ∃ tl, blocks P.length (k + 1) (P.drop (k + 1)) ++ epilogue
      = Instr.label (labelAt P.length (k + 1)) :: tl := by
  cases hd : P.drop (k + 1) with
  | nil =>
    have hlen : P.length ≤ k + 1 := by
      have hl := congrArg List.length hd
      rw [List.length_drop] at hl
      simp only [List.length_nil] at hl
      omega
    refine ⟨[Instr.push 0, Instr.retrieve, Instr.outNum, Instr.halt], ?_⟩
    simp only [blocks, epilogue, labelAt, if_neg (by omega : ¬ (k + 1 < P.length)),
      List.nil_append]
  | cons i rest =>
    have hlen : k + 1 < P.length := by
      have hl := congrArg List.length hd
      rw [List.length_drop] at hl
      simp only [List.length_cons] at hl
      omega
    refine ⟨instrCode P.length i ++ (blocks P.length (k + 1 + 1) rest ++ epilogue), ?_⟩
    simp only [blocks, labelAt, if_pos hlen, List.cons_append, List.append_assoc]

theorem codeAt_block (P : Program) (inputs : List Nat) (k : Nat) (hk : k < P.length) :
    CodeAt (compile P inputs) (entry P inputs k)
      (instrCode P.length P[k] ++ [Instr.label (labelAt P.length (k + 1))]) := by
  cases blocks_tail_head P k hk with
  | intro tl htl =>
    have h : compile P inputs =
        ((prologue 0 inputs ++ blocks P.length 0 (P.take k)) ++ Instr.label (lbl k)
          :: ((instrCode P.length P[k] ++ [Instr.label (labelAt P.length (k + 1))])
              ++ tl)).toArray := by
      rw [compile, compileList_split P inputs k hk, htl]
      simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append]
    have hc := codeAt_of_split h
    rw [prefix_length] at hc
    exact hc

theorem codeAt_epilogue (P : Program) (inputs : List Nat) :
    CodeAt (compile P inputs) (entry P inputs P.length)
      [Instr.push 0, Instr.retrieve, Instr.outNum, Instr.halt] := by
  have h : compile P inputs =
      ((prologue 0 inputs ++ blocks P.length 0 P) ++ Instr.label lend
        :: ([Instr.push 0, Instr.retrieve, Instr.outNum, Instr.halt] ++ [])).toArray := by
    rw [compile, compileList_split_end P inputs]
  have hc := codeAt_of_split h
  rw [prefix_length_end] at hc
  exact hc

theorem codeAt_prologue (P : Program) (inputs : List Nat) :
    CodeAt (compile P inputs) 0 (prologue 0 inputs) := by
  have h : compile P inputs =
      (([] : List Instr) ++ (prologue 0 inputs ++ (blocks P.length 0 P ++ epilogue))).toArray := by
    rw [compile, compileList]
    simp only [List.nil_append, List.append_assoc]
  intro j hj
  rw [h]
  simp only [List.getElem?_toArray, List.nil_append, Nat.zero_add]
  exact List.getElem?_append_left hj

theorem getElem?_first_label (P : Program) (inputs : List Nat) (hne : 0 < P.length) :
    (compile P inputs)[base inputs]? = some (Instr.label (lbl 0)) := by
  have h : compile P inputs =
      ((prologue 0 inputs ++ blocks P.length 0 (P.take 0)) ++ Instr.label (lbl 0)
        :: (instrCode P.length P[0]
            ++ (blocks P.length (0 + 1) (P.drop (0 + 1)) ++ epilogue))).toArray := by
    rw [compile, compileList_split P inputs 0 hne]
  have := getElem?_at_split h
  rw [prefix_length] at this
  simpa [blockPos, codeSize] using this

theorem getElem?_lend_label (P : Program) (inputs : List Nat) :
    (compile P inputs)[blockPos P inputs P.length]? = some (Instr.label lend) := by
  have h : compile P inputs =
      ((prologue 0 inputs ++ blocks P.length 0 P) ++ Instr.label lend
        :: ([Instr.push 0, Instr.retrieve, Instr.outNum, Instr.halt] ++ [])).toArray := by
    rw [compile, compileList_split_end P inputs]
  have := getElem?_at_split h
  rw [prefix_length_end] at this
  exact this

/-! ## One URM instruction at a time -/

/-- The interpreter core specialised to a compiled program. -/
abbrev Ex (P : Program) (inputs : List Nat) :
    Nat → Whitespace.State → Whitespace.State × Exit :=
  exec (compile P inputs) (labelMap (compile P inputs))

theorem block_Z (P : Program) (inputs : List Nat) (k r : Nat) (hk : k < P.length)
    (hPk : P[k] = .Z r) (calls : List Nat) (heap : Std.HashMap Int Int)
    (inp : Input) (out : ByteArray) :
    Reaches (Ex P inputs)
      ⟨[], calls, heap, inp, out, entry P inputs k⟩
      ⟨[], calls, heap.insert (r : Int) 0, inp, out, entry P inputs (k + 1)⟩ := by
  have hcode := codeAt_block P inputs k hk
  rw [hPk] at hcode
  simp only [instrCode, List.cons_append, List.nil_append] at hcode
  have h0 := hcode.get 0 (by simp)
  have h1 := hcode.get 1 (by simp)
  have h2 := hcode.get 2 (by simp)
  have h3 := hcode.get 3 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1 h2 h3
  have harith : entry P inputs (k + 1) = entry P inputs k + 1 + 1 + 1 + 1 := by
    have h := entry_succ P inputs k hk
    rw [hPk] at h
    simp only [instrLen] at h
    omega
  rw [harith]
  refine Reaches.trans (reaches_push _ _ (by simpa using h0)) ?_
  refine Reaches.trans (reaches_push _ _ (by simpa using h1)) ?_
  refine Reaches.trans (reaches_store _ (r : Int) 0 [] rfl (by omega) (by simpa using h2)) ?_
  exact reaches_label _ _ (by simpa using h3)

theorem block_S (P : Program) (inputs : List Nat) (k r : Nat) (hk : k < P.length)
    (hPk : P[k] = .S r) (calls : List Nat) (heap : Std.HashMap Int Int)
    (inp : Input) (out : ByteArray) :
    Reaches (Ex P inputs)
      ⟨[], calls, heap, inp, out, entry P inputs k⟩
      ⟨[], calls, heap.insert (r : Int) (heap.getD (r : Int) 0 + 1), inp, out,
        entry P inputs (k + 1)⟩ := by
  have hcode := codeAt_block P inputs k hk
  rw [hPk] at hcode
  simp only [instrCode, List.cons_append, List.nil_append] at hcode
  have h0 := hcode.get 0 (by simp)
  have h1 := hcode.get 1 (by simp)
  have h2 := hcode.get 2 (by simp)
  have h3 := hcode.get 3 (by simp)
  have h4 := hcode.get 4 (by simp)
  have h5 := hcode.get 5 (by simp)
  have h6 := hcode.get 6 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1 h2 h3 h4 h5 h6
  have harith : entry P inputs (k + 1) = entry P inputs k + 1 + 1 + 1 + 1 + 1 + 1 + 1 := by
    have h := entry_succ P inputs k hk
    rw [hPk] at h
    simp only [instrLen] at h
    omega
  rw [harith]
  refine Reaches.trans (reaches_push _ _ (by simpa using h0)) ?_
  refine Reaches.trans (reaches_push _ _ (by simpa using h1)) ?_
  refine Reaches.trans (reaches_retrieve _ (r : Int) [(r : Int)] rfl (by omega)
    (by simpa using h2)) ?_
  refine Reaches.trans (reaches_push _ _ (by simpa using h3)) ?_
  refine Reaches.trans (reaches_add _ (heap.getD (r : Int) 0) 1 [(r : Int)] rfl
    (by simpa using h4)) ?_
  refine Reaches.trans (reaches_store _ (r : Int) (heap.getD (r : Int) 0 + 1) [] rfl
    (by omega) (by simpa using h5)) ?_
  exact reaches_label _ _ (by simpa using h6)

theorem block_T (P : Program) (inputs : List Nat) (k m r : Nat) (hk : k < P.length)
    (hPk : P[k] = .T m r) (calls : List Nat) (heap : Std.HashMap Int Int)
    (inp : Input) (out : ByteArray) :
    Reaches (Ex P inputs)
      ⟨[], calls, heap, inp, out, entry P inputs k⟩
      ⟨[], calls, heap.insert (r : Int) (heap.getD (m : Int) 0), inp, out,
        entry P inputs (k + 1)⟩ := by
  have hcode := codeAt_block P inputs k hk
  rw [hPk] at hcode
  simp only [instrCode, List.cons_append, List.nil_append] at hcode
  have h0 := hcode.get 0 (by simp)
  have h1 := hcode.get 1 (by simp)
  have h2 := hcode.get 2 (by simp)
  have h3 := hcode.get 3 (by simp)
  have h4 := hcode.get 4 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1 h2 h3 h4
  have harith : entry P inputs (k + 1) = entry P inputs k + 1 + 1 + 1 + 1 + 1 := by
    have h := entry_succ P inputs k hk
    rw [hPk] at h
    simp only [instrLen] at h
    omega
  rw [harith]
  refine Reaches.trans (reaches_push _ _ (by simpa using h0)) ?_
  refine Reaches.trans (reaches_push _ _ (by simpa using h1)) ?_
  refine Reaches.trans (reaches_retrieve _ (m : Int) [(r : Int)] rfl (by omega)
    (by simpa using h2)) ?_
  refine Reaches.trans (reaches_store _ (r : Int) (heap.getD (m : Int) 0) [] rfl
    (by omega) (by simpa using h3)) ?_
  exact reaches_label _ _ (by simpa using h4)

theorem block_J_taken (P : Program) (inputs : List Nat) (k m r q : Nat) (hk : k < P.length)
    (hPk : P[k] = .J m r q) (calls : List Nat) (heap : Std.HashMap Int Int)
    (inp : Input) (out : ByteArray)
    (heq : heap.getD (m : Int) 0 = heap.getD (r : Int) 0) :
    Reaches (Ex P inputs)
      ⟨[], calls, heap, inp, out, entry P inputs k⟩
      ⟨[], calls, heap, inp, out, entry P inputs (min q P.length)⟩ := by
  have hcode := codeAt_block P inputs k hk
  rw [hPk] at hcode
  simp only [instrCode, List.cons_append, List.nil_append] at hcode
  have h0 := hcode.get 0 (by simp)
  have h1 := hcode.get 1 (by simp)
  have h2 := hcode.get 2 (by simp)
  have h3 := hcode.get 3 (by simp)
  have h4 := hcode.get 4 (by simp)
  have h5 := hcode.get 5 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1 h2 h3 h4 h5
  refine Reaches.trans (reaches_push _ _ (by simpa using h0)) ?_
  refine Reaches.trans (reaches_retrieve _ (m : Int) [] rfl (by omega) (by simpa using h1)) ?_
  refine Reaches.trans (reaches_push _ _ (by simpa using h2)) ?_
  refine Reaches.trans (reaches_retrieve _ (r : Int) [heap.getD (m : Int) 0] rfl (by omega)
    (by simpa using h3)) ?_
  refine Reaches.trans (reaches_sub _ (heap.getD (m : Int) 0) (heap.getD (r : Int) 0) [] rfl
    (by simpa using h4)) ?_
  exact reaches_jz_taken _ [] (labelAt P.length q) (entry P inputs (min q P.length))
    (by simp [heq]) (labels_target P inputs q) (by simpa using h5)

theorem block_J_untaken (P : Program) (inputs : List Nat) (k m r q : Nat) (hk : k < P.length)
    (hPk : P[k] = .J m r q) (calls : List Nat) (heap : Std.HashMap Int Int)
    (inp : Input) (out : ByteArray)
    (hne : heap.getD (m : Int) 0 ≠ heap.getD (r : Int) 0) :
    Reaches (Ex P inputs)
      ⟨[], calls, heap, inp, out, entry P inputs k⟩
      ⟨[], calls, heap, inp, out, entry P inputs (k + 1)⟩ := by
  have hcode := codeAt_block P inputs k hk
  rw [hPk] at hcode
  simp only [instrCode, List.cons_append, List.nil_append] at hcode
  have h0 := hcode.get 0 (by simp)
  have h1 := hcode.get 1 (by simp)
  have h2 := hcode.get 2 (by simp)
  have h3 := hcode.get 3 (by simp)
  have h4 := hcode.get 4 (by simp)
  have h5 := hcode.get 5 (by simp)
  have h6 := hcode.get 6 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1 h2 h3 h4 h5 h6
  have harith : entry P inputs (k + 1) = entry P inputs k + 1 + 1 + 1 + 1 + 1 + 1 + 1 := by
    have h := entry_succ P inputs k hk
    rw [hPk] at h
    simp only [instrLen] at h
    omega
  rw [harith]
  refine Reaches.trans (reaches_push _ _ (by simpa using h0)) ?_
  refine Reaches.trans (reaches_retrieve _ (m : Int) [] rfl (by omega) (by simpa using h1)) ?_
  refine Reaches.trans (reaches_push _ _ (by simpa using h2)) ?_
  refine Reaches.trans (reaches_retrieve _ (r : Int) [heap.getD (m : Int) 0] rfl (by omega)
    (by simpa using h3)) ?_
  refine Reaches.trans (reaches_sub _ (heap.getD (m : Int) 0) (heap.getD (r : Int) 0) [] rfl
    (by simpa using h4)) ?_
  refine Reaches.trans (reaches_jz_untaken _ [] (labelAt P.length q)
    (heap.getD (m : Int) 0 - heap.getD (r : Int) 0) (by omega) rfl (by simpa using h5)) ?_
  exact reaches_label _ _ (by simpa using h6)

/-! ## Reading the answer back

The compiled program prints register 0 with Whitespace's `outnum`, so the
observable output is the decimal rendering of a natural number. These
definitions are the decoder, and `decodeOutput_encode` is the round-trip
lemma that makes the simulation theorem say what it should. -/

/-- The value of a decimal digit. -/
def digitVal (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat) else none

/-- Horner's rule over a list of decimal digits. -/
def foldDigits (cs : List Char) : Option Nat :=
  cs.foldl (fun acc c => acc.bind fun n => (digitVal c).map fun d => n * 10 + d) (some 0)

/-- Decimal parsing of a character list; `none` on an empty or non-numeric
list. -/
def decodeDecimal (cs : List Char) : Option Nat :=
  if cs.isEmpty then none else foldDigits cs

/-- The decoder of the simulation theorem: read the output bytes as a
decimal natural number. -/
def decodeOutput (b : ByteArray) : Option Nat :=
  match String.fromUTF8? b with
  | none => none
  | some s => decodeDecimal s.toList

theorem foldDigits_append_singleton (cs : List Char) (c : Char) :
    foldDigits (cs ++ [c]) =
      (foldDigits cs).bind fun n => (digitVal c).map fun d => n * 10 + d := by
  simp only [foldDigits, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem digitVal_digitChar {d : Nat} (h : d < 10) : digitVal (Nat.digitChar d) = some d := by
  simp only [digitVal, Nat.isDigit_digitChar, decide_eq_true_eq, if_pos h,
    Option.some.injEq]
  have : ('0' : Char).toNat = 48 := by decide
  rw [this, Nat.toNat_digitChar_sub_48_of_lt_ten h]

theorem foldDigits_toDigits (n : Nat) : foldDigits (Nat.toDigits 10 n) = some n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [Nat.toDigits_eq_if (by omega)]
    split
    · rename_i hlt
      simp only [foldDigits, List.foldl_cons, List.foldl_nil, Option.bind_some,
        digitVal_digitChar hlt, Option.map_some, Nat.zero_mul, Nat.zero_add]
    · rename_i hge
      have hn : 10 ≤ n := by omega
      have hdiv : n / 10 < n := Nat.div_lt_self (by omega) (by omega)
      rw [foldDigits_append_singleton, ih (n / 10) hdiv,
        digitVal_digitChar (Nat.mod_lt n (by omega))]
      simp only [Option.bind_some, Option.map_some, Option.some.injEq]
      omega

theorem decodeDecimal_toDigits (n : Nat) : decodeDecimal (Nat.toDigits 10 n) = some n := by
  simp only [decodeDecimal, List.isEmpty_iff, Nat.toDigits_ne_nil,
    foldDigits_toDigits, if_false]

theorem fromUTF8?_toUTF8 (s : String) : String.fromUTF8? s.toUTF8 = some s := by
  simp only [String.toUTF8_eq_toByteArray, String.fromUTF8?, dif_pos s.isValidUTF8,
    Option.some.injEq, ← String.toByteArray_inj]
  simp [String.fromUTF8]

/-- The decoder inverts what the compiled program prints. -/
theorem decodeOutput_encode (n : Nat) :
    decodeOutput ((toString ((n : Nat) : Int)).toUTF8) = some n := by
  have hstr : toString ((n : Nat) : Int) = Nat.repr n := by simp [Int.repr_eq_if]
  simp only [decodeOutput, fromUTF8?_toUTF8, hstr]
  rw [Nat.toList_repr, decodeDecimal_toDigits]

/-! ## The prologue -/

/-- The register state after the prologue has stored `vs` from address `a`. -/
def loadFrom (a : Nat) : List Nat → Regs → Regs
  | [], regs => regs
  | v :: vs, regs => loadFrom (a + 1) vs (regs.write a v)

theorem loadFrom_apply (vs : List Nat) :
    ∀ (a : Nat) (regs : Regs) (r : Nat),
      loadFrom a vs regs r = if r < a then regs r else vs.getD (r - a) (regs r) := by
  induction vs with
  | nil => intro a regs r; simp [loadFrom]
  | cons v vs ih =>
    intro a regs r
    rw [loadFrom, ih]
    by_cases h1 : r < a
    · rw [if_pos (by omega), if_pos h1, Cslib.URM.Regs.write,
        Function.update_of_ne (by omega : r ≠ a)]
    · by_cases h2 : r = a
      · subst h2
        rw [if_pos (by omega), if_neg h1]
        simp [Cslib.URM.Regs.write]
      · rw [if_neg (by omega), if_neg h1, Cslib.URM.Regs.write,
          Function.update_of_ne (by omega : r ≠ a),
          show r - a = (r - (a + 1)) + 1 from by omega]
        simp

theorem loadFrom_zero (inputs : List Nat) :
    loadFrom 0 inputs (fun _ => 0) = Cslib.URM.Regs.ofInputs inputs := by
  funext r
  rw [loadFrom_apply]
  simp [Cslib.URM.Regs.ofInputs]

theorem reaches_prologue (P : Program) (inputs : List Nat) (vs : List Nat) :
    ∀ (a p : Nat) (calls : List Nat) (heap : Std.HashMap Int Int) (inp : Input)
      (out : ByteArray) (regs : Regs),
      CodeAt (compile P inputs) p (prologue a vs) → HeapMatches heap regs →
      ∃ heap', Reaches (Ex P inputs)
          ⟨[], calls, heap, inp, out, p⟩
          ⟨[], calls, heap', inp, out, p + 3 * vs.length⟩
        ∧ HeapMatches heap' (loadFrom a vs regs) := by
  induction vs with
  | nil =>
    intro a p calls heap inp out regs _ hh
    refine ⟨heap, ?_, hh⟩
    simp only [List.length_nil, Nat.mul_zero, Nat.add_zero]
    exact Reaches.refl _ _
  | cons v vs ih =>
    intro a p calls heap inp out regs hcode hh
    have h0 := hcode.get 0 (by simp [prologue])
    have h1 := hcode.get 1 (by simp [prologue])
    have h2 := hcode.get 2 (by simp [prologue])
    simp only [prologue, List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1 h2
    have hcode' : CodeAt (compile P inputs) (p + 3) (prologue (a + 1) vs) := by
      intro j hj
      have hlen : (prologue (a + 1) vs).length = 3 * vs.length := prologue_length _ _
      have := hcode (j + 3) (by
        rw [prologue_length]
        simp only [List.length_cons]
        rw [hlen] at hj
        omega)
      rw [show p + (j + 3) = p + 3 + j from by omega] at this
      rw [this]
      simp [prologue]
    cases ih (a + 1) (p + 3) calls (heap.insert (a : Int) (v : Int)) inp out
        (regs.write a v) hcode' (heapMatches_write hh a v) with
    | intro heap' hres =>
      refine ⟨heap', ?_, hres.2⟩
      have chain : Reaches (Ex P inputs) ⟨[], calls, heap, inp, out, p⟩
          ⟨[], calls, heap.insert (a : Int) (v : Int), inp, out, p + 3⟩ := by
        rw [show p + 3 = p + 1 + 1 + 1 from by omega]
        refine Reaches.trans (reaches_push _ _ (by simpa using h0)) ?_
        refine Reaches.trans (reaches_push _ _ (by simpa using h1)) ?_
        exact reaches_store _ (a : Int) (v : Int) [] rfl (by omega) (by simpa using h2)
      rw [show p + 3 * (v :: vs).length = p + 3 + 3 * vs.length from by
        simp only [List.length_cons]; omega]
      exact Reaches.trans chain hres.1

/-! ## The epilogue -/

theorem exec_epilogue (P : Program) (inputs : List Nat) (calls : List Nat)
    (heap : Std.HashMap Int Int) (inp : Input) (out : ByteArray) :
    ∃ m, Ex P inputs m ⟨[], calls, heap, inp, out, entry P inputs P.length⟩
      = (⟨[], calls, heap, inp, out ++ (toString (heap.getD (0 : Int) 0)).toUTF8,
          entry P inputs P.length + 1 + 1 + 1 + 1⟩, Exit.halted) := by
  have hcode := codeAt_epilogue P inputs
  have h0 := hcode.get 0 (by simp)
  have h1 := hcode.get 1 (by simp)
  have h2 := hcode.get 2 (by simp)
  have h3 := hcode.get 3 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1 h2 h3
  have chain : Reaches (Ex P inputs)
      ⟨[], calls, heap, inp, out, entry P inputs P.length⟩
      ⟨[], calls, heap, inp, out ++ (toString (heap.getD (0 : Int) 0)).toUTF8,
        entry P inputs P.length + 1 + 1 + 1⟩ := by
    refine Reaches.trans (reaches_push _ _ (by simpa using h0)) ?_
    refine Reaches.trans (reaches_retrieve _ (0 : Int) [] rfl (by omega)
      (by simpa using h1)) ?_
    exact reaches_outNum _ (heap.getD (0 : Int) 0) [] rfl (by simpa using h2)
  cases chain with
  | intro c hc =>
    refine ⟨c + 1, ?_⟩
    rw [hc 1]
    exact exec_halt _ (by simpa using h3) 0

/-! ## The simulation -/

private theorem lt_len {P : Program} {k : Nat} {i : Cslib.URM.Instr} (h : P[k]? = some i) :
    k < P.length := by
  cases Nat.lt_or_ge k P.length with
  | inl hlt => exact hlt
  | inr hge => rw [List.getElem?_eq_none hge] at h; exact absurd h (by simp)

private theorem getElem_of_getElem? {P : Program} {k : Nat} {i : Cslib.URM.Instr}
    (h : P[k]? = some i) : P[k]'(lt_len h) = i := by
  rw [List.getElem?_eq_getElem (lt_len h)] at h
  exact Option.some.inj h

/-- One URM step becomes one labelled block. -/
theorem step_sim (P : Program) (inputs : List Nat) {s s' : Cslib.URM.State}
    (hstep : Step P s s') (calls : List Nat) (heap : Std.HashMap Int Int)
    (inp : Input) (out : ByteArray) (hh : HeapMatches heap s.regs) :
    ∃ heap', Reaches (Ex P inputs)
        ⟨[], calls, heap, inp, out, entry P inputs (min s.pc P.length)⟩
        ⟨[], calls, heap', inp, out, entry P inputs (min s'.pc P.length)⟩
      ∧ HeapMatches heap' s'.regs := by
  cases hstep
  case zero n hi =>
    have hk : s.pc < P.length := lt_len hi
    rw [Nat.min_eq_left (Nat.le_of_lt hk), Nat.min_eq_left (show s.pc + 1 ≤ P.length by omega)]
    refine ⟨heap.insert (n : Int) 0,
      block_Z P inputs s.pc n hk (getElem_of_getElem? hi) calls heap inp out, ?_⟩
    simpa using heapMatches_write hh n 0
  case succ n hi =>
    have hk : s.pc < P.length := lt_len hi
    rw [Nat.min_eq_left (Nat.le_of_lt hk), Nat.min_eq_left (show s.pc + 1 ≤ P.length by omega)]
    refine ⟨heap.insert (n : Int) (heap.getD (n : Int) 0 + 1),
      block_S P inputs s.pc n hk (getElem_of_getElem? hi) calls heap inp out, ?_⟩
    have hval : heap.getD (n : Int) 0 + 1 = ((s.regs.read n + 1 : Nat) : Int) := by
      rw [hh n]; simp [Cslib.URM.Regs.read]
    rw [hval]
    exact heapMatches_write hh n (s.regs.read n + 1)
  case transfer m n hi =>
    have hk : s.pc < P.length := lt_len hi
    rw [Nat.min_eq_left (Nat.le_of_lt hk), Nat.min_eq_left (show s.pc + 1 ≤ P.length by omega)]
    refine ⟨heap.insert (n : Int) (heap.getD (m : Int) 0),
      block_T P inputs s.pc m n hk (getElem_of_getElem? hi) calls heap inp out, ?_⟩
    rw [show heap.getD (m : Int) 0 = ((s.regs.read m : Nat) : Int) from hh m]
    exact heapMatches_write hh n (s.regs.read m)
  case jump_eq m n q hi heq =>
    have hk : s.pc < P.length := lt_len hi
    rw [Nat.min_eq_left (Nat.le_of_lt hk)]
    refine ⟨heap, block_J_taken P inputs s.pc m n q hk (getElem_of_getElem? hi)
      calls heap inp out ?_, hh⟩
    rw [hh m, hh n]
    exact congrArg _ heq
  case jump_ne m n q hi hne =>
    have hk : s.pc < P.length := lt_len hi
    rw [Nat.min_eq_left (Nat.le_of_lt hk), Nat.min_eq_left (show s.pc + 1 ≤ P.length by omega)]
    refine ⟨heap, block_J_untaken P inputs s.pc m n q hk (getElem_of_getElem? hi)
      calls heap inp out ?_, hh⟩
    rw [hh m, hh n]
    intro hc
    exact hne (by simp only [Cslib.URM.Regs.read]; exact_mod_cast hc)

/-- A whole URM run becomes a whole run of the compiled program. -/
theorem steps_sim (P : Program) (inputs : List Nat) {s₀ s : Cslib.URM.State}
    (hsteps : Steps P s₀ s) (calls : List Nat) (heap : Std.HashMap Int Int)
    (inp : Input) (out : ByteArray) (hh : HeapMatches heap s₀.regs) :
    ∃ heap', Reaches (Ex P inputs)
        ⟨[], calls, heap, inp, out, entry P inputs (min s₀.pc P.length)⟩
        ⟨[], calls, heap', inp, out, entry P inputs (min s.pc P.length)⟩
      ∧ HeapMatches heap' s.regs := by
  induction hsteps with
  | refl => exact ⟨heap, Reaches.refl _ _, hh⟩
  | tail _ hlast ih =>
    cases ih with
    | intro h₁ hr₁ =>
      cases step_sim P inputs hlast calls h₁ inp out hr₁.2 with
      | intro h₂ hr₂ => exact ⟨h₂, Reaches.trans hr₁.1 hr₂.1, hr₂.2⟩

theorem getElem?_block0_label (P : Program) (inputs : List Nat) :
    (compile P inputs)[blockPos P inputs 0]? = some (Instr.label (labelAt P.length 0)) := by
  by_cases h : 0 < P.length
  · rw [labelAt, if_pos h]
    have hb := getElem?_first_label P inputs h
    simpa [blockPos, codeSize] using hb
  · have hz : P.length = 0 := by omega
    rw [labelAt, if_neg (by omega)]
    have hb := getElem?_lend_label P inputs
    rw [hz] at hb
    exact hb

/-! ## The end-to-end theorem -/

/-- **The simulation.** Whenever the URM `P` halts on `inputs` with `result`
in register 0, the compiled Whitespace program halts, for some fuel bound,
having printed `result` in decimal. The input stream is irrelevant: the
compiled program never reads it. -/
theorem simulation (P : Program) (inputs : List Nat) (result : Nat)
    (h : HaltsWithResult P inputs result) (input : Input) :
    ∃ m, (evalProg (compile P inputs) input m).exit = Exit.halted ∧
         decodeOutput (evalProg (compile P inputs) input m).output = some result := by
  cases h with
  | intro s hs =>
    have hinit : HeapMatches (∅ : Std.HashMap Int Int) (fun _ => 0) := by
      intro r; simp
    cases reaches_prologue P inputs inputs 0 0 [] ∅ input ByteArray.empty (fun _ => 0)
        (codeAt_prologue P inputs) hinit with
    | intro heap0 hpro =>
      have hheap0 : HeapMatches heap0 (Cslib.URM.Regs.ofInputs inputs) := by
        rw [← loadFrom_zero inputs]; exact hpro.2
      have hlab : Reaches (Ex P inputs)
          ⟨[], [], heap0, input, ByteArray.empty, 0 + 3 * inputs.length⟩
          ⟨[], [], heap0, input, ByteArray.empty, entry P inputs 0⟩ := by
        rw [show (0 : Nat) + 3 * inputs.length = blockPos P inputs 0 by
          simp [blockPos, base, codeSize]]
        exact reaches_label _ _ (getElem?_block0_label P inputs)
      cases steps_sim P inputs hs.1 [] heap0 input ByteArray.empty hheap0 with
      | intro heapF hsim =>
        simp only [Cslib.URM.State.init, Nat.zero_min,
          Nat.min_eq_right hs.2.1] at hsim
        cases exec_epilogue P inputs [] heapF input ByteArray.empty with
        | intro m₀ hep =>
          have htot : Reaches (Ex P inputs)
              ⟨[], [], ∅, input, ByteArray.empty, 0⟩
              ⟨[], [], heapF, input, ByteArray.empty, entry P inputs P.length⟩ :=
            Reaches.trans hpro.1 (Reaches.trans hlab hsim.1)
          cases htot with
          | intro c hc =>
            refine ⟨c + m₀, ?_⟩
            have hzero : heapF.getD (0 : Int) 0 = ((s.regs 0 : Nat) : Int) := by
              simpa using hsim.2 0
            simp only [evalProg]
            rw [show ({ input := input } : Whitespace.State)
                  = ⟨[], [], ∅, input, ByteArray.empty, 0⟩ from rfl,
              show exec (compile P inputs) (labelMap (compile P inputs)) (c + m₀)
                  = Ex P inputs (c + m₀) from rfl,
              hc m₀, hep]
            refine ⟨rfl, ?_⟩
            simp only [ByteArray.empty_append, hzero]
            rw [decodeOutput_encode (s.regs 0)]
            exact congrArg some hs.2.2

end Langlib.Computability.URMWhitespace

namespace Langlib.Computability

open Langlib.Common

/-- The tag type naming Whitespace for the `Esolang` class. -/
inductive WhitespaceLang : Type

instance : Esolang WhitespaceLang where
  Prog := Langlib.Whitespace.Prog
  parse := Langlib.Whitespace.parse
  run := Langlib.Whitespace.evalProg

/-- **Whitespace is Turing complete.**

The witness is the compiler `URMWhitespace.compile`, which turns a URM
program and its input vector into a Whitespace program, and the simulation
`URMWhitespace.simulation`. The compiled program ignores its input stream
and prints the URM's answer, the contents of register 0, in decimal.

Since the unlimited register machine computes every partial computable
function (Shepherdson and Sturgis 1963; Cutland, *Computability*, chapter
3), so does Whitespace. -/
def whitespaceComplete : TuringComplete WhitespaceLang where
  compile := URMWhitespace.compile
  encodeInput := fun _ => Input.ofString ""
  decodeOutput := URMWhitespace.decodeOutput
  simulates := fun P inputs result h =>
    URMWhitespace.simulation P inputs result h (Input.ofString "")

end Langlib.Computability
