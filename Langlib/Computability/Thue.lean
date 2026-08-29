import Langlib.Computability.Brainfuck
import Langlib.Languages.Thue.Semantics

/-!
# Thue is Turing complete: a verified URM-to-Thue generator

The compiler reuses the structured counter machine proved correct in
`Langlib.Computability.Brainfuck`.  Its counters are rendered as finite unary
runs separated by `d`.  A self-delimiting control token contains the current
counter-code continuation.  Rewrite phases move that token to the selected
counter, perform one local operation, and move it back to the left boundary.

Every generated left-hand side contains the unique character `@`, and that is
what makes a nondeterministic rewriting system behave like a machine: the
marker is the program counter.  The file proves prefix-free phase encoding,
calculates token occurrences and `Thue.applyAt`, and shows that any rule
selected by `Thue.firstMatch` on a represented state belongs to that state's
active phase.  Because a phase and the one adjacent cell determine the rule,
`Thue.step` is a function on represented states even though `Thue` itself is
not deterministic.

On top of that, `reaches_exec` lifts a whole big-step counter-machine
derivation (`URMBrainfuck.Ev`) to a run of the generated rules, `reaches_finish`
dispatches the counter the macro leaves behind back to a source control
marker, and `reaches_steps` composes those over a halting URM run.
`simulation` then reads register zero out of the halted final state, and
`thueComplete : TuringComplete ThueLang` is the witness.

The claim covers halting runs only, as the shared `TuringComplete` interface
does everywhere; see `docs/computability-thue.md`.
-/

namespace Langlib.Computability.URMThue

open Langlib.Common
open Langlib.Thue
open Langlib.Computability.URMBrainfuck

/-! ## Self-delimiting control encodings -/

/-- Unary natural-number encoding used inside control tokens. -/
def encNat (n : Nat) : List Char := List.replicate n 'n' ++ [';']

theorem encNat_injective : Function.Injective encNat := by
  intro m n h
  have hc := congrArg (List.count 'n') h
  simpa [encNat] using hc

/-- A unary natural is self-delimiting, so it can be cancelled even when
different suffixes follow the two encodings. -/
theorem encNat_append_injective {m n : Nat} {xs ys : List Char}
    (h : encNat m ++ xs = encNat n ++ ys) : m = n ∧ xs = ys := by
  induction m generalizing n with
  | zero =>
      cases n with
      | zero => simpa [encNat] using h
      | succ n => simp [encNat, List.replicate_succ] at h
  | succ m ih =>
      cases n with
      | zero => simp [encNat, List.replicate_succ] at h
      | succ n =>
          simp only [encNat, List.replicate_succ, List.cons_append, List.cons.injEq,
            true_and] at h
          obtain ⟨hmn, hxy⟩ := ih (n := n) h
          exact ⟨by omega, hxy⟩

@[simp] theorem marker_not_mem_encNat (n : Nat) : '@' ∉ encNat n := by
  simp [encNat]

mutual
  /-- Structural encoding of one counter-machine command. -/
  def encCmd : Cmd → List Char
    | .inc r => 'i' :: encNat r
    | .dec r => 'j' :: encNat r
    | .emit => ['e']
    | .loop r body => 'l' :: encNat r ++ '(' :: encCode body ++ [')']

  /-- Structural encoding of a counter-machine continuation. -/
  def encCode : Code → List Char
    | [] => ['z']
    | c :: cs => 'c' :: encCmd c ++ encCode cs
end

mutual
  /-- A command encoding is prefix-free.  The theorem is mutually recursive
  with `encCode_append_injective` because a loop contains a nested code list. -/
  theorem encCmd_append_injective : ∀ (c d : Cmd) (xs ys : List Char),
      encCmd c ++ xs = encCmd d ++ ys → c = d ∧ xs = ys
    | .inc r, .inc s, xs, ys, h => by
        simp only [encCmd, List.cons_append, List.cons.injEq, true_and] at h
        obtain ⟨hrs, hxy⟩ := encNat_append_injective h
        exact ⟨by simp [hrs], hxy⟩
    | .inc _, .dec _, _, _, h => by simp [encCmd] at h
    | .inc _, .emit, _, _, h => by simp [encCmd] at h
    | .inc _, .loop _ _, _, _, h => by simp [encCmd] at h
    | .dec _, .inc _, _, _, h => by simp [encCmd] at h
    | .dec r, .dec s, xs, ys, h => by
        simp only [encCmd, List.cons_append, List.cons.injEq, true_and] at h
        obtain ⟨hrs, hxy⟩ := encNat_append_injective h
        exact ⟨by simp [hrs], hxy⟩
    | .dec _, .emit, _, _, h => by simp [encCmd] at h
    | .dec _, .loop _ _, _, _, h => by simp [encCmd] at h
    | .emit, .inc _, _, _, h => by simp [encCmd] at h
    | .emit, .dec _, _, _, h => by simp [encCmd] at h
    | .emit, .emit, xs, ys, h => by
        have hxy : xs = ys := by simpa [encCmd] using h
        exact ⟨rfl, hxy⟩
    | .emit, .loop _ _, _, _, h => by simp [encCmd] at h
    | .loop _ _, .inc _, _, _, h => by simp [encCmd] at h
    | .loop _ _, .dec _, _, _, h => by simp [encCmd] at h
    | .loop _ _, .emit, _, _, h => by simp [encCmd] at h
    | .loop r body, .loop s body', xs, ys, h => by
        simp only [encCmd, List.cons_append, List.cons.injEq, true_and] at h
        obtain ⟨hrs, hrest⟩ := encNat_append_injective
          (m := r) (n := s)
          (xs := '(' :: (encCode body ++ [')'] ++ xs))
          (ys := '(' :: (encCode body' ++ [')'] ++ ys))
          (by simpa [List.append_assoc] using h)
        simp only [List.cons.injEq] at hrest
        have hbody : encCode body ++ (')' :: xs) = encCode body' ++ (')' :: ys) := by
          simpa [List.append_assoc] using hrest
        obtain ⟨hb, hxy⟩ := encCode_append_injective body body' _ _ hbody
        exact ⟨by simp [hrs, hb], by simpa using hxy⟩
  termination_by c d xs ys _h => (encCmd c).length
  decreasing_by
    all_goals simp [encCmd]
    all_goals omega

  /-- A counter-code encoding is prefix-free, including nested loop bodies. -/
  theorem encCode_append_injective : ∀ (cs ds : Code) (xs ys : List Char),
      encCode cs ++ xs = encCode ds ++ ys → cs = ds ∧ xs = ys
    | [], [], xs, ys, h => by
        have hxy : xs = ys := by simpa [encCode] using h
        exact ⟨rfl, hxy⟩
    | [], _ :: _, _, _, h => by simp [encCode] at h
    | _ :: _, [], _, _, h => by simp [encCode] at h
    | c :: cs, d :: ds, xs, ys, h => by
        simp only [encCode, List.cons_append, List.cons.injEq, true_and] at h
        have hc : encCmd c ++ (encCode cs ++ xs) =
            encCmd d ++ (encCode ds ++ ys) := by simpa [List.append_assoc] using h
        obtain ⟨hcd, hrest⟩ := encCmd_append_injective c d _ _ hc
        obtain ⟨hcs, hxy⟩ := encCode_append_injective cs ds xs ys hrest
        exact ⟨by simp [hcd, hcs], hxy⟩
  termination_by cs ds xs ys _h => (encCode cs).length
  decreasing_by
    all_goals simp [encCode]
    all_goals omega
end

theorem encCode_injective : Function.Injective encCode := by
  intro cs ds h
  exact (encCode_append_injective cs ds [] [] (by simpa using h)).1

mutual
  @[simp] theorem boundary_not_mem_encCmd (c : Cmd) : 'b' ∉ encCmd c := by
    cases c with
    | inc r => simp [encCmd, encNat]
    | dec r => simp [encCmd, encNat]
    | emit => simp [encCmd]
    | loop r body => simp [encCmd, encNat, boundary_not_mem_encCode body]

  @[simp] theorem boundary_not_mem_encCode (code : Code) : 'b' ∉ encCode code := by
    cases code with
    | nil => simp [encCode]
    | cons c cs => simp [encCode, boundary_not_mem_encCmd c, boundary_not_mem_encCode cs]
end

mutual
  @[simp] theorem marker_not_mem_encCmd (c : Cmd) : '@' ∉ encCmd c := by
    cases c with
    | inc r => simp [encCmd]
    | dec r => simp [encCmd]
    | emit => simp [encCmd]
    | loop r body => simp [encCmd, marker_not_mem_encCode body]

  @[simp] theorem marker_not_mem_encCode (code : Code) : '@' ∉ encCode code := by
    cases code with
    | nil => simp [encCode]
    | cons c cs => simp [encCode, marker_not_mem_encCmd c, marker_not_mem_encCode cs]
end

/-- A dispatch result: the unary value found in the counter-machine program
counter and the corresponding source URM program counter. -/
structure Outcome where
  count : Nat
  pc : Nat
deriving Repr

/-- What happens after a counter macro finishes.  The macro leaves the next
URM program counter plus one in counter `target`; dispatch consumes that
counter and installs the matching source control marker. -/
structure Done where
  target : Nat
  outcomes : List Outcome
deriving Repr

/-- A control or micro-step phase of the generated rewriter. -/
inductive Phase where
  | control (pc : Nat)
  | exec (done : Done) (code : Code)
  | scanInc (done : Done) (next : Code) (target current : Nat)
  | scanDec (done : Done) (next : Code) (target current : Nat)
  | scanZero (done : Done) (zero nonzero : Code) (target current : Nat)
  | back (done : Done) (next : Code)
  | seekPC (done : Done) (current : Nat)
  | countPC (done : Done) (count : Nat)
  | backPC (pc : Nat)
deriving Repr

def encOutcome (o : Outcome) : List Char := encNat o.count ++ encNat o.pc

def encDone (d : Done) : List Char :=
  encNat d.target ++ '[' :: d.outcomes.flatMap encOutcome ++ [']']

/-- One dispatch outcome is self-delimiting. -/
theorem encOutcome_append_injective (o p : Outcome) (xs ys : List Char)
    (h : encOutcome o ++ xs = encOutcome p ++ ys) : o = p ∧ xs = ys := by
  obtain ⟨oc, op⟩ := o
  obtain ⟨pc, pp⟩ := p
  simp only [encOutcome] at h
  obtain ⟨hc, hrest⟩ := encNat_append_injective
    (m := oc) (n := pc) (xs := encNat op ++ xs) (ys := encNat pp ++ ys)
    (by simpa [List.append_assoc] using h)
  obtain ⟨hp, hxy⟩ := encNat_append_injective hrest
  exact ⟨by simp [hc, hp], hxy⟩

/-- A list of dispatch outcomes is self-delimiting at its closing bracket. -/
theorem encOutcomes_bracket_injective : ∀ (os ps : List Outcome) (xs ys : List Char),
    os.flatMap encOutcome ++ ']' :: xs = ps.flatMap encOutcome ++ ']' :: ys →
      os = ps ∧ xs = ys
  | [], [], xs, ys, h => ⟨rfl, by simpa using h⟩
  | [], ⟨pc, pp⟩ :: ps, xs, ys, h => by
      cases pc <;> simp [encOutcome, encNat, List.replicate_succ] at h
  | ⟨oc, op⟩ :: os, [], xs, ys, h => by
      cases oc <;> simp [encOutcome, encNat, List.replicate_succ] at h
  | o :: os, p :: ps, xs, ys, h => by
      simp only [List.flatMap_cons] at h
      have ho : encOutcome o ++ (os.flatMap encOutcome ++ ']' :: xs) =
          encOutcome p ++ (ps.flatMap encOutcome ++ ']' :: ys) := by
        simpa [List.append_assoc] using h
      obtain ⟨hop, hrest⟩ := encOutcome_append_injective o p _ _ ho
      obtain ⟨hops, hxy⟩ := encOutcomes_bracket_injective os ps xs ys hrest
      exact ⟨by simp [hop, hops], hxy⟩

/-- A completed-macro descriptor is self-delimiting. -/
theorem encDone_append_injective (d e : Done) (xs ys : List Char)
    (h : encDone d ++ xs = encDone e ++ ys) : d = e ∧ xs = ys := by
  obtain ⟨dt, dos⟩ := d
  obtain ⟨et, eos⟩ := e
  simp only [encDone] at h
  obtain ⟨ht, hrest⟩ := encNat_append_injective
    (m := dt) (n := et)
    (xs := '[' :: (dos.flatMap encOutcome ++ [']'] ++ xs))
    (ys := '[' :: (eos.flatMap encOutcome ++ [']'] ++ ys))
    (by simpa [List.append_assoc] using h)
  simp only [List.cons.injEq] at hrest
  have hos : dos.flatMap encOutcome ++ (']' :: xs) =
      eos.flatMap encOutcome ++ (']' :: ys) := by
    simpa [List.append_assoc] using hrest
  obtain ⟨houts, hxy⟩ := encOutcomes_bracket_injective dos eos _ _ hos
  exact ⟨by simp [ht, houts], hxy⟩

@[simp] theorem marker_not_mem_encOutcome (o : Outcome) : '@' ∉ encOutcome o := by
  simp [encOutcome]

@[simp] theorem marker_not_mem_encDone (d : Done) : '@' ∉ encDone d := by
  simp [encDone, List.mem_flatMap]

@[simp] theorem boundary_not_mem_encOutcome (o : Outcome) : 'b' ∉ encOutcome o := by
  simp [encOutcome, encNat]

@[simp] theorem boundary_not_mem_encDone (d : Done) : 'b' ∉ encDone d := by
  simp [encDone, encNat, List.mem_flatMap]

/-- Payload of a phase token.  The leading constructor character makes the
five forms disjoint; every variable-length field is self-delimiting. -/
def encPhase : Phase → List Char
  | .control pc => 'C' :: encNat pc
  | .exec done code => 'E' :: encDone done ++ '|' :: encCode code
  | .scanInc done next target current =>
      'I' :: encDone done ++ '|' :: encCode next ++ '|' :: encNat target ++ encNat current
  | .scanDec done next target current =>
      'D' :: encDone done ++ '|' :: encCode next ++ '|' :: encNat target ++ encNat current
  | .scanZero done zero nonzero target current =>
      'Z' :: encDone done ++ '|' :: encCode zero ++ '|' :: encCode nonzero ++ '|' ::
        encNat target ++ encNat current
  | .back done next => 'B' :: encDone done ++ '|' :: encCode next
  | .seekPC done current => 'S' :: encDone done ++ '|' :: encNat current
  | .countPC done count => 'N' :: encDone done ++ '|' :: encNat count
  | .backPC pc => 'P' :: encNat pc

private def phaseTag : Phase → Char
  | .control _ => 'C'
  | .exec _ _ => 'E'
  | .scanInc _ _ _ _ => 'I'
  | .scanDec _ _ _ _ => 'D'
  | .scanZero _ _ _ _ _ => 'Z'
  | .back _ _ => 'B'
  | .seekPC _ _ => 'S'
  | .countPC _ _ => 'N'
  | .backPC _ => 'P'

/-- Phase payloads are prefix-free.  This is the central separation theorem
for rule families, since every generated left-hand side contains one whole
phase token. -/
theorem encPhase_append_injective (p q : Phase) (xs ys : List Char)
    (h : encPhase p ++ xs = encPhase q ++ ys) : p = q ∧ xs = ys := by
  have htag : phaseTag p = phaseTag q := by
    cases p <;> cases q <;> simp [encPhase, phaseTag] at h ⊢
  cases p <;> cases q <;> simp [phaseTag] at htag
  all_goals simp only [encPhase, List.cons_append, List.cons.injEq, true_and] at h
  · obtain ⟨hp, hxy⟩ := encNat_append_injective h
    exact ⟨by simp [hp], hxy⟩
  · obtain ⟨hd, hrest⟩ := encDone_append_injective _ _ _ _
      (by simpa [List.append_assoc] using h)
    simp only [List.cons.injEq, true_and] at hrest
    obtain ⟨hc, hxy⟩ := encCode_append_injective _ _ _ _
      (by simpa [List.append_assoc] using hrest)
    exact ⟨by simp [hd, hc], hxy⟩
  · obtain ⟨hd, hrest⟩ := encDone_append_injective _ _ _ _
      (by simpa [List.append_assoc] using h)
    simp only [List.cons.injEq, true_and] at hrest
    obtain ⟨hc, hrest⟩ := encCode_append_injective _ _ _ _
      (by simpa [List.append_assoc] using hrest)
    simp only [List.cons.injEq, true_and] at hrest
    obtain ⟨ht, hrest⟩ := encNat_append_injective hrest
    obtain ⟨hi, hxy⟩ := encNat_append_injective hrest
    exact ⟨by simp [hd, hc, ht, hi], hxy⟩
  · obtain ⟨hd, hrest⟩ := encDone_append_injective _ _ _ _
      (by simpa [List.append_assoc] using h)
    simp only [List.cons.injEq, true_and] at hrest
    obtain ⟨hc, hrest⟩ := encCode_append_injective _ _ _ _
      (by simpa [List.append_assoc] using hrest)
    simp only [List.cons.injEq, true_and] at hrest
    obtain ⟨ht, hrest⟩ := encNat_append_injective hrest
    obtain ⟨hi, hxy⟩ := encNat_append_injective hrest
    exact ⟨by simp [hd, hc, ht, hi], hxy⟩
  · obtain ⟨hd, hrest⟩ := encDone_append_injective _ _ _ _
      (by simpa [List.append_assoc] using h)
    simp only [List.cons.injEq, true_and] at hrest
    obtain ⟨hz, hrest⟩ := encCode_append_injective _ _ _ _
      (by simpa [List.append_assoc] using hrest)
    simp only [List.cons.injEq, true_and] at hrest
    obtain ⟨hn, hrest⟩ := encCode_append_injective _ _ _ _
      (by simpa [List.append_assoc] using hrest)
    simp only [List.cons.injEq, true_and] at hrest
    obtain ⟨ht, hrest⟩ := encNat_append_injective hrest
    obtain ⟨hi, hxy⟩ := encNat_append_injective hrest
    exact ⟨by simp [hd, hz, hn, ht, hi], hxy⟩
  · obtain ⟨hd, hrest⟩ := encDone_append_injective _ _ _ _
      (by simpa [List.append_assoc] using h)
    simp only [List.cons.injEq, true_and] at hrest
    obtain ⟨hc, hxy⟩ := encCode_append_injective _ _ _ _
      (by simpa [List.append_assoc] using hrest)
    exact ⟨by simp [hd, hc], hxy⟩
  · obtain ⟨hd, hrest⟩ := encDone_append_injective _ _ _ _
      (by simpa [List.append_assoc] using h)
    simp only [List.cons.injEq, true_and] at hrest
    obtain ⟨hn, hxy⟩ := encNat_append_injective hrest
    exact ⟨by simp [hd, hn], hxy⟩
  · obtain ⟨hd, hrest⟩ := encDone_append_injective _ _ _ _
      (by simpa [List.append_assoc] using h)
    simp only [List.cons.injEq, true_and] at hrest
    obtain ⟨hn, hxy⟩ := encNat_append_injective hrest
    exact ⟨by simp [hd, hn], hxy⟩
  · obtain ⟨hp, hxy⟩ := encNat_append_injective h
    exact ⟨by simp [hp], hxy⟩

theorem encPhase_injective : Function.Injective encPhase := by
  intro p q h
  exact (encPhase_append_injective p q [] [] (by simpa using h)).1

@[simp] theorem marker_not_mem_encPhase (p : Phase) : '@' ∉ encPhase p := by
  cases p <;> simp [encPhase]

@[simp] theorem boundary_not_mem_encPhase (p : Phase) : 'b' ∉ encPhase p := by
  cases p <;> simp [encPhase, encNat]

/-- Every live machine phase is represented by one `@...$` token. -/
def token (p : Phase) : List Char := '@' :: encPhase p ++ ['$']

theorem token_injective : Function.Injective token := by
  intro p q h
  unfold token at h
  exact (encPhase_append_injective p q ['$'] ['$'] (List.cons.inj h).2).1

private theorem firstOccurrence_go_token_right (p : Phase) (extra pre post : List Char)
    (hpre : '@' ∉ pre) (i : Nat) :
    firstOccurrence?.go (token p ++ extra) (pre ++ token p ++ extra ++ post) i =
      some (i + pre.length) := by
  induction pre generalizing i with
  | nil => simp [firstOccurrence?.go, token]
  | cons a pre ih =>
      have ha : a ≠ '@' := fun h => hpre (h ▸ List.mem_cons_self)
      have hp : '@' ∉ pre := fun h => hpre (List.mem_cons_of_mem a h)
      rw [show (a :: pre) ++ token p ++ extra ++ post =
        a :: (pre ++ token p ++ extra ++ post) by simp]
      simp only [firstOccurrence?.go]
      rw [if_neg]
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih hp (i + 1)
      · intro hprefix
        have hh : '@' = a :=
          (show '@' = a ∧
              (encPhase p ++ '$' :: extra).isPrefixOf
                (pre ++ token p ++ extra ++ post) = true by
            simpa [token, List.isPrefixOf, List.append_assoc] using hprefix).1
        exact ha hh.symm

/-- The leftmost occurrence of a token-headed rule is exactly the represented
token.  The prefix may contain emitted `o` cells, but no active marker. -/
theorem firstOccurrence_token_right (p : Phase) (extra pre post : List Char)
    (hpre : '@' ∉ pre) :
    firstOccurrence? (token p ++ extra) (pre ++ token p ++ extra ++ post) =
      some pre.length := by
  unfold firstOccurrence?
  rw [if_neg (by simp [token])]
  simpa [List.append_assoc] using
    firstOccurrence_go_token_right p extra pre post hpre 0

private theorem firstOccurrence_go_token_left (p : Phase) (c : Char)
    (pre post : List Char) (hc : c ≠ '@') (hpre : '@' ∉ pre) (i : Nat) :
    firstOccurrence?.go (c :: token p) (pre ++ c :: token p ++ post) i =
      some (i + pre.length) := by
  induction pre generalizing i with
  | nil => simp [firstOccurrence?.go, token]
  | cons a pre ih =>
      have hp : '@' ∉ pre := fun h => hpre (List.mem_cons_of_mem a h)
      rw [show (a :: pre) ++ c :: token p ++ post =
        a :: (pre ++ c :: token p ++ post) by simp]
      simp only [firstOccurrence?.go]
      rw [if_neg]
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih hp (i + 1)
      · intro hprefix
        cases pre with
        | nil =>
            have hsecond : '@' = c :=
              (show c = a ∧ '@' = c ∧
                  (encPhase p ++ ['$']).isPrefixOf (token p ++ post) = true by
                simpa [token, List.isPrefixOf] using hprefix).2.1
            exact hc hsecond.symm
        | cons b bs =>
            have hb : b ≠ '@' := fun h => hp (h ▸ List.mem_cons_self)
            have hsecond : '@' = b :=
              (show c = a ∧ '@' = b ∧
                  (encPhase p ++ ['$']).isPrefixOf (bs ++ c :: token p ++ post) = true by
                simpa [token, List.isPrefixOf, List.append_assoc] using hprefix).2.1
            exact hb hsecond.symm

/-- The leftmost occurrence of a left-moving rule is the character directly
before the represented phase token. -/
theorem firstOccurrence_token_left (p : Phase) (c : Char) (pre post : List Char)
    (hc : c ≠ '@') (hpre : '@' ∉ pre) :
    firstOccurrence? (c :: token p) (pre ++ c :: token p ++ post) = some pre.length := by
  unfold firstOccurrence?
  rw [if_neg (by simp [token])]
  simpa [List.append_assoc] using
    firstOccurrence_go_token_left p c pre post hc hpre 0

/-- A successful occurrence search supplies the exact prefix and suffix at
which the pattern occurs. -/
private theorem firstOccurrence_go_factor (pat s : List Char) (i pos : Nat)
    (h : firstOccurrence?.go pat s i = some pos) :
    ∃ pre post, s = pre ++ pat ++ post ∧ pos = i + pre.length := by
  induction s generalizing i with
  | nil => simp [firstOccurrence?.go] at h
  | cons a s ih =>
      simp only [firstOccurrence?.go] at h
      split at h
      next hp =>
        have hprefix : pat <+: a :: s := by simpa using hp
        refine ⟨[], (a :: s).drop pat.length, ?_, by simpa using h.symm⟩
        simpa using (List.prefix_iff_eq_append.mp hprefix).symm
      next hp =>
        obtain ⟨pre, post, hs, hpos⟩ := ih (i + 1) h
        refine ⟨a :: pre, post, ?_, ?_⟩
        · simp [hs]
        · simp [hpos, Nat.add_comm, Nat.add_left_comm]

theorem firstOccurrence_factor (pat s : List Char) (pos : Nat)
    (h : firstOccurrence? pat s = some pos) :
    ∃ pre post, s = pre ++ pat ++ post ∧ pos = pre.length := by
  unfold firstOccurrence? at h
  split at h
  · simp at h
  · obtain ⟨pre, post, hs, hpos⟩ := firstOccurrence_go_factor pat s 0 pos h
    exact ⟨pre, post, hs, by simpa using hpos⟩

/-- A list containing one distinguished marker has a unique decomposition at
that marker. -/
theorem marker_decomp_unique : ∀ (as bs xs ys : List Char),
    '@' ∉ as → '@' ∉ bs →
    as ++ '@' :: xs = bs ++ '@' :: ys → as = bs ∧ xs = ys
  | [], [], xs, ys, _hax, _hby, h => by simpa using h
  | [], b :: bs, xs, ys, _hax, hby, h => by
      have hb : b ≠ '@' := fun he => hby (he ▸ List.mem_cons_self)
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact False.elim (hb h.1.symm)
  | a :: as, [], xs, ys, hax, _hby, h => by
      have ha : a ≠ '@' := fun he => hax (he ▸ List.mem_cons_self)
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact False.elim (ha h.1)
  | a :: as, b :: bs, xs, ys, hax, hby, h => by
      simp only [List.cons_append, List.cons.injEq] at h
      have has : '@' ∉ as := fun hm => hax (List.mem_cons_of_mem a hm)
      have hbs : '@' ∉ bs := fun hm => hby (List.mem_cons_of_mem b hm)
      obtain ⟨hab, htail⟩ := h
      obtain ⟨hpre, hpost⟩ := marker_decomp_unique as bs xs ys has hbs htail
      exact ⟨by simp [hab, hpre], hpost⟩

/-- If one complete token occurs in a represented state, its phase is the
represented phase. -/
theorem token_infix_phase (active q : Phase) (pre post a extra b : List Char)
    (hpre : '@' ∉ pre) (ha : '@' ∉ a)
    (h : pre ++ token active ++ post = a ++ token q ++ extra ++ b) : active = q := by
  have hm : pre ++ '@' :: (encPhase active ++ '$' :: post) =
      a ++ '@' :: (encPhase q ++ '$' :: (extra ++ b)) := by
    simpa [token, List.append_assoc] using h
  obtain ⟨_, htail⟩ := marker_decomp_unique pre a _ _ hpre ha hm
  exact (encPhase_append_injective active q ('$' :: post) ('$' :: (extra ++ b))
    (by simpa [List.append_assoc] using htail)).1

/-- In a represented state, the prefix preceding any complete token occurrence
contains no marker. -/
theorem not_mem_factor_prefix (active q : Phase) (pre post a extra b : List Char)
    (hpre : '@' ∉ pre) (hpost : '@' ∉ post)
    (h : pre ++ token active ++ post = a ++ token q ++ extra ++ b) : '@' ∉ a := by
  have hcount : (pre ++ token active ++ post).count '@' = 1 := by
    have ht : (token active).count '@' = 1 := by
      have hc : (encPhase active).count '@' = 0 :=
        List.count_eq_zero.mpr (marker_not_mem_encPhase active)
      simp [token, List.count_append, hc]
    simp [List.count_append, List.count_eq_zero.mpr hpre,
      List.count_eq_zero.mpr hpost, ht]
  have htq : (token q).count '@' = 1 := by
    have hc : (encPhase q).count '@' = 0 :=
      List.count_eq_zero.mpr (marker_not_mem_encPhase q)
    simp [token, List.count_append, hc]
  have heq := congrArg (List.count '@') h
  rw [hcount] at heq
  simp [List.count_append, htq] at heq
  exact List.count_eq_zero.mp (by omega)

/-- A token-right rule can match a uniquely marked state only when its
adjacent character is the actual character immediately after the token. -/
theorem token_right_match_cell (p : Phase) (actual expected : Char)
    (pre post : List Char) (hpre : '@' ∉ pre) (hpost : '@' ∉ post)
    (ha : actual ≠ '@') (pos : Nat)
    (hm : firstOccurrence? (token p ++ [expected])
      (pre ++ token p ++ actual :: post) = some pos) :
    expected = actual ∧ pos = pre.length := by
  obtain ⟨a, b, hs, hpos⟩ := firstOccurrence_factor _ _ _ hm
  have htail : '@' ∉ actual :: post := by
    simp only [List.mem_cons, not_or]
    exact ⟨ha.symm, hpost⟩
  have hma : '@' ∉ a :=
    not_mem_factor_prefix p p pre (actual :: post) a [expected] b
      hpre htail (by simpa [List.append_assoc] using hs)
  have hmark : pre ++ '@' :: (encPhase p ++ '$' :: actual :: post) =
      a ++ '@' :: (encPhase p ++ '$' :: expected :: b) := by
    simpa [token, List.append_assoc] using hs
  obtain ⟨hpa, hrest⟩ := marker_decomp_unique pre a _ _ hpre hma hmark
  have hsuffix : '$' :: actual :: post = '$' :: expected :: b :=
    (encPhase_append_injective p p ('$' :: actual :: post)
      ('$' :: expected :: b) (by simpa [List.append_assoc] using hrest)).2
  have hcells : actual :: post = expected :: b := (List.cons.inj hsuffix).2
  exact ⟨(List.cons.inj hcells).1.symm, by simpa [hpa] using hpos⟩

/-- A token-left rule can match a uniquely marked state only when its
adjacent character is the actual character immediately before the token. -/
theorem token_left_match_cell (p : Phase) (actual expected : Char)
    (pre post : List Char) (hpre : '@' ∉ pre) (hpost : '@' ∉ post)
    (ha : actual ≠ '@') (pos : Nat)
    (hm : firstOccurrence? (expected :: token p)
      (pre ++ actual :: token p ++ post) = some pos) :
    expected = actual ∧ pos = pre.length := by
  obtain ⟨a, b, hs, hpos⟩ := firstOccurrence_factor _ _ _ hm
  have hleft : '@' ∉ pre ++ [actual] := by
    simp only [List.mem_append, List.mem_singleton, not_or]
    exact ⟨hpre, ha.symm⟩
  have hright : '@' ∉ a ++ [expected] :=
    not_mem_factor_prefix p p (pre ++ [actual]) post (a ++ [expected]) [] b
      hleft hpost (by simpa [token, List.append_assoc] using hs)
  have hmark : (pre ++ [actual]) ++ '@' :: (encPhase p ++ '$' :: post) =
      (a ++ [expected]) ++ '@' :: (encPhase p ++ '$' :: b) := by
    simpa [token, List.append_assoc] using hs
  obtain ⟨hpref, _hrest⟩ :=
    marker_decomp_unique (pre ++ [actual]) (a ++ [expected]) _ _
      hleft hright hmark
  have hlast := congrArg List.getLast? hpref
  have hcell : actual = expected := by simpa using hlast
  have hlen := congrArg List.length hpref
  have hapos : a.length = pre.length := by simp at hlen; omega
  exact ⟨hcell.symm, by simpa [hapos] using hpos⟩

@[simp] theorem token_marker_count (p : Phase) : (token p).count '@' = 1 := by
  have hc : (encPhase p).count '@' = 0 :=
    List.count_eq_zero.mpr (marker_not_mem_encPhase p)
  simp [token, List.count_append, hc]

@[simp] theorem boundary_not_mem_token (p : Phase) : 'b' ∉ token p := by
  simp [token]

theorem control_token_injective : Function.Injective (fun pc => token (.control pc)) := by
  intro m n h
  simp only [token, encPhase] at h
  have htail := (List.cons.inj h).2
  have hpre := List.append_left_injective ['$'] htail
  have henc : encNat m = encNat n := by
    exact (List.cons.inj hpre).2
  exact encNat_injective henc

private def str (cs : List Char) : String := String.ofList cs

private def rule (lhs rhs : List Char) : Rule :=
  { lhs := str lhs, rhs := .str (str rhs) }

/-- The three syntactic forms used by every generated rule. -/
inductive RuleShape : Rule → Prop where
  | token (p : Phase) (rhs : List Char) : RuleShape (rule (token p) rhs)
  | right (p : Phase) (c : Char) (rhs : List Char) (hc : c ≠ '@') :
      RuleShape (rule (token p ++ [c]) rhs)
  | left (p : Phase) (c : Char) (rhs : List Char) (hc : c ≠ '@') :
      RuleShape (rule (c :: token p) rhs)

/-- A shaped rule whose token carries one specified active phase. -/
inductive ActiveRule (p : Phase) : Rule → Prop where
  | token (rhs : List Char) : ActiveRule p (rule (token p) rhs)
  | right (c : Char) (rhs : List Char) (hc : c ≠ '@') :
      ActiveRule p (rule (token p ++ [c]) rhs)
  | left (c : Char) (rhs : List Char) (hc : c ≠ '@') :
      ActiveRule p (rule (c :: token p) rhs)

theorem ActiveRule.phase_unique {p q : Phase} {r : Rule}
    (hp : ActiveRule p r) (hq : ActiveRule q r) : p = q := by
  have factor : ∀ {a : Phase} {s : Rule}, ActiveRule a s →
      ∃ pre post, '@' ∉ pre ∧ s.lhs.toList =
        pre ++ Langlib.Computability.URMThue.token a ++ post := by
    intro a s hs
    cases hs with
    | token rhs => exact ⟨[], [], by simp, by simp [rule, str]⟩
    | right c rhs hc => exact ⟨[], [c], by simp, by simp [rule, str]⟩
    | left c rhs hc => exact ⟨[c], [], by simpa [eq_comm] using hc, by simp [rule, str]⟩
  obtain ⟨ap, ep, hap, hrp⟩ := factor hp
  obtain ⟨aq, eq, haq, hrq⟩ := factor hq
  apply token_infix_phase p q ap ep aq eq [] hap haq
  rw [← hrp, ← hrq]
  simp

/-- Any generated-shaped rule that matches a represented state belongs to
the state's active phase. -/
theorem RuleShape.active_of_match {r : Rule} (hr : RuleShape r)
    (active : Phase) (pre post : List Char) (hpre : '@' ∉ pre) (hpost : '@' ∉ post)
    (pos : Nat)
    (hm : firstOccurrence? r.lhs.toList
      (pre ++ Langlib.Computability.URMThue.token active ++ post) = some pos) :
    ActiveRule active r := by
  cases hr with
  | token q rhs =>
      simp only [rule, str, String.toList_ofList] at hm
      obtain ⟨a, b, hs, _⟩ := firstOccurrence_factor _ _ _ hm
      have ha := not_mem_factor_prefix active q pre post a [] b hpre hpost
        (by simpa [List.append_assoc] using hs)
      have hp := token_infix_phase active q pre post a [] b hpre ha
        (by simpa [List.append_assoc] using hs)
      subst q
      exact .token _
  | right q c rhs hc =>
      simp only [rule, str, String.toList_ofList] at hm
      obtain ⟨a, b, hs, _⟩ := firstOccurrence_factor _ _ _ hm
      have ha := not_mem_factor_prefix active q pre post a [c] b hpre hpost
        (by simpa [List.append_assoc] using hs)
      have hp := token_infix_phase active q pre post a [c] b hpre ha
        (by simpa [List.append_assoc] using hs)
      subst q
      exact .right _ _ hc
  | left q c rhs hc =>
      simp only [rule, str, String.toList_ofList] at hm
      obtain ⟨a, b, hs, _⟩ := firstOccurrence_factor _ _ _ hm
      have hs' : pre ++ Langlib.Computability.URMThue.token active ++ post =
          (a ++ [c]) ++ Langlib.Computability.URMThue.token q ++ b := by
        simpa [List.append_assoc] using hs
      have ha := not_mem_factor_prefix active q pre post (a ++ [c]) [] b hpre hpost
        (by simpa [List.append_assoc] using hs')
      have hp := token_infix_phase active q pre post (a ++ [c]) [] b hpre ha
        (by simpa [List.append_assoc] using hs')
      subst q
      exact .left _ _ hc

/-- Applying a generated token-headed rule at the calculated marker position
replaces exactly its left-hand side. -/
theorem applyAt_rule_right (p : Phase) (extra pre rep post : List Char)
    (st : MState) (hs : st.str = pre ++ token p ++ extra ++ post) :
    applyAt st pre.length (rule (token p ++ extra) rep) =
      { st with str := pre ++ rep ++ post } := by
  have htake : st.str.take pre.length = pre := by
    rw [hs]
    simp
  have hdrop : st.str.drop (pre.length + (token p ++ extra).length) = post := by
    rw [hs]
    simp [List.append_assoc]
  obtain ⟨state, input, output, rng⟩ := st
  unfold applyAt rule str
  simp only [String.toList_ofList]
  simp_all [List.append_assoc]

/-- Applying a generated left-moving rule replaces the preceding cell and
the phase token at the calculated position. -/
theorem applyAt_rule_left (p : Phase) (c : Char) (pre rep post : List Char)
    (st : MState) (hs : st.str = pre ++ c :: token p ++ post) :
    applyAt st pre.length (rule (c :: token p) rep) =
      { st with str := pre ++ rep ++ post } := by
  have htake : st.str.take pre.length = pre := by
    rw [hs]
    simp
  have hdrop : st.str.drop (pre.length + (c :: token p).length) = post := by
    rw [hs]
    simp [List.append_assoc]
  obtain ⟨state, input, output, rng⟩ := st
  unfold applyAt rule str
  simp only [String.toList_ofList]
  simp_all [List.append_assoc]

/-- Every generated left-hand side is anchored by one active marker. -/
def RuleAnchored (r : Rule) : Prop := r.lhs.toList.count '@' = 1

private theorem anchored_token (p : Phase) (rhs : List Char) :
    RuleAnchored (rule (token p) rhs) := by
  simp [RuleAnchored, rule, str]

private theorem anchored_token_right (p : Phase) (c : Char) (rhs : List Char)
    (h : c ≠ '@') :
    RuleAnchored (rule (token p ++ [c]) rhs) := by
  simp [RuleAnchored, rule, str, List.count_append, h]

private theorem anchored_token_left (p : Phase) (c : Char) (rhs : List Char)
    (h : c ≠ '@') : RuleAnchored (rule (c :: token p) rhs) := by
  simp [RuleAnchored, rule, str, h]

/-! ## Rules for one counter operation -/

/-- Move a completed operation back across unary cells and delimiters, then
install the next control continuation at the left boundary. -/
def backRules (done : Done) (next : Code) : List Rule :=
  [ rule ('x' :: token (.back done next)) (token (.back done next) ++ ['x'])
  , rule ('d' :: token (.back done next)) (token (.back done next) ++ ['d'])
  , rule ('b' :: token (.back done next)) (token (.exec done next) ++ ['b'])
  ]

theorem backRules_anchored (done : Done) (next : Code) :
    ∀ r ∈ backRules done next, RuleAnchored r := by
  intro r hr
  simp [backRules] at hr
  rcases hr with rfl | rfl | rfl
  · exact anchored_token_left _ _ _ (by decide)
  · exact anchored_token_left _ _ _ (by decide)
  · exact anchored_token_left _ _ _ (by decide)

theorem backRules_shaped (done : Done) (next : Code) :
    ∀ r ∈ backRules done next, RuleShape r := by
  intro r hr
  simp [backRules] at hr
  rcases hr with rfl | rfl | rfl
  · exact .left _ _ _ (by decide)
  · exact .left _ _ _ (by decide)
  · exact .left _ _ _ (by decide)

/-- Scan to counter `target`, append one unary cell, and return. -/
def incRules (done : Done) (next : Code) (target : Nat) : List Rule :=
  ((List.range (target + 1)).flatMap fun current =>
    let p := Phase.scanInc done next target current
    if current < target then
      [ rule (token p ++ ['x']) ('x' :: token p)
      , rule (token p ++ ['d'])
          ('d' :: token (.scanInc done next target (current + 1)))
      ]
    else
      [ rule (token p ++ ['x']) ('x' :: token p)
      , rule (token p ++ ['d']) ('x' :: 'd' :: token (.back done next))
      ])
  ++ backRules done next

theorem incRules_anchored (done : Done) (next : Code) (target : Nat) :
    ∀ r ∈ incRules done next target, RuleAnchored r := by
  intro r hr
  simp only [incRules, List.mem_append, List.mem_flatMap] at hr
  rcases hr with ⟨current, _, hr⟩ | hr
  · split at hr
    all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    all_goals rcases hr with rfl | rfl
    all_goals exact anchored_token_right _ _ _ (by decide)
  · exact backRules_anchored done next r hr

theorem incRules_shaped (done : Done) (next : Code) (target : Nat) :
    ∀ r ∈ incRules done next target, RuleShape r := by
  intro r hr
  simp only [incRules, List.mem_append, List.mem_flatMap] at hr
  rcases hr with ⟨current, _, hr⟩ | hr
  · split at hr
    all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    all_goals rcases hr with rfl | rfl
    all_goals exact .right _ _ _ (by decide)
  · exact backRules_shaped done next r hr

/-- Scan to counter `target`, erase one unary cell, and return.  Counter-code
evaluation guarantees that the selected counter is nonzero. -/
def decRules (done : Done) (next : Code) (target : Nat) : List Rule :=
  ((List.range (target + 1)).flatMap fun current =>
    let p := Phase.scanDec done next target current
    if current < target then
      [ rule (token p ++ ['x']) ('x' :: token p)
      , rule (token p ++ ['d'])
          ('d' :: token (.scanDec done next target (current + 1)))
      ]
    else
      [rule (token p ++ ['x']) (token (.back done next))])
  ++ backRules done next

theorem decRules_anchored (done : Done) (next : Code) (target : Nat) :
    ∀ r ∈ decRules done next target, RuleAnchored r := by
  intro r hr
  simp only [decRules, List.mem_append, List.mem_flatMap] at hr
  rcases hr with ⟨current, _, hr⟩ | hr
  · split at hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact anchored_token_right _ _ _ (by decide)
      · exact anchored_token_right _ _ _ (by decide)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r
      exact anchored_token_right _ _ _ (by decide)
  · exact backRules_anchored done next r hr

theorem decRules_shaped (done : Done) (next : Code) (target : Nat) :
    ∀ r ∈ decRules done next target, RuleShape r := by
  intro r hr
  simp only [decRules, List.mem_append, List.mem_flatMap] at hr
  rcases hr with ⟨current, _, hr⟩ | hr
  · split at hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .right _ _ _ (by decide)
      · exact .right _ _ _ (by decide)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r
      exact .right _ _ _ (by decide)
  · exact backRules_shaped done next r hr

/-- Scan to counter `target` and choose a continuation according to whether
its unary run is empty. -/
def zeroRules (done : Done) (zero nonzero : Code) (target : Nat) : List Rule :=
  ((List.range (target + 1)).flatMap fun current =>
    let p := Phase.scanZero done zero nonzero target current
    if current < target then
      [ rule (token p ++ ['x']) ('x' :: token p)
      , rule (token p ++ ['d'])
          ('d' :: token (.scanZero done zero nonzero target (current + 1)))
      ]
    else
      [ rule (token p ++ ['d']) ('d' :: token (.back done zero))
      , rule (token p ++ ['x']) ('x' :: token (.back done nonzero))
      ])
  ++ backRules done zero ++ backRules done nonzero

theorem zeroRules_anchored (done : Done) (zero nonzero : Code) (target : Nat) :
    ∀ r ∈ zeroRules done zero nonzero target, RuleAnchored r := by
  intro r hr
  simp only [zeroRules, List.mem_append, List.mem_flatMap] at hr
  rcases hr with (⟨current, _, hr⟩ | hr) | hr
  · split at hr
    all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    all_goals rcases hr with rfl | rfl
    all_goals exact anchored_token_right _ _ _ (by decide)
  · exact backRules_anchored done zero r hr
  · exact backRules_anchored done nonzero r hr

theorem zeroRules_shaped (done : Done) (zero nonzero : Code) (target : Nat) :
    ∀ r ∈ zeroRules done zero nonzero target, RuleShape r := by
  intro r hr
  simp only [zeroRules, List.mem_append, List.mem_flatMap] at hr
  rcases hr with (⟨current, _, hr⟩ | hr) | hr
  · split at hr
    all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    all_goals rcases hr with rfl | rfl
    all_goals exact .right _ _ _ (by decide)
  · exact backRules_shaped done zero r hr
  · exact backRules_shaped done nonzero r hr

/-- Rules that leave one counter-code control continuation. -/
def headRules (done : Done) (current : Code) : List Rule :=
  match current with
  | [] => []
  | .inc r :: rest =>
      rule (token (.exec done current) ++ ['b'])
        ('b' :: token (.scanInc done rest r 0)) :: incRules done rest r
  | .dec r :: rest =>
      rule (token (.exec done current) ++ ['b'])
        ('b' :: token (.scanDec done rest r 0)) :: decRules done rest r
  | .emit :: rest =>
      [rule (token (.exec done current) ++ ['b'])
        ('o' :: token (.exec done rest) ++ ['b'])]
  | (.loop r body) :: rest =>
      let again := (.loop r body) :: rest
      let nonzero := body ++ again
      rule (token (.exec done current) ++ ['b'])
        ('b' :: token (.scanZero done rest nonzero r 0)) ::
          zeroRules done rest nonzero r

theorem headRules_anchored (done : Done) (current : Code) :
    ∀ r ∈ headRules done current, RuleAnchored r := by
  intro r hr
  cases current with
  | nil => simp [headRules] at hr
  | cons cmd rest =>
    cases cmd with
    | inc a =>
      simp only [headRules, List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact anchored_token_right _ _ _ (by decide)
      · exact incRules_anchored done rest a r hr
    | dec a =>
      simp only [headRules, List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact anchored_token_right _ _ _ (by decide)
      · exact decRules_anchored done rest a r hr
    | emit =>
      simp only [headRules, List.mem_singleton] at hr
      subst r
      exact anchored_token_right _ _ _ (by decide)
    | loop a body =>
      simp only [headRules, List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact anchored_token_right _ _ _ (by decide)
      · exact zeroRules_anchored done rest (body ++ Cmd.loop a body :: rest) a r hr

theorem headRules_shaped (done : Done) (current : Code) :
    ∀ r ∈ headRules done current, RuleShape r := by
  intro r hr
  cases current with
  | nil => simp [headRules] at hr
  | cons cmd rest =>
    cases cmd with
    | inc a =>
      simp only [headRules, List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact .right _ _ _ (by decide)
      · exact incRules_shaped done rest a r hr
    | dec a =>
      simp only [headRules, List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact .right _ _ _ (by decide)
      · exact decRules_shaped done rest a r hr
    | emit =>
      simp only [headRules, List.mem_singleton] at hr
      subst r
      exact .right _ _ _ (by decide)
    | loop a body =>
      simp only [headRules, List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact .right _ _ _ (by decide)
      · exact zeroRules_shaped done rest (body ++ Cmd.loop a body :: rest) a r hr

/-! ## Finite rule generation -/

/-- A structural size that counts all nested commands. -/
def codeWeight : Code → Nat
  | [] => 0
  | .loop _ body :: rest => codeWeight body + codeWeight rest + 1
  | _ :: rest => codeWeight rest + 1

set_option linter.unnecessarySeqFocus false in
/-- Generate rules for `code ++ suffix`.  Loop bodies are traversed with the
loop continuation as their suffix, which covers every continuation exposed by
the counter-machine `Ev.loopS` rule without unfolding a loop infinitely. -/
def generate : (done : Done) → (code suffix : Code) → List Rule
  | _, [], _ => []
  | done, cmd :: rest, suffix =>
      let current := cmd :: (rest ++ suffix)
      let tailRules := generate done rest suffix
      match cmd with
      | .loop _ body =>
          headRules done current ++ generate done body current ++ tailRules
      | _ => headRules done current ++ tailRules
termination_by _ code _ => codeWeight code
decreasing_by
  · cases cmd <;> simp [codeWeight] <;> omega
  · simp [codeWeight] <;> omega

/-- Every recursively generated counter-code rule has one of the three
marker-anchored shapes. -/
theorem generate_shaped : ∀ (done : Done) (code suffix : Code) (r : Rule),
    r ∈ generate done code suffix → RuleShape r
  | _, [], _, _, h => by simp [generate] at h
  | done, .inc a :: rest, suffix, r, h => by
      simp only [generate, List.mem_append] at h
      rcases h with hh | ht
      · exact headRules_shaped done (.inc a :: (rest ++ suffix)) r hh
      · exact generate_shaped done rest suffix r ht
  | done, .dec a :: rest, suffix, r, h => by
      simp only [generate, List.mem_append] at h
      rcases h with hh | ht
      · exact headRules_shaped done (.dec a :: (rest ++ suffix)) r hh
      · exact generate_shaped done rest suffix r ht
  | done, .emit :: rest, suffix, r, h => by
      simp only [generate, List.mem_append] at h
      rcases h with hh | ht
      · exact headRules_shaped done (.emit :: (rest ++ suffix)) r hh
      · exact generate_shaped done rest suffix r ht
  | done, .loop a body :: rest, suffix, r, h => by
      simp only [generate, List.mem_append] at h
      rcases h with (hh | hb) | ht
      · exact headRules_shaped done (.loop a body :: (rest ++ suffix)) r hh
      · exact generate_shaped done body (.loop a body :: (rest ++ suffix)) r hb
      · exact generate_shaped done rest suffix r ht
termination_by done code suffix r _h => codeWeight code
decreasing_by
  all_goals simp [codeWeight] <;> omega

/-- Largest unary program-counter value accepted by a dispatch phase. -/
def maxOutcome (os : List Outcome) : Nat := os.foldl (fun n o => max n o.count) 0

/-- The canonical local rules determined solely by a phase value.  Generator
traversal may emit a canonical rule more than once, but cannot change it. -/
def phaseRules : Phase → List Rule
  | .control _ => []
  | .exec done [] =>
      [rule (token (.exec done []) ++ ['b']) ('b' :: token (.seekPC done 0))]
  | .exec done (.inc r :: rest) =>
      [rule (token (.exec done (.inc r :: rest)) ++ ['b'])
        ('b' :: token (.scanInc done rest r 0))]
  | .exec done (.dec r :: rest) =>
      [rule (token (.exec done (.dec r :: rest)) ++ ['b'])
        ('b' :: token (.scanDec done rest r 0))]
  | .exec done (.emit :: rest) =>
      [rule (token (.exec done (.emit :: rest)) ++ ['b'])
        ('o' :: token (.exec done rest) ++ ['b'])]
  | .exec done ((.loop r body) :: rest) =>
      [rule (token (.exec done ((.loop r body) :: rest)) ++ ['b'])
        ('b' :: token (.scanZero done rest (body ++ (.loop r body) :: rest) r 0))]
  | .scanInc done next target current =>
      if current < target then
        [ rule (token (.scanInc done next target current) ++ ['x'])
            ('x' :: token (.scanInc done next target current))
        , rule (token (.scanInc done next target current) ++ ['d'])
            ('d' :: token (.scanInc done next target (current + 1))) ]
      else
        [ rule (token (.scanInc done next target current) ++ ['x'])
            ('x' :: token (.scanInc done next target current))
        , rule (token (.scanInc done next target current) ++ ['d'])
            ('x' :: 'd' :: token (.back done next)) ]
  | .scanDec done next target current =>
      if current < target then
        [ rule (token (.scanDec done next target current) ++ ['x'])
            ('x' :: token (.scanDec done next target current))
        , rule (token (.scanDec done next target current) ++ ['d'])
            ('d' :: token (.scanDec done next target (current + 1))) ]
      else
        [rule (token (.scanDec done next target current) ++ ['x'])
          (token (.back done next))]
  | .scanZero done zero nonzero target current =>
      if current < target then
        [ rule (token (.scanZero done zero nonzero target current) ++ ['x'])
            ('x' :: token (.scanZero done zero nonzero target current))
        , rule (token (.scanZero done zero nonzero target current) ++ ['d'])
            ('d' :: token (.scanZero done zero nonzero target (current + 1))) ]
      else
        [ rule (token (.scanZero done zero nonzero target current) ++ ['d'])
            ('d' :: token (.back done zero))
        , rule (token (.scanZero done zero nonzero target current) ++ ['x'])
            ('x' :: token (.back done nonzero)) ]
  | .back done next => backRules done next
  | .seekPC done current =>
      if current < done.target then
        [ rule (token (.seekPC done current) ++ ['x'])
            ('x' :: token (.seekPC done current))
        , rule (token (.seekPC done current) ++ ['d'])
            ('d' :: token (.seekPC done (current + 1))) ]
      else
        [rule (token (.seekPC done current) ++ ['x']) (token (.countPC done 1))]
  | .countPC done count =>
      rule (token (.countPC done count) ++ ['x'])
          (token (.countPC done (count + 1))) ::
        (done.outcomes.filter (fun o => o.count == count)).map fun o =>
          rule (token (.countPC done count) ++ ['d']) ('d' :: token (.backPC o.pc))
  | .backPC pc =>
      [ rule ('x' :: token (.backPC pc)) (token (.backPC pc) ++ ['x'])
      , rule ('d' :: token (.backPC pc)) (token (.backPC pc) ++ ['d'])
      , rule ('b' :: token (.backPC pc)) (token (.control pc) ++ ['b']) ]

theorem phaseRules_active (p : Phase) : ∀ r ∈ phaseRules p, ActiveRule p r := by
  intro r hr
  cases p with
  | control pc => simp [phaseRules] at hr
  | exec done code =>
      cases code with
      | nil => simp [phaseRules] at hr; subst r; exact .right _ _ (by decide)
      | cons cmd rest =>
        cases cmd <;> simp [phaseRules] at hr <;> subst r
        all_goals exact .right _ _ (by decide)
  | scanInc done next target current =>
      simp only [phaseRules] at hr
      split at hr
      all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      all_goals rcases hr with rfl | rfl
      all_goals exact .right _ _ (by decide)
  | scanDec done next target current =>
      simp only [phaseRules] at hr
      split at hr
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact .right _ _ (by decide)
      · simp only [List.mem_singleton] at hr
        subst r
        exact .right _ _ (by decide)
  | scanZero done zero nonzero target current =>
      simp only [phaseRules] at hr
      split at hr
      all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      all_goals rcases hr with rfl | rfl
      all_goals exact .right _ _ (by decide)
  | back done next =>
      simp [phaseRules, backRules] at hr
      rcases hr with rfl | rfl | rfl
      all_goals exact .left _ _ (by decide)

  | seekPC done current =>
      simp only [phaseRules] at hr
      split at hr
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact .right _ _ (by decide)
      · simp only [List.mem_singleton] at hr
        subst r
        exact .right _ _ (by decide)
  | countPC done count =>
      simp only [phaseRules, List.mem_cons, List.mem_map] at hr
      rcases hr with rfl | ⟨o, _ho, rfl⟩
      · exact .right _ _ (by decide)
      · exact .right _ _ (by decide)
  | backPC pc =>
      simp [phaseRules] at hr
      rcases hr with rfl | rfl | rfl
      all_goals exact .left _ _ (by decide)

/-- Dispatch tables used by a live instruction map a unary count to at most
one destination program counter. -/
def OutcomeFunctional (os : List Outcome) : Prop :=
  ∀ a ∈ os, ∀ b ∈ os, a.count = b.count → a.pc = b.pc

/-- The only canonical family whose right-hand side is not syntactically
fixed by its left-hand side is `countPC`: several outcomes can emit the same
`token ++ d` lhs.  A functional outcome table makes those rules equal too. -/
theorem phaseRules_lhs_functional (p : Phase)
    (hout : ∀ done count, p = .countPC done count →
      OutcomeFunctional done.outcomes) :
    ∀ r ∈ phaseRules p, ∀ s ∈ phaseRules p,
      r.lhs = s.lhs → r = s := by
  intro r hr s hs hlhs
  cases p with
  | control pc => simp [phaseRules] at hr
  | exec done code =>
      cases code with
      | nil => simp [phaseRules] at hr hs; subst r; subst s; rfl
      | cons cmd rest =>
        cases cmd <;> simp [phaseRules] at hr hs <;> subst r <;> subst s <;> rfl
  | scanInc done next target current =>
      by_cases h : current < target
      · simp [phaseRules, h] at hr hs
        rcases hr with rfl | rfl <;> rcases hs with rfl | rfl
        all_goals simp [rule, str] at hlhs ⊢
      · simp [phaseRules, h] at hr hs
        rcases hr with rfl | rfl <;> rcases hs with rfl | rfl
        all_goals simp [rule, str] at hlhs ⊢
  | scanDec done next target current =>
      by_cases h : current < target
      · simp [phaseRules, h] at hr hs
        rcases hr with rfl | rfl <;> rcases hs with rfl | rfl
        all_goals simp [rule, str] at hlhs ⊢
      · simp [phaseRules, h] at hr hs
        subst r
        subst s
        rfl
  | scanZero done zero nonzero target current =>
      by_cases h : current < target
      · simp [phaseRules, h] at hr hs
        rcases hr with rfl | rfl <;> rcases hs with rfl | rfl
        all_goals simp [rule, str] at hlhs ⊢
      · simp [phaseRules, h] at hr hs
        rcases hr with rfl | rfl <;> rcases hs with rfl | rfl
        all_goals simp [rule, str] at hlhs ⊢
  | back done next =>
      simp [phaseRules, backRules] at hr hs
      rcases hr with rfl | rfl | rfl <;> rcases hs with rfl | rfl | rfl
      all_goals simp [rule, str] at hlhs ⊢
  | seekPC done current =>
      by_cases h : current < done.target
      · simp [phaseRules, h] at hr hs
        rcases hr with rfl | rfl <;> rcases hs with rfl | rfl
        all_goals simp [rule, str] at hlhs ⊢
      · simp [phaseRules, h] at hr hs
        subst r
        subst s
        rfl
  | countPC done count =>
      simp only [phaseRules, List.mem_cons, List.mem_map] at hr hs
      rcases hr with rfl | ⟨a, ha, rfl⟩ <;> rcases hs with rfl | ⟨b, hb, rfl⟩
      · rfl
      · simp [rule, str] at hlhs
      · simp [rule, str] at hlhs
      · have hac : a.count = count := by
          have := (List.mem_filter.mp ha).2
          simpa using this
        have hbc : b.count = count := by
          have := (List.mem_filter.mp hb).2
          simpa using this
        have hpc : a.pc = b.pc :=
          hout done count rfl a (List.mem_filter.mp ha).1 b
            (List.mem_filter.mp hb).1 (by omega)
        simp [hpc]
  | backPC pc =>
      simp [phaseRules] at hr hs
      rcases hr with rfl | rfl | rfl <;> rcases hs with rfl | rfl | rfl
      all_goals simp [rule, str] at hlhs ⊢

def HasPhase (r : Rule) : Prop := ∃ p, r ∈ phaseRules p

theorem backRules_hasPhase (done : Done) (next : Code) :
    ∀ r ∈ backRules done next, HasPhase r := by
  intro r hr
  exact ⟨.back done next, by simpa [phaseRules] using hr⟩

theorem incRules_hasPhase (done : Done) (next : Code) (target : Nat) :
    ∀ r ∈ incRules done next target, HasPhase r := by
  intro r hr
  simp only [incRules, List.mem_append, List.mem_flatMap] at hr
  rcases hr with ⟨current, _, hr⟩ | hr
  · refine ⟨.scanInc done next target current, ?_⟩
    simpa [phaseRules] using hr
  · exact backRules_hasPhase done next r hr

theorem decRules_hasPhase (done : Done) (next : Code) (target : Nat) :
    ∀ r ∈ decRules done next target, HasPhase r := by
  intro r hr
  simp only [decRules, List.mem_append, List.mem_flatMap] at hr
  rcases hr with ⟨current, _, hr⟩ | hr
  · refine ⟨.scanDec done next target current, ?_⟩
    simpa [phaseRules] using hr
  · exact backRules_hasPhase done next r hr

theorem zeroRules_hasPhase (done : Done) (zero nonzero : Code) (target : Nat) :
    ∀ r ∈ zeroRules done zero nonzero target, HasPhase r := by
  intro r hr
  simp only [zeroRules, List.mem_append, List.mem_flatMap] at hr
  rcases hr with (⟨current, _, hr⟩ | hr) | hr
  · refine ⟨.scanZero done zero nonzero target current, ?_⟩
    simpa [phaseRules] using hr
  · exact backRules_hasPhase done zero r hr
  · exact backRules_hasPhase done nonzero r hr

theorem headRules_hasPhase (done : Done) (current : Code) :
    ∀ r ∈ headRules done current, HasPhase r := by
  intro r hr
  cases current with
  | nil => simp [headRules] at hr
  | cons cmd rest =>
    cases cmd with
    | inc a =>
      simp only [headRules, List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact ⟨.exec done (.inc a :: rest), by simp [phaseRules]⟩
      · exact incRules_hasPhase done rest a r hr
    | dec a =>
      simp only [headRules, List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact ⟨.exec done (.dec a :: rest), by simp [phaseRules]⟩
      · exact decRules_hasPhase done rest a r hr
    | emit =>
      simp only [headRules, List.mem_singleton] at hr
      subst r
      exact ⟨.exec done (.emit :: rest), by simp [phaseRules]⟩
    | loop a body =>
      simp only [headRules, List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact ⟨.exec done (.loop a body :: rest), by simp [phaseRules]⟩
      · exact zeroRules_hasPhase done rest (body ++ Cmd.loop a body :: rest) a r hr

theorem generate_hasPhase : ∀ (done : Done) (code suffix : Code) (r : Rule),
    r ∈ generate done code suffix → HasPhase r
  | _, [], _, _, h => by simp [generate] at h
  | done, .inc a :: rest, suffix, r, h => by
      simp only [generate, List.mem_append] at h
      rcases h with hh | ht
      · exact headRules_hasPhase done (.inc a :: (rest ++ suffix)) r hh
      · exact generate_hasPhase done rest suffix r ht
  | done, .dec a :: rest, suffix, r, h => by
      simp only [generate, List.mem_append] at h
      rcases h with hh | ht
      · exact headRules_hasPhase done (.dec a :: (rest ++ suffix)) r hh
      · exact generate_hasPhase done rest suffix r ht
  | done, .emit :: rest, suffix, r, h => by
      simp only [generate, List.mem_append] at h
      rcases h with hh | ht
      · exact headRules_hasPhase done (.emit :: (rest ++ suffix)) r hh
      · exact generate_hasPhase done rest suffix r ht
  | done, .loop a body :: rest, suffix, r, h => by
      simp only [generate, List.mem_append] at h
      rcases h with (hh | hb) | ht
      · exact headRules_hasPhase done (.loop a body :: (rest ++ suffix)) r hh
      · exact generate_hasPhase done body (.loop a body :: (rest ++ suffix)) r hb
      · exact generate_hasPhase done rest suffix r ht
termination_by done code suffix r _h => codeWeight code
decreasing_by
  all_goals simp [codeWeight] <;> omega

/-- Rules that consume the counter-machine program counter and install a
source URM control marker. -/
def finishRules (done : Done) : List Rule :=
  let seekRules := (List.range (done.target + 1)).flatMap fun current =>
    let p := Phase.seekPC done current
    if current < done.target then
      [ rule (token p ++ ['x']) ('x' :: token p)
      , rule (token p ++ ['d']) ('d' :: token (.seekPC done (current + 1)))
      ]
    else
      [rule (token p ++ ['x']) (token (.countPC done 1))]
  let countRules := (List.range (maxOutcome done.outcomes + 1)).flatMap fun n =>
    [rule (token (.countPC done n) ++ ['x']) (token (.countPC done (n + 1)))]
  let chooseRules := done.outcomes.map fun o =>
    rule (token (.countPC done o.count) ++ ['d'])
      ('d' :: token (.backPC o.pc))
  let returnRules := done.outcomes.flatMap fun o =>
    [ rule ('x' :: token (.backPC o.pc)) (token (.backPC o.pc) ++ ['x'])
    , rule ('d' :: token (.backPC o.pc)) (token (.backPC o.pc) ++ ['d'])
    , rule ('b' :: token (.backPC o.pc)) (token (.control o.pc) ++ ['b'])
    ]
  rule (token (.exec done []) ++ ['b'])
      ('b' :: token (.seekPC done 0)) ::
    seekRules ++ countRules ++ chooseRules ++ returnRules

theorem finishRules_shaped (done : Done) :
    ∀ r ∈ finishRules done, RuleShape r := by
  intro r hr
  simp only [finishRules, List.mem_cons, List.mem_append, List.mem_flatMap,
    List.mem_map] at hr
  rcases hr with (((hr | hr) | hr) | hr) | hr
  · subst r
    exact .right _ _ _ (by decide)
  · obtain ⟨a, _ha, hr⟩ := hr
    split at hr
    all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    · rcases hr with rfl | rfl
      · exact .right _ _ _ (by decide)
      · exact .right _ _ _ (by decide)
    · subst r
      exact .right _ _ _ (by decide)
  · obtain ⟨a, _ha, hr⟩ := hr
    rcases hr with rfl | hr
    · exact .right _ _ _ (by decide)
    · simp at hr
  · obtain ⟨o, _ho, hr⟩ := hr
    subst r
    exact .right _ _ _ (by decide)
  · obtain ⟨o, _ho, hr⟩ := hr
    rcases hr with rfl | rfl | rfl | hr
    · exact .left _ _ _ (by decide)
    · exact .left _ _ _ (by decide)
    · exact .left _ _ _ (by decide)
    · simp at hr

theorem finishRules_hasPhase (done : Done) :
    ∀ r ∈ finishRules done, HasPhase r := by
  intro r hr
  simp only [finishRules, List.mem_cons, List.mem_append, List.mem_flatMap,
    List.mem_map] at hr
  rcases hr with (((hr | hr) | hr) | hr) | hr
  · subst r
    exact ⟨.exec done [], by simp [phaseRules]⟩
  · obtain ⟨a, _ha, hr⟩ := hr
    split at hr
    all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    · rcases hr with rfl | rfl
      · exact ⟨.seekPC done a, by simp [phaseRules, *]⟩
      · exact ⟨.seekPC done a, by simp [phaseRules, *]⟩
    · subst r
      exact ⟨.seekPC done a, by simp [phaseRules, *]⟩
  · obtain ⟨a, _ha, hr⟩ := hr
    rcases hr with rfl | hr
    · exact ⟨.countPC done a, by simp [phaseRules]⟩
    · simp at hr
  · obtain ⟨o, ho, hr⟩ := hr
    subst r
    refine ⟨.countPC done o.count, ?_⟩
    simp only [phaseRules, List.mem_cons, List.mem_map, List.mem_filter]
    right
    exact ⟨o, ⟨ho, by simp⟩, rfl⟩
  · obtain ⟨o, _ho, hr⟩ := hr
    rcases hr with rfl | rfl | rfl | hr
    · exact ⟨.backPC o.pc, by simp [phaseRules]⟩
    · exact ⟨.backPC o.pc, by simp [phaseRules]⟩
    · exact ⟨.backPC o.pc, by simp [phaseRules]⟩
    · simp at hr

/-- Possible values written to the counter-machine program counter by source
instruction `i` at index `k`. -/
def outcomes (k : Nat) : Cslib.URM.Instr → List Outcome
  | .J m n q => if m = n then [⟨q + 1, q⟩] else [⟨q + 1, q⟩, ⟨k + 2, k + 1⟩]
  | _ => [⟨k + 2, k + 1⟩]

/-- Dispatch counts emitted for one source instruction determine a unique
source program counter. Duplicate outcomes can occur, but are equal. -/
theorem outcomes_functional (k : Nat) (i : Cslib.URM.Instr) :
    ∀ a ∈ outcomes k i, ∀ b ∈ outcomes k i, a.count = b.count → a.pc = b.pc := by
  intro a ha b hb hc
  cases i with
  | Z r | S r | T r s =>
      simp [outcomes] at ha hb
      subst a
      subst b
      rfl
  | J m n q =>
      by_cases hmn : m = n
      · simp [outcomes, hmn] at ha hb
        subst a
        subst b
        rfl
      · simp [outcomes, hmn] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all

/-- The arithmetic successor selected by `execInstr` is one of the dispatch
outcomes emitted for the source instruction. -/
theorem nextPC_mem_outcomes (k : Nat) (i : Cslib.URM.Instr) (regs : Cslib.URM.Regs) :
    ⟨instrNextPC k i regs + 1, instrNextPC k i regs⟩ ∈ outcomes k i := by
  cases i with
  | Z r => simp [instrNextPC, outcomes]
  | S r => simp [instrNextPC, outcomes]
  | T m n => simp [instrNextPC, outcomes]
  | J m n q =>
    by_cases hmn : m = n
    · subst n; simp [instrNextPC, outcomes]
    · by_cases h : regs.read m = regs.read n
      · simp [instrNextPC, outcomes, hmn, h]
      · simp [instrNextPC, outcomes, hmn, h]

/-- Counter macro used by the Thue compiler.  A syntactic self-comparison is
an unconditional jump, so it only needs to write the target literal. -/
def macroCode (B k : Nat) : Cslib.URM.Instr → Code
  | .J m n q => if m = n then incMany (pcReg B) (q + 1) else execInstr B k (.J m n q)
  | i => execInstr B k i

/-- One selected URM instruction has a proved counter-macro execution whose
source counters agree with the URM successor, whose scratch counters are
clean, and whose encoded next program counter is accepted by the generated
dispatch table. -/
theorem instruction_macro_correct {B k : Nat} (i : Cslib.URM.Instr)
    (regs : Cslib.URM.Regs) (hmax : i.maxRegister < B) (s : CState)
    (hsrc : SourceMatches B s.regs regs) (hpc : s.regs (pcReg B) = 0)
    (hclean : ScratchClean B s.regs) :
    ∃ w', Ev (counterBound B) (execInstr B k i) s ⟨w', s.out⟩ ∧
      SourceMatches B w' (instrNextRegs i regs) ∧
      w' (pcReg B) = instrNextPC k i regs + 1 ∧
      ScratchClean B w' ∧
      ⟨w' (pcReg B), instrNextPC k i regs⟩ ∈ outcomes k i := by
  obtain ⟨w', hev, hsrc', hpc', hclean'⟩ :=
    execInstr_spec i regs hmax s hsrc hpc hclean
  exact ⟨w', hev, hsrc', hpc', hclean', hpc' ▸ nextPC_mem_outcomes k i regs⟩

/-- Correctness of the macro actually emitted by `instrRules`, including the
short unconditional-jump case. -/
theorem macroCode_correct {B k : Nat} (i : Cslib.URM.Instr)
    (regs : Cslib.URM.Regs) (hmax : i.maxRegister < B) (s : CState)
    (hsrc : SourceMatches B s.regs regs) (hpc : s.regs (pcReg B) = 0)
    (hclean : ScratchClean B s.regs) :
    ∃ w', Ev (counterBound B) (macroCode B k i) s ⟨w', s.out⟩ ∧
      SourceMatches B w' (instrNextRegs i regs) ∧
      w' (pcReg B) = instrNextPC k i regs + 1 ∧
      ScratchClean B w' ∧
      ⟨w' (pcReg B), instrNextPC k i regs⟩ ∈ outcomes k i := by
  cases i with
  | Z r => simpa [macroCode] using instruction_macro_correct (.Z r) regs hmax s hsrc hpc hclean
  | S r => simpa [macroCode] using instruction_macro_correct (.S r) regs hmax s hsrc hpc hclean
  | T m n => simpa [macroCode] using instruction_macro_correct (.T m n) regs hmax s hsrc hpc hclean
  | J m n q =>
    by_cases hmn : m = n
    · subst n
      have hp : pcReg B < counterBound B := by simp [pcReg, counterBound]
      obtain ⟨w', hev, hwpc, hfr⟩ := incMany_spec hp (q + 1) s
      refine ⟨w', ?_, ?_, ?_, ?_, ?_⟩
      · simpa [macroCode] using hev
      · intro r hr
        rw [hfr r (by simp [pcReg]; omega), hsrc r hr]
        rfl
      · rw [hwpc, hpc]
        simp [instrNextPC]
      · apply ScratchClean.frame hclean
        intro r hBr hrR
        exact hfr r (by simp [pcReg]; omega)
      · rw [hwpc, hpc]
        simp [instrNextPC, outcomes]
    · simpa [macroCode, hmn] using
        instruction_macro_correct (.J m n q) regs hmax s hsrc hpc hclean

theorem instr_below_sourceBound {P : Cslib.URM.Program} {inputs : List Nat}
    {i : Cslib.URM.Instr} (hi : i ∈ P) : i.maxRegister < sourceBound P inputs := by
  exact programBelow_sourceBound P inputs i hi

theorem ofInputs_eq_zero_of_length_le (inputs : List Nat) {r : Nat}
    (h : inputs.length ≤ r) : Cslib.URM.Regs.ofInputs inputs r = 0 := by
  simp [Cslib.URM.Regs.ofInputs, List.getD_eq_getElem?_getD,
    List.getElem?_eq_none h]

/-- The compiled initial register file agrees with the URM input and has the
counter-macro program counter and all comparison scratch counters cleared. -/
theorem initial_macro_invariant (P : Cslib.URM.Program) (inputs : List Nat) :
    let B := sourceBound P inputs
    SourceMatches B (Cslib.URM.Regs.ofInputs inputs) (Cslib.URM.Regs.ofInputs inputs) ∧
    Cslib.URM.Regs.ofInputs inputs (pcReg B) = 0 ∧
    ScratchClean B (Cslib.URM.Regs.ofInputs inputs) := by
  let B := sourceBound P inputs
  have hlen : inputs.length ≤ B := by simp [B, sourceBound]
  refine ⟨fun _ _ => rfl, ofInputs_eq_zero_of_length_le inputs (by simpa [pcReg] using hlen), ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ofInputs_eq_zero_of_length_le inputs (by simp only [savedReg]; omega)
  · exact ofInputs_eq_zero_of_length_le inputs (by simp only [cmpXReg]; omega)
  · exact ofInputs_eq_zero_of_length_le inputs (by simp only [cmpYReg]; omega)
  · exact ofInputs_eq_zero_of_length_le inputs (by simp only [tmpReg]; omega)
  · exact ofInputs_eq_zero_of_length_le inputs (by simp only [gateReg]; omega)
  · exact ofInputs_eq_zero_of_length_le inputs (by simp only [eqReg]; omega)
  · exact ofInputs_eq_zero_of_length_le inputs (by simp only [fallReg]; omega)

/-- Generated rules for one source instruction. -/
def instrRules (B k : Nat) (i : Cslib.URM.Instr) : List Rule :=
  let done : Done := ⟨pcReg B, outcomes k i⟩
  let code := macroCode B k i
  rule (token (.control k)) (token (.exec done code)) ::
    generate done code [] ++ finishRules done

theorem instrRules_shaped (B k : Nat) (i : Cslib.URM.Instr) :
    ∀ r ∈ instrRules B k i, RuleShape r := by
  intro r hr
  simp only [instrRules, List.mem_cons, List.mem_append] at hr
  rcases hr with (rfl | hg) | hf
  · exact .token _ _
  · exact generate_shaped _ _ _ r hg
  · exact finishRules_shaped _ r hf

theorem instrRules_origin (B k : Nat) (i : Cslib.URM.Instr) :
    ∀ r ∈ instrRules B k i,
      r = rule (token (.control k))
          (token (.exec ⟨pcReg B, outcomes k i⟩ (macroCode B k i))) ∨ HasPhase r := by
  intro r hr
  simp only [instrRules, List.mem_cons, List.mem_append] at hr
  rcases hr with (rfl | hg) | hf
  · exact Or.inl rfl
  · exact Or.inr (generate_hasPhase _ _ _ r hg)
  · exact Or.inr (finishRules_hasPhase _ r hf)

/-- Generate one finite rule block per URM instruction. -/
def compileAt (B : Nat) : Nat → Cslib.URM.Program → List Rule
  | _, [] => []
  | k, i :: rest => instrRules B k i ++ compileAt B (k + 1) rest

theorem compileAt_shaped (B : Nat) : ∀ (k : Nat) (P : Cslib.URM.Program) (r : Rule),
    r ∈ compileAt B k P → RuleShape r
  | _, [], _, h => by simp [compileAt] at h
  | k, i :: rest, r, h => by
      simp only [compileAt, List.mem_append] at h
      rcases h with hi | ht
      · exact instrRules_shaped B k i r hi
      · exact compileAt_shaped B (k + 1) rest r ht

theorem compileAt_origin (B : Nat) :
    ∀ (base : Nat) (P : Cslib.URM.Program) (r : Rule), r ∈ compileAt B base P →
      HasPhase r ∨ ∃ offset i, P[offset]? = some i ∧
        r = rule (token (.control (base + offset)))
          (token (.exec ⟨pcReg B, outcomes (base + offset) i⟩
            (macroCode B (base + offset) i)))
  | _, [], _, h => by simp [compileAt] at h
  | base, head :: rest, r, h => by
      simp only [compileAt, List.mem_append] at h
      rcases h with hi | ht
      · rcases instrRules_origin B base head r hi with he | hp
        · exact Or.inr ⟨0, head, by simp, by simpa using he⟩
        · exact Or.inl hp
      · rcases compileAt_origin B (base + 1) rest r ht with hp | he
        · exact Or.inl hp
        · obtain ⟨offset, i, hi, he⟩ := he
          refine Or.inr ⟨offset + 1, i, ?_, ?_⟩
          · exact hi
          · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he

/-- The control-entry rule for any source instruction occurs in its generated
block at the correspondingly shifted program counter. -/
theorem control_rule_mem_compileAt (B : Nat) :
    ∀ (base : Nat) (P : Cslib.URM.Program) (offset : Nat) (i : Cslib.URM.Instr),
      P[offset]? = some i →
      rule (token (.control (base + offset)))
          (token (.exec ⟨pcReg B, outcomes (base + offset) i⟩
            (macroCode B (base + offset) i))) ∈ compileAt B base P
  | _, [], _, _, h => by simp at h
  | base, head :: rest, 0, i, h => by
      simp at h
      subst head
      simp [compileAt, instrRules]
  | base, head :: rest, offset + 1, i, h => by
      change rest[offset]? = some i at h
      apply List.mem_append_right (instrRules B base head)
      have hm := control_rule_mem_compileAt B (base + 1) rest offset i h
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hm

/-- The finite generated rulebase.  Repeated entries can arise when control
paths share a return continuation.  They are equal as `Rule` values and have
the same unique occurrence and rewrite result; the determinism theorem is
stated for distinct rule values.  Keeping the list structural also avoids a
quadratic duplicate-removal pass over the deliberately large generated code. -/
def compileRules (P : Cslib.URM.Program) (inputs : List Nat) : List Rule :=
  compileAt (sourceBound P inputs) 0 P

theorem compileRules_shaped (P : Cslib.URM.Program) (inputs : List Nat) :
    ∀ r ∈ compileRules P inputs, RuleShape r := by
  intro r hr
  exact compileAt_shaped (sourceBound P inputs) 0 P r hr

/-- The concrete control rule for an in-range source program counter is in
the complete generated rulebase. -/
theorem control_rule_mem_compileRules (P : Cslib.URM.Program) (inputs : List Nat)
    (k : Nat) (i : Cslib.URM.Instr) (hi : P[k]? = some i) :
    let B := sourceBound P inputs
    rule (token (.control k))
        (token (.exec ⟨pcReg B, outcomes k i⟩ (macroCode B k i))) ∈
      compileRules P inputs := by
  simpa [compileRules] using control_rule_mem_compileAt
    (sourceBound P inputs) 0 P k i hi

/-! ## Counter-state representation -/

/-- Unary runs for counters `0, ..., R-1`, each terminated by `d`. -/
def encodeRegs : Nat → (Nat → Nat) → List Char
  | 0, _ => []
  | R + 1, regs =>
      List.replicate (regs 0) 'x' ++ 'd' :: encodeRegs R (fun r => regs (r + 1))

@[simp] theorem marker_not_mem_encodeRegs (R : Nat) (regs : Nat → Nat) :
    '@' ∉ encodeRegs R regs := by
  induction R generalizing regs with
  | zero => simp [encodeRegs]
  | succ R ih => simp [encodeRegs, ih]

/-- A complete generated state.  `o` counts emitted bytes; `b` and `q` are
the left and right boundaries of the unary register file. -/
def encodeState (R : Nat) (s : CState) (phase : Phase) : List Char :=
  List.replicate s.out 'o' ++ token phase ++
    'b' :: encodeRegs R s.regs ++ ['q']

/-- Every represented control or micro-step state contains exactly one active
marker.  All generated rule left-hand sides are anchored at this marker. -/
theorem encodeState_marker_count (R : Nat) (s : CState) (phase : Phase) :
    (encodeState R s phase).count '@' = 1 := by
  have hr : (encodeRegs R s.regs).count '@' = 0 :=
    List.count_eq_zero.mpr (marker_not_mem_encodeRegs R s.regs)
  have ho : (List.replicate s.out 'o').count '@' = 0 :=
    List.count_eq_zero.mpr (by simp)
  simp [encodeState, List.count_append, hr, ho]

/-- Every rule from a compiled program that actually matches a represented
state carries that state's active phase.  This combines generator-wide rule
shape with the concrete `firstOccurrence?` semantics. -/
theorem compileRules_match_active (P : Cslib.URM.Program) (inputs : List Nat)
    (R : Nat) (s : CState) (phase : Phase) (r : Rule)
    (hr : r ∈ compileRules P inputs) (pos : Nat)
    (hm : firstOccurrence? r.lhs.toList (encodeState R s phase) = some pos) :
    ActiveRule phase r := by
  apply (compileRules_shaped P inputs r hr).active_of_match phase
      (List.replicate s.out 'o') ('b' :: encodeRegs R s.regs ++ ['q'])
  · simp
  · simp [marker_not_mem_encodeRegs]
  · simpa [encodeState, List.append_assoc] using hm

/-- Phase recovery does not depend on the token being at the left boundary
of the register file.  This form is used for scan and return states, where
the unique token sits between two unary-tape fragments. -/
theorem compileRules_match_active_at (P : Cslib.URM.Program) (inputs : List Nat)
    (phase : Phase) (pre post : List Char) (hpre : '@' ∉ pre) (hpost : '@' ∉ post)
    (r : Rule) (hr : r ∈ compileRules P inputs) (pos : Nat)
    (hm : firstOccurrence? r.lhs.toList (pre ++ token phase ++ post) = some pos) :
    ActiveRule phase r := by
  exact (compileRules_shaped P inputs r hr).active_of_match
    phase pre post hpre hpost pos hm

/-- A successful deterministic rule selection records a member of the rule
list and that rule's concrete leftmost occurrence. -/
theorem firstMatch_some : ∀ {rules : List Rule} {state : List Char}
    {pos : Nat} {r : Rule}, firstMatch rules state = some (pos, r) →
      r ∈ rules ∧ firstOccurrence? r.lhs.toList state = some pos
  | [], _, _, _, h => by simp [firstMatch] at h
  | a :: rules, state, pos, r, h => by
      simp only [firstMatch] at h
      split at h
      next p hp =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hpos, hr⟩ := h
        subst p
        subst a
        exact ⟨List.mem_cons_self, hp⟩
      next hp =>
        obtain ⟨hr, hm⟩ := firstMatch_some h
        exact ⟨List.mem_cons_of_mem a hr, hm⟩

/-- If one listed rule occurs, deterministic selection returns some listed
rule and its concrete leftmost occurrence. -/
theorem firstMatch_exists_of_mem {rules : List Rule} {state : List Char}
    {r : Rule} (hr : r ∈ rules) {pos : Nat}
    (hm : firstOccurrence? r.lhs.toList state = some pos) :
    ∃ pos' r', firstMatch rules state = some (pos', r') := by
  induction rules with
  | nil => simp at hr
  | cons a rules ih =>
      simp only [List.mem_cons] at hr
      simp only [firstMatch]
      split
      next p hp => exact ⟨p, a, rfl⟩
      next hp =>
        rcases hr with rfl | hr
        · exact False.elim (by rw [hm] at hp; simp at hp)
        · exact ih hr

/-- The rule selected by the actual `.first` strategy on a represented state
belongs to its active phase. -/
theorem compileRules_firstMatch_active (P : Cslib.URM.Program) (inputs : List Nat)
    (R : Nat) (s : CState) (phase : Phase) (pos : Nat) (r : Rule)
    (hm : firstMatch (compileRules P inputs) (encodeState R s phase) = some (pos, r)) :
    ActiveRule phase r := by
  obtain ⟨hr, ho⟩ := firstMatch_some hm
  exact compileRules_match_active P inputs R s phase r hr pos ho

/-- Generator-family functionality at the actual deterministic selection.
Every selected non-control rule is a member of the canonical rule list for
the represented phase. A selected control rule is the unique source entry at
that program counter. -/
theorem compileRules_firstMatch_origin (P : Cslib.URM.Program) (inputs : List Nat)
    (R : Nat) (s : CState) (phase : Phase) (pos : Nat) (r : Rule)
    (hm : firstMatch (compileRules P inputs) (encodeState R s phase) = some (pos, r)) :
    r ∈ phaseRules phase ∨
      ∃ k i, phase = .control k ∧ P[k]? = some i ∧
        r = rule (token (.control k))
          (token (.exec ⟨pcReg (sourceBound P inputs), outcomes k i⟩
            (macroCode (sourceBound P inputs) k i))) := by
  have hactive := compileRules_firstMatch_active P inputs R s phase pos r hm
  obtain ⟨hr, _⟩ := firstMatch_some hm
  rcases compileAt_origin (sourceBound P inputs) 0 P r
      (by simpa [compileRules] using hr) with hp | he
  · obtain ⟨q, hq⟩ := hp
    have hqa := phaseRules_active q r hq
    have heq := hactive.phase_unique hqa
    subst q
    exact Or.inl hq
  · obtain ⟨k, i, hi, he⟩ := he
    have hcontrol : ActiveRule (.control k) r := by
      rw [he]
      simpa using (ActiveRule.token (p := Phase.control k)
        (token (.exec ⟨pcReg (sourceBound P inputs), outcomes k i⟩
          (macroCode (sourceBound P inputs) k i))))
    have hphase := hactive.phase_unique hcontrol
    refine Or.inr ⟨k, i, hphase, hi, ?_⟩
    simpa using he

/-- Generator-family functionality for an arbitrary position of the unique
phase token.  This is the cursor-state version of
`compileRules_firstMatch_origin`. -/
theorem compileRules_firstMatch_origin_at (P : Cslib.URM.Program) (inputs : List Nat)
    (phase : Phase) (pre post : List Char) (hpre : '@' ∉ pre) (hpost : '@' ∉ post)
    (pos : Nat) (r : Rule)
    (hm : firstMatch (compileRules P inputs) (pre ++ token phase ++ post) =
      some (pos, r)) :
    r ∈ phaseRules phase ∨
      ∃ k i, phase = .control k ∧ P[k]? = some i ∧
        r = rule (token (.control k))
          (token (.exec ⟨pcReg (sourceBound P inputs), outcomes k i⟩
            (macroCode (sourceBound P inputs) k i))) := by
  obtain ⟨hr, ho⟩ := firstMatch_some hm
  have hactive := compileRules_match_active_at P inputs phase pre post
    hpre hpost r hr pos ho
  rcases compileAt_origin (sourceBound P inputs) 0 P r
      (by simpa [compileRules] using hr) with hp | he
  · obtain ⟨q, hq⟩ := hp
    have hqa := phaseRules_active q r hq
    have heq := hactive.phase_unique hqa
    subst q
    exact Or.inl hq
  · obtain ⟨k, i, hi, he⟩ := he
    have hcontrol : ActiveRule (.control k) r := by
      rw [he]
      simpa using (ActiveRule.token (p := Phase.control k)
        (token (.exec ⟨pcReg (sourceBound P inputs), outcomes k i⟩
          (macroCode (sourceBound P inputs) k i))))
    have hphase := hactive.phase_unique hcontrol
    exact Or.inr ⟨k, i, hphase, hi, by simpa using he⟩

/-- Reduce deterministic selection of a right-looking phase to functionality
of that phase's canonical rule family. -/
theorem firstMatch_eq_phase_right (P : Cslib.URM.Program) (inputs : List Nat)
    (p : Phase) (c : Char) (rep pre post : List Char)
    (hpre : '@' ∉ pre) (hpost : '@' ∉ post) (hc : c ≠ '@')
    (hncontrol : ∀ k, p ≠ .control k)
    (hmem : rule (token p ++ [c]) rep ∈ compileRules P inputs)
    (hfunctional : ∀ r ∈ phaseRules p, ∀ pos,
      firstOccurrence? r.lhs.toList (pre ++ token p ++ c :: post) = some pos →
        r = rule (token p ++ [c]) rep) :
    firstMatch (compileRules P inputs) (pre ++ token p ++ c :: post) =
      some (pre.length, rule (token p ++ [c]) rep) := by
  have heocc : firstOccurrence? (rule (token p ++ [c]) rep).lhs.toList
      (pre ++ token p ++ c :: post) = some pre.length := by
    simp only [rule, str, String.toList_ofList]
    simpa [List.append_assoc] using firstOccurrence_token_right p [c] pre post hpre
  obtain ⟨pos, r, hselect⟩ := firstMatch_exists_of_mem hmem heocc
  obtain ⟨hr, hrocc⟩ := firstMatch_some hselect
  rcases compileRules_firstMatch_origin_at P inputs p pre (c :: post)
      hpre (by
        simp only [List.mem_cons, not_or]
        exact ⟨hc.symm, hpost⟩) pos r hselect with hphase | hcontrol
  · have hre := hfunctional r hphase pos hrocc
    subst r
    have hpos : pos = pre.length := by
      rw [heocc] at hrocc
      exact (Option.some.inj hrocc).symm
    simpa [hpos] using hselect
  · obtain ⟨k, _i, hp, _hi, _hr⟩ := hcontrol
    exact False.elim (hncontrol k hp)

/-- Left-looking counterpart of `firstMatch_eq_phase_right`. -/
theorem firstMatch_eq_phase_left (P : Cslib.URM.Program) (inputs : List Nat)
    (p : Phase) (c : Char) (rep pre post : List Char)
    (hpre : '@' ∉ pre) (hpost : '@' ∉ post) (hc : c ≠ '@')
    (hncontrol : ∀ k, p ≠ .control k)
    (hmem : rule (c :: token p) rep ∈ compileRules P inputs)
    (hfunctional : ∀ r ∈ phaseRules p, ∀ pos,
      firstOccurrence? r.lhs.toList (pre ++ c :: token p ++ post) = some pos →
        r = rule (c :: token p) rep) :
    firstMatch (compileRules P inputs) (pre ++ c :: token p ++ post) =
      some (pre.length, rule (c :: token p) rep) := by
  have heocc : firstOccurrence? (rule (c :: token p) rep).lhs.toList
      (pre ++ c :: token p ++ post) = some pre.length := by
    simp only [rule, str, String.toList_ofList]
    exact firstOccurrence_token_left p c pre post hc hpre
  obtain ⟨pos, r, hselect⟩ := firstMatch_exists_of_mem hmem heocc
  obtain ⟨hr, hrocc⟩ := firstMatch_some hselect
  rcases compileRules_firstMatch_origin_at P inputs p (pre ++ [c]) post
      (by
        simp only [List.mem_append, List.mem_singleton, not_or]
        exact ⟨hpre, hc.symm⟩) hpost pos r
      (by simpa [List.append_assoc] using hselect) with hphase | hcontrol
  · have hre := hfunctional r hphase pos hrocc
    subst r
    have hpos : pos = pre.length := by
      rw [heocc] at hrocc
      exact (Option.some.inj hrocc).symm
    simpa [hpos] using hselect
  · obtain ⟨k, _i, hp, _hi, _hr⟩ := hcontrol
    exact False.elim (hncontrol k hp)

/-- One deterministic rewrite is a composable `Reaches` step. -/
theorem reaches_of_step {rules : List Rule} {s t : MState}
    (h : step ({} : Config) rules s = some t) :
    Reaches (exec ({} : Config) rules) s t := by
  apply Reaches.one
  intro fuel
  simp only [exec]
  rw [h]

/-- Apply a proved-functional right-looking generated phase. -/
theorem reaches_phase_right (P : Cslib.URM.Program) (inputs : List Nat)
    (p : Phase) (c : Char) (rep pre post : List Char) (st : MState)
    (hs : st.str = pre ++ token p ++ c :: post)
    (hpre : '@' ∉ pre) (hpost : '@' ∉ post) (hc : c ≠ '@')
    (hncontrol : ∀ k, p ≠ .control k)
    (hmem : rule (token p ++ [c]) rep ∈ compileRules P inputs)
    (hfunctional : ∀ r ∈ phaseRules p, ∀ pos,
      firstOccurrence? r.lhs.toList (pre ++ token p ++ c :: post) = some pos →
        r = rule (token p ++ [c]) rep) :
    Reaches (exec ({} : Config) (compileRules P inputs)) st
      { st with str := pre ++ rep ++ post } := by
  apply reaches_of_step
  unfold step
  simp only
  rw [hs]
  rw [firstMatch_eq_phase_right P inputs p c rep pre post hpre hpost hc
    hncontrol hmem hfunctional]
  simp only [Option.map_some]
  exact congrArg some (applyAt_rule_right p [c] pre rep post st
    (by simpa [List.append_assoc] using hs))

/-- Apply a proved-functional left-looking generated phase. -/
theorem reaches_phase_left (P : Cslib.URM.Program) (inputs : List Nat)
    (p : Phase) (c : Char) (rep pre post : List Char) (st : MState)
    (hs : st.str = pre ++ c :: token p ++ post)
    (hpre : '@' ∉ pre) (hpost : '@' ∉ post) (hc : c ≠ '@')
    (hncontrol : ∀ k, p ≠ .control k)
    (hmem : rule (c :: token p) rep ∈ compileRules P inputs)
    (hfunctional : ∀ r ∈ phaseRules p, ∀ pos,
      firstOccurrence? r.lhs.toList (pre ++ c :: token p ++ post) = some pos →
        r = rule (c :: token p) rep) :
    Reaches (exec ({} : Config) (compileRules P inputs)) st
      { st with str := pre ++ rep ++ post } := by
  apply reaches_of_step
  unfold step
  simp only
  rw [hs]
  rw [firstMatch_eq_phase_left P inputs p c rep pre post hpre hpost hc
    hncontrol hmem hfunctional]
  simp only [Option.map_some]
  exact congrArg some (applyAt_rule_left p c pre rep post st hs)

/-- A singleton right-looking canonical family is immediately functional. -/
theorem reaches_phase_right_single (P : Cslib.URM.Program) (inputs : List Nat)
    (p : Phase) (c : Char) (rep pre post : List Char) (st : MState)
    (hs : st.str = pre ++ token p ++ c :: post)
    (hpre : '@' ∉ pre) (hpost : '@' ∉ post) (hc : c ≠ '@')
    (hncontrol : ∀ k, p ≠ .control k)
    (hrules : ∀ r, r ∈ phaseRules p ↔ r = rule (token p ++ [c]) rep)
    (hmem : rule (token p ++ [c]) rep ∈ compileRules P inputs) :
    Reaches (exec ({} : Config) (compileRules P inputs)) st
      { st with str := pre ++ rep ++ post } := by
  apply reaches_phase_right P inputs p c rep pre post st hs hpre hpost hc
    hncontrol hmem
  intro r hr _pos _hm
  exact (hrules r).mp hr

/-- Two right-looking rules with different adjacent characters are
functional on a concrete tape cell. -/
theorem reaches_phase_right_pair (P : Cslib.URM.Program) (inputs : List Nat)
    (p : Phase) (c other : Char) (rep otherRep pre post : List Char) (st : MState)
    (hs : st.str = pre ++ token p ++ c :: post)
    (hpre : '@' ∉ pre) (hpost : '@' ∉ post)
    (hc : c ≠ '@') (hne : c ≠ other)
    (hncontrol : ∀ k, p ≠ .control k)
    (hrules : ∀ r, r ∈ phaseRules p ↔
      r = rule (token p ++ [c]) rep ∨
      r = rule (token p ++ [other]) otherRep)
    (hmem : rule (token p ++ [c]) rep ∈ compileRules P inputs) :
    Reaches (exec ({} : Config) (compileRules P inputs)) st
      { st with str := pre ++ rep ++ post } := by
  apply reaches_phase_right P inputs p c rep pre post st hs hpre hpost hc
    hncontrol hmem
  intro r hr pos hm
  have hr := (hrules r).mp hr
  rcases hr with rfl | rfl
  · rfl
  · simp only [rule, str, String.toList_ofList] at hm
    have heq := (token_right_match_cell p c other pre post hpre hpost hc pos hm).1
    exact False.elim (hne heq.symm)

/-- Three left-looking rules distinguished by their preceding character are
functional on a concrete tape cell. -/
theorem reaches_phase_left_triple (P : Cslib.URM.Program) (inputs : List Nat)
    (p : Phase) (c d e : Char) (rep repD repE pre post : List Char) (st : MState)
    (hs : st.str = pre ++ c :: token p ++ post)
    (hpre : '@' ∉ pre) (hpost : '@' ∉ post)
    (hc : c ≠ '@') (hcd : c ≠ d) (hce : c ≠ e)
    (hncontrol : ∀ k, p ≠ .control k)
    (hrules : ∀ r, r ∈ phaseRules p ↔
      r = rule (c :: token p) rep ∨ r = rule (d :: token p) repD ∨
      r = rule (e :: token p) repE)
    (hmem : rule (c :: token p) rep ∈ compileRules P inputs) :
    Reaches (exec ({} : Config) (compileRules P inputs)) st
      { st with str := pre ++ rep ++ post } := by
  apply reaches_phase_left P inputs p c rep pre post st hs hpre hpost hc
    hncontrol hmem
  intro r hr pos hm
  have hr := (hrules r).mp hr
  rcases hr with rfl | rfl | rfl
  · rfl
  · simp only [rule, str, String.toList_ofList] at hm
    have heq := (token_left_match_cell p c d pre post hpre hpost hc pos hm).1
    exact False.elim (hcd heq.symm)
  · simp only [rule, str, String.toList_ofList] at hm
    have heq := (token_left_match_cell p c e pre post hpre hpost hc pos hm).1
    exact False.elim (hce heq.symm)

/-- A left-moving phase crosses any finite word of unary cells and counter
delimiters.  Its three rules are distinguished by the cell they consume, so
the crossing is deterministic whatever the tape holds. -/
theorem reaches_left_across (P : Cslib.URM.Program) (inputs : List Nat)
    (p : Phase) (bRep : List Char) (tape pre post : List Char) (st : MState)
    (hs : st.str = pre ++ tape ++ token p ++ post)
    (hpre : '@' ∉ pre) (hpost : '@' ∉ post)
    (htape : ∀ c ∈ tape, c = 'x' ∨ c = 'd')
    (hncontrol : ∀ k, p ≠ .control k)
    (hrules : ∀ r, r ∈ phaseRules p ↔
      r = rule ('x' :: token p) (token p ++ ['x']) ∨
      r = rule ('d' :: token p) (token p ++ ['d']) ∨
      r = rule ('b' :: token p) bRep)
    (hx : rule ('x' :: token p) (token p ++ ['x']) ∈ compileRules P inputs)
    (hd : rule ('d' :: token p) (token p ++ ['d']) ∈ compileRules P inputs) :
    Reaches (exec ({} : Config) (compileRules P inputs)) st
      { st with str := pre ++ token p ++ tape ++ post } := by
  induction tape generalizing pre st with
  | nil =>
      simp only [List.append_nil]
      have heq : { st with str := pre ++ token p ++ post } = st := by
        cases st
        simp_all [List.append_assoc]
      rw [heq]
      exact Reaches.refl (exec ({} : Config) (compileRules P inputs)) st
  | cons c tape ih =>
      have hc := htape c List.mem_cons_self
      have ht : ∀ a ∈ tape, a = 'x' ∨ a = 'd' :=
        fun a ha => htape a (List.mem_cons_of_mem c ha)
      have hcmark : c ≠ '@' := by rcases hc with rfl | rfl <;> decide
      have htmark : '@' ∉ tape := by
        intro hm
        rcases ht '@' hm with h | h <;> contradiction
      let mid : MState :=
        { st with str := (pre ++ [c]) ++ token p ++ tape ++ post }
      have hfirst : Reaches (exec ({} : Config) (compileRules P inputs)) st mid := by
        apply ih (pre := pre ++ [c]) (st := st)
        · simpa [mid, List.append_assoc] using hs
        · simp only [List.mem_append, List.mem_singleton, not_or]
          exact ⟨hpre, hcmark.symm⟩
        · exact ht
      have hsecond : Reaches (exec ({} : Config) (compileRules P inputs)) mid
          { mid with str := pre ++ token p ++ c :: tape ++ post } := by
        rcases hc with rfl | rfl
        · have hmove := reaches_phase_left_triple P inputs p 'x' 'd' 'b'
            (token p ++ ['x']) (token p ++ ['d']) bRep
            pre (tape ++ post) mid
            (by simp [mid, List.append_assoc]) hpre (by simp [htmark, hpost])
            (by decide) (by decide) (by decide) hncontrol
            (by intro r; rw [hrules r]; try tauto) hx
          simpa [List.append_assoc] using hmove
        · have hmove := reaches_phase_left_triple P inputs p 'd' 'x' 'b'
            (token p ++ ['d']) (token p ++ ['x']) bRep
            pre (tape ++ post) mid
            (by simp [mid, List.append_assoc]) hpre (by simp [htmark, hpost])
            (by decide) (by decide) (by decide) hncontrol
            (by intro r; rw [hrules r]; try tauto) hd
          simpa [List.append_assoc] using hmove
      have htotal := Reaches.trans hfirst hsecond
      simpa [mid, List.append_assoc] using htotal

/-- A complete left scan crosses the unary tape and installs the phase's
boundary replacement immediately before the left boundary. -/
theorem reaches_left_home (P : Cslib.URM.Program) (inputs : List Nat)
    (p : Phase) (bRep : List Char) (tape pre post : List Char) (st : MState)
    (hs : st.str = pre ++ 'b' :: tape ++ token p ++ post)
    (hpre : '@' ∉ pre) (hpost : '@' ∉ post)
    (htape : ∀ c ∈ tape, c = 'x' ∨ c = 'd')
    (hncontrol : ∀ k, p ≠ .control k)
    (hrules : ∀ r, r ∈ phaseRules p ↔
      r = rule ('x' :: token p) (token p ++ ['x']) ∨
      r = rule ('d' :: token p) (token p ++ ['d']) ∨
      r = rule ('b' :: token p) bRep)
    (hx : rule ('x' :: token p) (token p ++ ['x']) ∈ compileRules P inputs)
    (hd : rule ('d' :: token p) (token p ++ ['d']) ∈ compileRules P inputs)
    (hb : rule ('b' :: token p) bRep ∈ compileRules P inputs) :
    Reaches (exec ({} : Config) (compileRules P inputs)) st
      { st with str := pre ++ bRep ++ tape ++ post } := by
  have htmark : '@' ∉ tape := by
    intro hm
    rcases htape '@' hm with h | h <;> contradiction
  let mid : MState :=
    { st with str := (pre ++ ['b']) ++ token p ++ tape ++ post }
  have hcross : Reaches (exec ({} : Config) (compileRules P inputs)) st mid := by
    apply reaches_left_across P inputs p bRep tape (pre ++ ['b']) post st
    · simpa [mid, List.append_assoc] using hs
    · simp only [List.mem_append, List.mem_singleton, not_or]
      exact ⟨hpre, by decide⟩
    · exact hpost
    · exact htape
    · exact hncontrol
    · exact hrules
    · exact hx
    · exact hd
  have hboundary := reaches_phase_left_triple P inputs p 'b' 'x' 'd'
    bRep (token p ++ ['x']) (token p ++ ['d'])
    pre (tape ++ post) mid
    (by simp [mid, List.append_assoc]) hpre (by simp [htmark, hpost])
    (by decide) (by decide) (by decide) hncontrol
    (by intro r; rw [hrules r]; try tauto) hb
  have htotal := Reaches.trans hcross hboundary
  simpa [mid, List.append_assoc] using htotal

/-- A return token moves left across any finite word of unary cells and
counter delimiters. -/
theorem reaches_back_across (P : Cslib.URM.Program) (inputs : List Nat)
    (done : Done) (next : Code) (tape pre post : List Char) (st : MState)
    (hs : st.str = pre ++ tape ++ token (.back done next) ++ post)
    (hpre : '@' ∉ pre) (hpost : '@' ∉ post)
    (htape : ∀ c ∈ tape, c = 'x' ∨ c = 'd')
    (hx : rule ('x' :: token (.back done next))
        (token (.back done next) ++ ['x']) ∈ compileRules P inputs)
    (hd : rule ('d' :: token (.back done next))
        (token (.back done next) ++ ['d']) ∈ compileRules P inputs) :
    Reaches (exec ({} : Config) (compileRules P inputs)) st
      { st with str := pre ++ token (.back done next) ++ tape ++ post } :=
  reaches_left_across P inputs (.back done next)
    (token (.exec done next) ++ ['b']) tape pre post st hs hpre hpost htape
    (by intro k h; cases h) (by intro r; simp [phaseRules, backRules]) hx hd

/-- A complete return scan crosses the unary prefix and reinstalls the next
structured-code continuation immediately before the left boundary. -/
theorem reaches_back_home (P : Cslib.URM.Program) (inputs : List Nat)
    (done : Done) (next : Code) (tape pre post : List Char) (st : MState)
    (hs : st.str = pre ++ 'b' :: tape ++ token (.back done next) ++ post)
    (hpre : '@' ∉ pre) (hpost : '@' ∉ post)
    (htape : ∀ c ∈ tape, c = 'x' ∨ c = 'd')
    (hx : rule ('x' :: token (.back done next))
        (token (.back done next) ++ ['x']) ∈ compileRules P inputs)
    (hd : rule ('d' :: token (.back done next))
        (token (.back done next) ++ ['d']) ∈ compileRules P inputs)
    (hb : rule ('b' :: token (.back done next))
        (token (.exec done next) ++ ['b']) ∈ compileRules P inputs) :
    Reaches (exec ({} : Config) (compileRules P inputs)) st
      { st with str := pre ++ token (.exec done next) ++ 'b' :: tape ++ post } := by
  have h := reaches_left_home P inputs (.back done next)
    (token (.exec done next) ++ ['b']) tape pre post st hs hpre hpost htape
    (by intro k h; cases h) (by intro r; simp [phaseRules, backRules]) hx hd hb
  simpa [List.append_assoc] using h
/-- A right-moving phase crosses a unary run while retaining the same phase
token. -/
theorem reaches_across_xs (P : Cslib.URM.Program) (inputs : List Nat)
    (p : Phase) (dRep pre post : List Char) (n : Nat) (st : MState)
    (hs : st.str = pre ++ token p ++ List.replicate n 'x' ++ post)
    (hpre : '@' ∉ pre) (hpost : '@' ∉ post)
    (hncontrol : ∀ k, p ≠ .control k)
    (hrules : ∀ r, r ∈ phaseRules p ↔
      r = rule (token p ++ ['x']) ('x' :: token p) ∨
      r = rule (token p ++ ['d']) dRep)
    (hx : rule (token p ++ ['x']) ('x' :: token p) ∈ compileRules P inputs) :
    Reaches (exec ({} : Config) (compileRules P inputs)) st
      { st with str := pre ++ List.replicate n 'x' ++ token p ++ post } := by
  induction n generalizing pre st with
  | zero =>
      simp only [List.replicate_zero, List.append_nil] at hs ⊢
      have heq : { st with str := pre ++ token p ++ post } = st := by
        cases st
        simp_all [List.append_assoc]
      rw [heq]
      exact Reaches.refl (exec ({} : Config) (compileRules P inputs)) st
  | succ n ih =>
      let mid : MState :=
        { st with str := (pre ++ ['x']) ++ token p ++ List.replicate n 'x' ++ post }
      have hstep : Reaches (exec ({} : Config) (compileRules P inputs)) st mid := by
        have h := reaches_phase_right_pair P inputs p 'x' 'd'
          ('x' :: token p) dRep pre (List.replicate n 'x' ++ post) st
          (by simpa [List.replicate_succ, List.append_assoc] using hs)
          hpre (by simp [hpost]) (by decide) (by decide) hncontrol hrules hx
        simpa [mid, List.append_assoc] using h
      have hrest : Reaches (exec ({} : Config) (compileRules P inputs)) mid
          { mid with str := (pre ++ ['x']) ++ List.replicate n 'x' ++ token p ++ post } := by
        apply ih (pre := pre ++ ['x']) (st := mid)
        · simp [mid, List.append_assoc]
        · simp [hpre]
      have htotal := Reaches.trans hstep hrest
      simpa [mid, List.replicate_succ, List.append_assoc] using htotal

/-- Every in-range increment scan has its unary-cell rule in the generated
increment family. -/
theorem incRules_scan_x_mem (done : Done) (next : Code) (target current : Nat)
    (hcurrent : current ≤ target) :
    rule (token (.scanInc done next target current) ++ ['x'])
        ('x' :: token (.scanInc done next target current)) ∈
      incRules done next target := by
  simp only [incRules, List.mem_append, List.mem_flatMap]
  left
  refine ⟨current, List.mem_range.mpr (by omega), ?_⟩
  split <;> simp

/-- A non-target increment scan advances across its delimiter. -/
theorem incRules_scan_d_mem (done : Done) (next : Code) (target current : Nat)
    (hcurrent : current < target) :
    rule (token (.scanInc done next target current) ++ ['d'])
        ('d' :: token (.scanInc done next target (current + 1))) ∈
      incRules done next target := by
  simp only [incRules, List.mem_append, List.mem_flatMap]
  left
  refine ⟨current, List.mem_range.mpr (by omega), ?_⟩
  simp [hcurrent]

/-- The target delimiter rule appends one unary cell and starts the return. -/
theorem incRules_finish_mem (done : Done) (next : Code) (target : Nat) :
    rule (token (.scanInc done next target target) ++ ['d'])
        ('x' :: 'd' :: token (.back done next)) ∈ incRules done next target := by
  simp only [incRules, List.mem_append, List.mem_flatMap]
  left
  refine ⟨target, List.mem_range.mpr (by omega), ?_⟩
  simp

/-- The three common return rules occur in every increment family. -/
theorem incRules_back_mem (done : Done) (next : Code) (target : Nat) :
    (∀ c ∈ ['x', 'd'],
      rule (c :: token (.back done next)) (token (.back done next) ++ [c]) ∈
        incRules done next target) ∧
    rule ('b' :: token (.back done next)) (token (.exec done next) ++ ['b']) ∈
      incRules done next target := by
  constructor
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> simp [incRules, backRules]
  · simp [incRules, backRules]

/-- An increment scan crosses any initial block of complete counters,
advancing the phase's counter index at each delimiter. -/
theorem reaches_scanInc_prefix (P : Cslib.URM.Program) (inputs : List Nat)
    (done : Done) (next : Code) (target current n : Nat)
    (regs : Nat → Nat) (pre post : List Char) (st : MState)
    (hbound : current + n ≤ target)
    (hs : st.str = pre ++ token (.scanInc done next target current) ++
      encodeRegs n regs ++ post)
    (hpre : '@' ∉ pre) (hpost : '@' ∉ post)
    (hx : ∀ j, j ≤ target →
      rule (token (.scanInc done next target j) ++ ['x'])
        ('x' :: token (.scanInc done next target j)) ∈ compileRules P inputs)
    (hd : ∀ j, j < target →
      rule (token (.scanInc done next target j) ++ ['d'])
        ('d' :: token (.scanInc done next target (j + 1))) ∈ compileRules P inputs) :
    Reaches (exec ({} : Config) (compileRules P inputs)) st
      { st with str := pre ++ encodeRegs n regs ++
        (token (.scanInc done next target (current + n)) ++ post) } := by
  induction n generalizing current regs pre st with
  | zero =>
      simp only [encodeRegs, Nat.add_zero, List.append_nil] at hs ⊢
      have heq : { st with str := pre ++ (token (.scanInc done next target current) ++ post) } =
          st := by
        cases st
        simp_all [List.append_assoc]
      rw [heq]
      exact Reaches.refl (exec ({} : Config) (compileRules P inputs)) st
  | succ n ih =>
      have hcur : current < target := by omega
      let p := Phase.scanInc done next target current
      let p' := Phase.scanInc done next target (current + 1)
      let tail := encodeRegs n (fun r => regs (r + 1)) ++ post
      let mid₁ : MState :=
        { st with str := pre ++ List.replicate (regs 0) 'x' ++ token p ++ 'd' :: tail }
      have hacross : Reaches (exec ({} : Config) (compileRules P inputs)) st mid₁ := by
        have h := reaches_across_xs P inputs p
          ('d' :: token p') pre ('d' :: tail) (regs 0) st
          (by simpa [p, tail, encodeRegs, List.append_assoc] using hs)
          hpre (by simp [tail, hpost, marker_not_mem_encodeRegs])
          (by intro k; simp [p])
          (by
            intro r
            simp [p, p', phaseRules, hcur])
          (by simpa [p] using hx current (by omega))
        simpa [mid₁, List.append_assoc] using h
      let mid₂ : MState :=
        { mid₁ with str := pre ++ List.replicate (regs 0) 'x' ++ 'd' :: token p' ++ tail }
      have hdelim : Reaches (exec ({} : Config) (compileRules P inputs)) mid₁ mid₂ := by
        have h := reaches_phase_right_pair P inputs p 'd' 'x'
          ('d' :: token p') ('x' :: token p)
          (pre ++ List.replicate (regs 0) 'x') tail mid₁
          (by simp [mid₁, List.append_assoc])
          (by simp [hpre])
          (by simp [tail, hpost, marker_not_mem_encodeRegs])
          (by decide) (by decide) (by intro k; simp [p])
          (by
            intro r
            simp [p, p', phaseRules, hcur]
            tauto)
          (by simpa [p, p'] using hd current hcur)
        simpa [mid₂, List.append_assoc] using h
      have hrest := ih (current := current + 1) (regs := fun r => regs (r + 1))
        (pre := pre ++ List.replicate (regs 0) 'x' ++ ['d']) (st := mid₂)
        (by omega)
        (by simp [mid₂, p', tail, List.append_assoc])
        (by simp [hpre])
      have htotal := Reaches.trans hacross (Reaches.trans hdelim hrest)
      simpa [mid₁, mid₂, p, p', tail, encodeRegs, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htotal

/-- Splitting the counter bound splits the unary register tape at the same
counter index. -/
theorem encodeRegs_add (a b : Nat) (regs : Nat → Nat) :
    encodeRegs (a + b) regs = encodeRegs a regs ++
      encodeRegs b (fun r => regs (a + r)) := by
  induction a generalizing regs with
  | zero => simp [encodeRegs]
  | succ a ih =>
      simp only [Nat.succ_add, encodeRegs]
      rw [ih]
      simp [List.append_assoc, Nat.add_assoc]

/-- Register-tape encoding depends only on the bounded prefix of the register
function. -/
theorem encodeRegs_congr (R : Nat) {f g : Nat → Nat}
    (h : ∀ r, r < R → f r = g r) : encodeRegs R f = encodeRegs R g := by
  induction R generalizing f g with
  | zero => rfl
  | succ R ih =>
      simp only [encodeRegs]
      rw [h 0 (by omega)]
      apply congrArg (List.replicate (g 0) 'x' ++ 'd' :: ·)
      apply ih
      intro r hr
      exact h (r + 1) (by omega)

/-- Incrementing a bounded counter inserts exactly one `x` in its unary run. -/
theorem encodeRegs_up (R target : Nat) (s : CState) (hbound : target < R) :
    encodeRegs R (s.up target).regs =
      encodeRegs target s.regs ++ List.replicate (s.regs target) 'x' ++
        'x' :: 'd' :: encodeRegs (R - (target + 1))
          (fun r => s.regs (target + 1 + r)) := by
  have hR : R = target + (1 + (R - (target + 1))) := by omega
  conv_lhs => rw [hR, encodeRegs_add target]
  rw [Nat.one_add]
  simp only [encodeRegs]
  have hprefix : encodeRegs target (s.up target).regs = encodeRegs target s.regs := by
    apply encodeRegs_congr
    intro r hr
    exact CState.up_regs_of_ne s (by omega)
  rw [hprefix]
  simp only [Nat.add_zero]
  rw [CState.up_regs_self]
  have hsuffix : encodeRegs (R - (target + 1))
      (fun r => (s.up target).regs (target + (r + 1))) =
      encodeRegs (R - (target + 1)) (fun r => s.regs (target + 1 + r)) := by
    apply encodeRegs_congr
    intro r _hr
    rw [CState.up_regs_of_ne s (by omega)]
    congr 1
    omega
  rw [hsuffix]
  simp [List.replicate_succ', List.append_assoc]

/-- The original tape has the corresponding split without the inserted cell. -/
theorem encodeRegs_split_at (R target : Nat) (regs : Nat → Nat)
    (hbound : target < R) :
    encodeRegs R regs = encodeRegs target regs ++
      List.replicate (regs target) 'x' ++ 'd' ::
        encodeRegs (R - (target + 1)) (fun r => regs (target + 1 + r)) := by
  have hR : R = target + (1 + (R - (target + 1))) := by omega
  conv_lhs => rw [hR, encodeRegs_add target]
  rw [Nat.one_add]
  simp [encodeRegs, List.append_assoc, Nat.add_comm, Nat.add_left_comm]

theorem encodeRegs_cells (R : Nat) (regs : Nat → Nat) :
    ∀ c ∈ encodeRegs R regs, c = 'x' ∨ c = 'd' := by
  induction R generalizing regs with
  | zero => simp [encodeRegs]
  | succ R ih =>
      intro c hc
      simp only [encodeRegs, List.mem_append, List.mem_replicate, List.mem_cons] at hc
      rcases hc with ⟨_, rfl⟩ | rfl | hc
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact ih (fun r => regs (r + 1)) c hc

/-- One complete structured-counter increment is simulated by the actual
deterministic Thue interpreter, from one home-position encoding to the next. -/
theorem reaches_inc (P : Cslib.URM.Program) (inputs : List Nat)
    (done : Done) (next : Code) (R target : Nat) (s : CState)
    (pre post : List Char) (st : MState) (htarget : target < R)
    (hs : st.str = pre ++ token (.exec done (.inc target :: next)) ++
      'b' :: encodeRegs R s.regs ++ post)
    (hpre : '@' ∉ pre) (hpost : '@' ∉ post)
    (hstart : rule (token (.exec done (.inc target :: next)) ++ ['b'])
        ('b' :: token (.scanInc done next target 0)) ∈ compileRules P inputs)
    (hscanX : ∀ j, j ≤ target →
      rule (token (.scanInc done next target j) ++ ['x'])
        ('x' :: token (.scanInc done next target j)) ∈ compileRules P inputs)
    (hscanD : ∀ j, j < target →
      rule (token (.scanInc done next target j) ++ ['d'])
        ('d' :: token (.scanInc done next target (j + 1))) ∈ compileRules P inputs)
    (hfinish : rule (token (.scanInc done next target target) ++ ['d'])
        ('x' :: 'd' :: token (.back done next)) ∈ compileRules P inputs)
    (hbackX : rule ('x' :: token (.back done next))
        (token (.back done next) ++ ['x']) ∈ compileRules P inputs)
    (hbackD : rule ('d' :: token (.back done next))
        (token (.back done next) ++ ['d']) ∈ compileRules P inputs)
    (hbackB : rule ('b' :: token (.back done next))
        (token (.exec done next) ++ ['b']) ∈ compileRules P inputs) :
    Reaches (exec ({} : Config) (compileRules P inputs)) st
      { st with str := pre ++ token (.exec done next) ++
        'b' :: encodeRegs R (s.up target).regs ++ post } := by
  let suffix := encodeRegs (R - (target + 1))
    (fun r => s.regs (target + 1 + r))
  let p := Phase.scanInc done next target target
  let mid₀ : MState :=
    { st with str := pre ++ 'b' :: token (.scanInc done next target 0) ++
      encodeRegs R s.regs ++ post }
  have hentry : Reaches (exec ({} : Config) (compileRules P inputs)) st mid₀ := by
    have h := reaches_phase_right_single P inputs
      (.exec done (.inc target :: next)) 'b'
      ('b' :: token (.scanInc done next target 0))
      pre (encodeRegs R s.regs ++ post) st
      (by simpa [List.append_assoc] using hs) hpre
      (by simp [marker_not_mem_encodeRegs, hpost]) (by decide)
      (by intro k h; cases h)
      (by intro r; simp [phaseRules]) hstart
    simpa [mid₀, List.append_assoc] using h
  let targetTail := List.replicate (s.regs target) 'x' ++ 'd' :: suffix ++ post
  let mid₁ : MState :=
    { mid₀ with str := pre ++ 'b' :: encodeRegs target s.regs ++
      (token p ++ targetTail) }
  have hscan : Reaches (exec ({} : Config) (compileRules P inputs)) mid₀ mid₁ := by
    have h := reaches_scanInc_prefix P inputs done next target 0 target s.regs
      (pre ++ ['b']) targetTail mid₀ (by omega)
      (by
        simp only [mid₀]
        rw [show encodeRegs R s.regs = encodeRegs target s.regs ++
          List.replicate (s.regs target) 'x' ++ 'd' :: suffix from by
            simpa [suffix] using encodeRegs_split_at R target s.regs htarget]
        simp [targetTail, List.append_assoc])
      (by simp [hpre])
      (by simp [targetTail, suffix, hpost, marker_not_mem_encodeRegs])
      hscanX hscanD
    simpa [mid₁, p, List.append_assoc] using h
  let mid₂ : MState :=
    { mid₁ with str := pre ++ 'b' :: encodeRegs target s.regs ++
      List.replicate (s.regs target) 'x' ++ token p ++ 'd' :: suffix ++ post }
  have htargetRun : Reaches (exec ({} : Config) (compileRules P inputs)) mid₁ mid₂ := by
    have h := reaches_across_xs P inputs p
      ('x' :: 'd' :: token (.back done next))
      (pre ++ 'b' :: encodeRegs target s.regs) ('d' :: suffix ++ post)
      (s.regs target) mid₁
      (by simp [mid₁, targetTail, List.append_assoc])
      (by simp [hpre, marker_not_mem_encodeRegs])
      (by simp [suffix, hpost, marker_not_mem_encodeRegs])
      (by intro k; simp [p])
      (by intro r; simp [p, phaseRules])
      (hscanX target (by omega))
    simpa [mid₂, List.append_assoc] using h
  let tape := encodeRegs target s.regs ++
    List.replicate (s.regs target) 'x' ++ ['x', 'd']
  let mid₃ : MState :=
    { mid₂ with str := pre ++ 'b' :: tape ++ token (.back done next) ++ suffix ++ post }
  have hdo : Reaches (exec ({} : Config) (compileRules P inputs)) mid₂ mid₃ := by
    have h := reaches_phase_right_pair P inputs p 'd' 'x'
      ('x' :: 'd' :: token (.back done next)) ('x' :: token p)
      (pre ++ 'b' :: encodeRegs target s.regs ++
        List.replicate (s.regs target) 'x') (suffix ++ post) mid₂
      (by simp [mid₂, List.append_assoc])
      (by simp [hpre, marker_not_mem_encodeRegs])
      (by simp [suffix, hpost, marker_not_mem_encodeRegs])
      (by decide) (by decide) (by intro k; simp [p])
      (by
        intro r
        simp [p, phaseRules]
        tauto)
      hfinish
    simpa [mid₃, tape, List.append_assoc] using h
  have htape : ∀ c ∈ tape, c = 'x' ∨ c = 'd' := by
    intro c hc
    simp only [tape, List.mem_append, List.mem_cons, List.mem_replicate,
      List.not_mem_nil, or_false] at hc
    rcases hc with (hc | ⟨_, rfl⟩) | rfl | rfl
    · exact encodeRegs_cells target s.regs c hc
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hreturn := reaches_back_home P inputs done next tape pre (suffix ++ post) mid₃
    (by simp [mid₃, List.append_assoc]) hpre
    (by simp [suffix, hpost, marker_not_mem_encodeRegs]) htape
    hbackX hbackD hbackB
  have htotal := Reaches.trans hentry
    (Reaches.trans hscan (Reaches.trans htargetRun (Reaches.trans hdo hreturn)))
  rw [encodeRegs_up R target s htarget]
  simpa [mid₀, mid₁, mid₂, mid₃, p, targetTail, tape, suffix,
    List.append_assoc] using htotal

/-! ## Functional selection for uniform rule families

Every canonical family except `back` and `backPC` reads the cell to the
right of its token, and those two read the cell to its left.  These two
lemmas turn "the family is uniform in that sense" into the concrete
functionality hypothesis `reaches_phase_right` and `reaches_phase_left`
ask for, so a macro proof only has to name the rule it wants. -/

/-- A phase whose canonical rules all read the cell to the right of the
token is functional at a concrete cell: the adjacent character selects the
rule, and the phase fixes its replacement. -/
theorem reaches_phase_right_cell (P : Cslib.URM.Program) (inputs : List Nat)
    (p : Phase) (c : Char) (rep pre post : List Char) (st : MState)
    (hs : st.str = pre ++ token p ++ c :: post)
    (hpre : '@' ∉ pre) (hpost : '@' ∉ post) (hc : c ≠ '@')
    (hncontrol : ∀ k, p ≠ .control k)
    (hforms : ∀ r ∈ phaseRules p, ∃ c' rep', r = rule (token p ++ [c']) rep')
    (hpick : ∀ rep', rule (token p ++ [c]) rep' ∈ phaseRules p → rep' = rep)
    (hmem : rule (token p ++ [c]) rep ∈ compileRules P inputs) :
    Reaches (exec ({} : Config) (compileRules P inputs)) st
      { st with str := pre ++ rep ++ post } := by
  apply reaches_phase_right P inputs p c rep pre post st hs hpre hpost hc
    hncontrol hmem
  intro r hr pos hm
  obtain ⟨c', rep', rfl⟩ := hforms r hr
  simp only [rule, str, String.toList_ofList] at hm
  obtain ⟨hcell, -⟩ := token_right_match_cell p c c' pre post hpre hpost hc pos hm
  subst hcell
  rw [hpick rep' hr]

/-- The mirror image for the two families that read the cell to the left. -/
theorem reaches_phase_left_cell (P : Cslib.URM.Program) (inputs : List Nat)
    (p : Phase) (c : Char) (rep pre post : List Char) (st : MState)
    (hs : st.str = pre ++ c :: token p ++ post)
    (hpre : '@' ∉ pre) (hpost : '@' ∉ post) (hc : c ≠ '@')
    (hncontrol : ∀ k, p ≠ .control k)
    (hforms : ∀ r ∈ phaseRules p, ∃ c' rep', r = rule (c' :: token p) rep')
    (hpick : ∀ rep', rule (c :: token p) rep' ∈ phaseRules p → rep' = rep)
    (hmem : rule (c :: token p) rep ∈ compileRules P inputs) :
    Reaches (exec ({} : Config) (compileRules P inputs)) st
      { st with str := pre ++ rep ++ post } := by
  apply reaches_phase_left P inputs p c rep pre post st hs hpre hpost hc
    hncontrol hmem
  intro r hr pos hm
  obtain ⟨c', rep', rfl⟩ := hforms r hr
  simp only [rule, str, String.toList_ofList] at hm
  obtain ⟨hcell, -⟩ := token_left_match_cell p c c' pre post hpre hpost hc pos hm
  subst hcell
  rw [hpick rep' hr]

/-! ## The decrement macro -/

/-- Decrementing a nonzero bounded counter removes exactly one `x`. -/
theorem encodeRegs_down (R target : Nat) (s : CState) (hbound : target < R) :
    encodeRegs R (s.down target).regs =
      encodeRegs target s.regs ++ List.replicate (s.regs target - 1) 'x' ++
        'd' :: encodeRegs (R - (target + 1))
          (fun r => s.regs (target + 1 + r)) := by
  rw [encodeRegs_split_at R target (s.down target).regs hbound]
  have hprefix : encodeRegs target (s.down target).regs = encodeRegs target s.regs :=
    encodeRegs_congr target (fun r hr => CState.down_regs_of_ne s (by omega))
  have hsuffix : encodeRegs (R - (target + 1))
      (fun r => (s.down target).regs (target + 1 + r)) =
      encodeRegs (R - (target + 1)) (fun r => s.regs (target + 1 + r)) :=
    encodeRegs_congr _ (fun r _hr => CState.down_regs_of_ne s (by omega))
  rw [hprefix, hsuffix, CState.down_regs_self]

/-- A non-target decrement scan crosses its unary run. -/
theorem decRules_scan_x_mem (done : Done) (next : Code) (target current : Nat)
    (hcurrent : current < target) :
    rule (token (.scanDec done next target current) ++ ['x'])
        ('x' :: token (.scanDec done next target current)) ∈
      decRules done next target := by
  simp only [decRules, List.mem_append, List.mem_flatMap]
  left
  refine ⟨current, List.mem_range.mpr (by omega), ?_⟩
  simp [hcurrent]

/-- A non-target decrement scan advances across its delimiter. -/
theorem decRules_scan_d_mem (done : Done) (next : Code) (target current : Nat)
    (hcurrent : current < target) :
    rule (token (.scanDec done next target current) ++ ['d'])
        ('d' :: token (.scanDec done next target (current + 1))) ∈
      decRules done next target := by
  simp only [decRules, List.mem_append, List.mem_flatMap]
  left
  refine ⟨current, List.mem_range.mpr (by omega), ?_⟩
  simp [hcurrent]

/-- At the target counter the decrement family consumes one unary cell and
starts the return scan.  There is no delimiter rule, so a decrement of an
empty counter has no successor at all, which is exactly the discipline
`Ev.dec` imposes on the source. -/
theorem decRules_take_mem (done : Done) (next : Code) (target : Nat) :
    rule (token (.scanDec done next target target) ++ ['x'])
        (token (.back done next)) ∈ decRules done next target := by
  simp only [decRules, List.mem_append, List.mem_flatMap]
  left
  refine ⟨target, List.mem_range.mpr (by omega), ?_⟩
  simp

/-- The three common return rules occur in every decrement family. -/
theorem decRules_back_mem (done : Done) (next : Code) (target : Nat) :
    (∀ c ∈ ['x', 'd'],
      rule (c :: token (.back done next)) (token (.back done next) ++ [c]) ∈
        decRules done next target) ∧
    rule ('b' :: token (.back done next)) (token (.exec done next) ++ ['b']) ∈
      decRules done next target := by
  constructor
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> simp [decRules, backRules]
  · simp [decRules, backRules]

/-- A decrement scan crosses any initial block of complete counters,
advancing the phase's counter index at each delimiter. -/
theorem reaches_scanDec_prefix (P : Cslib.URM.Program) (inputs : List Nat)
    (done : Done) (next : Code) (target current n : Nat)
    (regs : Nat → Nat) (pre post : List Char) (st : MState)
    (hbound : current + n ≤ target)
    (hs : st.str = pre ++ token (.scanDec done next target current) ++
      encodeRegs n regs ++ post)
    (hpre : '@' ∉ pre) (hpost : '@' ∉ post)
    (hx : ∀ j, j < target →
      rule (token (.scanDec done next target j) ++ ['x'])
        ('x' :: token (.scanDec done next target j)) ∈ compileRules P inputs)
    (hd : ∀ j, j < target →
      rule (token (.scanDec done next target j) ++ ['d'])
        ('d' :: token (.scanDec done next target (j + 1))) ∈ compileRules P inputs) :
    Reaches (exec ({} : Config) (compileRules P inputs)) st
      { st with str := pre ++ encodeRegs n regs ++
        (token (.scanDec done next target (current + n)) ++ post) } := by
  induction n generalizing current regs pre st with
  | zero =>
      simp only [encodeRegs, Nat.add_zero, List.append_nil] at hs ⊢
      have heq : { st with str := pre ++ (token (.scanDec done next target current) ++ post) } =
          st := by
        cases st
        simp_all [List.append_assoc]
      rw [heq]
      exact Reaches.refl (exec ({} : Config) (compileRules P inputs)) st
  | succ n ih =>
      have hcur : current < target := by omega
      let p := Phase.scanDec done next target current
      let p' := Phase.scanDec done next target (current + 1)
      let tail := encodeRegs n (fun r => regs (r + 1)) ++ post
      let mid₁ : MState :=
        { st with str := pre ++ List.replicate (regs 0) 'x' ++ token p ++ 'd' :: tail }
      have hacross : Reaches (exec ({} : Config) (compileRules P inputs)) st mid₁ := by
        have h := reaches_across_xs P inputs p
          ('d' :: token p') pre ('d' :: tail) (regs 0) st
          (by simpa [p, tail, encodeRegs, List.append_assoc] using hs)
          hpre (by simp [tail, hpost, marker_not_mem_encodeRegs])
          (by intro k; simp [p])
          (by
            intro r
            simp [p, p', phaseRules, hcur])
          (by simpa [p] using hx current hcur)
        simpa [mid₁, List.append_assoc] using h
      let mid₂ : MState :=
        { mid₁ with str := pre ++ List.replicate (regs 0) 'x' ++ 'd' :: token p' ++ tail }
      have hdelim : Reaches (exec ({} : Config) (compileRules P inputs)) mid₁ mid₂ := by
        have h := reaches_phase_right_pair P inputs p 'd' 'x'
          ('d' :: token p') ('x' :: token p)
          (pre ++ List.replicate (regs 0) 'x') tail mid₁
          (by simp [mid₁, List.append_assoc])
          (by simp [hpre])
          (by simp [tail, hpost, marker_not_mem_encodeRegs])
          (by decide) (by decide) (by intro k; simp [p])
          (by
            intro r
            simp [p, p', phaseRules, hcur]
            tauto)
          (by simpa [p, p'] using hd current hcur)
        simpa [mid₂, List.append_assoc] using h
      have hrest := ih (current := current + 1) (regs := fun r => regs (r + 1))
        (pre := pre ++ List.replicate (regs 0) 'x' ++ ['d']) (st := mid₂)
        (by omega)
        (by simp [mid₂, p', tail, List.append_assoc])
        (by simp [hpre])
      have htotal := Reaches.trans hacross (Reaches.trans hdelim hrest)
      simpa [mid₁, mid₂, p, p', tail, encodeRegs, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htotal

/-- One complete structured-counter decrement is simulated by the actual
deterministic Thue interpreter, from one home-position encoding to the
next.  The source counter must be nonzero, which is what `Ev.dec` supplies. -/
theorem reaches_dec (P : Cslib.URM.Program) (inputs : List Nat)
    (done : Done) (next : Code) (R target : Nat) (s : CState)
    (pre post : List Char) (st : MState) (htarget : target < R)
    (hnz : s.regs target ≠ 0)
    (hs : st.str = pre ++ token (.exec done (.dec target :: next)) ++
      'b' :: encodeRegs R s.regs ++ post)
    (hpre : '@' ∉ pre) (hpost : '@' ∉ post)
    (hstart : rule (token (.exec done (.dec target :: next)) ++ ['b'])
        ('b' :: token (.scanDec done next target 0)) ∈ compileRules P inputs)
    (hscanX : ∀ j, j < target →
      rule (token (.scanDec done next target j) ++ ['x'])
        ('x' :: token (.scanDec done next target j)) ∈ compileRules P inputs)
    (hscanD : ∀ j, j < target →
      rule (token (.scanDec done next target j) ++ ['d'])
        ('d' :: token (.scanDec done next target (j + 1))) ∈ compileRules P inputs)
    (hfinish : rule (token (.scanDec done next target target) ++ ['x'])
        (token (.back done next)) ∈ compileRules P inputs)
    (hbackX : rule ('x' :: token (.back done next))
        (token (.back done next) ++ ['x']) ∈ compileRules P inputs)
    (hbackD : rule ('d' :: token (.back done next))
        (token (.back done next) ++ ['d']) ∈ compileRules P inputs)
    (hbackB : rule ('b' :: token (.back done next))
        (token (.exec done next) ++ ['b']) ∈ compileRules P inputs) :
    Reaches (exec ({} : Config) (compileRules P inputs)) st
      { st with str := pre ++ token (.exec done next) ++
        'b' :: encodeRegs R (s.down target).regs ++ post } := by
  let suffix := encodeRegs (R - (target + 1))
    (fun r => s.regs (target + 1 + r))
  let p := Phase.scanDec done next target target
  let rest := List.replicate (s.regs target - 1) 'x' ++ 'd' :: suffix ++ post
  let mid₀ : MState :=
    { st with str := pre ++ 'b' :: token (.scanDec done next target 0) ++
      encodeRegs R s.regs ++ post }
  have hentry : Reaches (exec ({} : Config) (compileRules P inputs)) st mid₀ := by
    have h := reaches_phase_right_single P inputs
      (.exec done (.dec target :: next)) 'b'
      ('b' :: token (.scanDec done next target 0))
      pre (encodeRegs R s.regs ++ post) st
      (by simpa [List.append_assoc] using hs) hpre
      (by simp [marker_not_mem_encodeRegs, hpost]) (by decide)
      (by intro k h; cases h)
      (by intro r; simp [phaseRules]) hstart
    simpa [mid₀, List.append_assoc] using h
  let targetTail := List.replicate (s.regs target) 'x' ++ 'd' :: suffix ++ post
  let mid₁ : MState :=
    { mid₀ with str := pre ++ 'b' :: encodeRegs target s.regs ++
      (token p ++ targetTail) }
  have hscan : Reaches (exec ({} : Config) (compileRules P inputs)) mid₀ mid₁ := by
    have h := reaches_scanDec_prefix P inputs done next target 0 target s.regs
      (pre ++ ['b']) targetTail mid₀ (by omega)
      (by
        simp only [mid₀]
        rw [show encodeRegs R s.regs = encodeRegs target s.regs ++
          List.replicate (s.regs target) 'x' ++ 'd' :: suffix from by
            simpa [suffix] using encodeRegs_split_at R target s.regs htarget]
        simp [targetTail, List.append_assoc])
      (by simp [hpre])
      (by simp [targetTail, suffix, hpost, marker_not_mem_encodeRegs])
      hscanX hscanD
    simpa [mid₁, p, List.append_assoc] using h
  have hcell : List.replicate (s.regs target) 'x' =
      'x' :: List.replicate (s.regs target - 1) 'x' := by
    obtain ⟨m, hm⟩ : ∃ m, s.regs target = m + 1 := ⟨s.regs target - 1, by omega⟩
    simp [hm, List.replicate_succ]
  let mid₂ : MState :=
    { mid₁ with
      str := pre ++ 'b' :: encodeRegs target s.regs ++
        (token (.back done next) ++ rest) }
  have hdo : Reaches (exec ({} : Config) (compileRules P inputs)) mid₁ mid₂ := by
    have h := reaches_phase_right_single P inputs p 'x'
      (token (.back done next))
      (pre ++ 'b' :: encodeRegs target s.regs) rest mid₁
      (by simp [mid₁, targetTail, rest, hcell, List.append_assoc])
      (by simp [hpre, marker_not_mem_encodeRegs])
      (by simp [rest, suffix, hpost, marker_not_mem_encodeRegs])
      (by decide) (by intro k; simp [p])
      (by intro r; simp [p, phaseRules])
      hfinish
    simpa [mid₂, List.append_assoc] using h
  have htape : ∀ c ∈ encodeRegs target s.regs, c = 'x' ∨ c = 'd' :=
    encodeRegs_cells target s.regs
  have hreturn := reaches_back_home P inputs done next
    (encodeRegs target s.regs) pre rest mid₂
    (by simp [mid₂, List.append_assoc]) hpre
    (by simp [rest, suffix, hpost, marker_not_mem_encodeRegs]) htape
    hbackX hbackD hbackB
  have htotal := Reaches.trans hentry
    (Reaches.trans hscan (Reaches.trans hdo hreturn))
  rw [encodeRegs_down R target s htarget]
  simpa [mid₀, mid₁, mid₂, p, targetTail, rest, suffix,
    List.append_assoc] using htotal

/-! ## The zero test and the emit step -/

/-- The counter scan shared by the increment, decrement and zero-test
families: a phase indexed by the counter it has reached crosses one
complete counter per delimiter until it arrives at its target. -/
theorem reaches_scan_prefix (P : Cslib.URM.Program) (inputs : List Nat)
    (ph : Nat → Phase) (target current n : Nat)
    (regs : Nat → Nat) (pre post : List Char) (st : MState)
    (hbound : current + n ≤ target)
    (hs : st.str = pre ++ token (ph current) ++ encodeRegs n regs ++ post)
    (hpre : '@' ∉ pre) (hpost : '@' ∉ post)
    (hncontrol : ∀ j k, ph j ≠ .control k)
    (hrules : ∀ j, j < target → ∀ r, r ∈ phaseRules (ph j) ↔
      r = rule (token (ph j) ++ ['x']) ('x' :: token (ph j)) ∨
      r = rule (token (ph j) ++ ['d']) ('d' :: token (ph (j + 1))))
    (hx : ∀ j, j < target →
      rule (token (ph j) ++ ['x']) ('x' :: token (ph j)) ∈ compileRules P inputs)
    (hd : ∀ j, j < target →
      rule (token (ph j) ++ ['d']) ('d' :: token (ph (j + 1))) ∈
        compileRules P inputs) :
    Reaches (exec ({} : Config) (compileRules P inputs)) st
      { st with str := pre ++ encodeRegs n regs ++
        (token (ph (current + n)) ++ post) } := by
  induction n generalizing current regs pre st with
  | zero =>
      simp only [encodeRegs, Nat.add_zero, List.append_nil] at hs ⊢
      have heq : { st with str := pre ++ (token (ph current) ++ post) } = st := by
        cases st
        simp_all [List.append_assoc]
      rw [heq]
      exact Reaches.refl (exec ({} : Config) (compileRules P inputs)) st
  | succ n ih =>
      have hcur : current < target := by omega
      let tail := encodeRegs n (fun r => regs (r + 1)) ++ post
      let mid₁ : MState :=
        { st with str := pre ++ List.replicate (regs 0) 'x' ++
          (token (ph current) ++ 'd' :: tail) }
      have hacross : Reaches (exec ({} : Config) (compileRules P inputs)) st mid₁ := by
        have h := reaches_across_xs P inputs (ph current)
          ('d' :: token (ph (current + 1))) pre ('d' :: tail) (regs 0) st
          (by simpa [tail, encodeRegs, List.append_assoc] using hs)
          hpre (by simp [tail, hpost, marker_not_mem_encodeRegs])
          (fun k => hncontrol current k)
          (hrules current hcur)
          (hx current hcur)
        simpa [mid₁, List.append_assoc] using h
      let mid₂ : MState :=
        { mid₁ with str := pre ++ List.replicate (regs 0) 'x' ++
          'd' :: token (ph (current + 1)) ++ tail }
      have hdelim : Reaches (exec ({} : Config) (compileRules P inputs)) mid₁ mid₂ := by
        have h := reaches_phase_right_pair P inputs (ph current) 'd' 'x'
          ('d' :: token (ph (current + 1))) ('x' :: token (ph current))
          (pre ++ List.replicate (regs 0) 'x') tail mid₁
          (by simp [mid₁, List.append_assoc])
          (by simp [hpre])
          (by simp [tail, hpost, marker_not_mem_encodeRegs])
          (by decide) (by decide) (fun k => hncontrol current k)
          (by
            intro r
            rw [hrules current hcur r]
            tauto)
          (hd current hcur)
        simpa [mid₂, List.append_assoc] using h
      have hrest := ih (current := current + 1) (regs := fun r => regs (r + 1))
        (pre := pre ++ List.replicate (regs 0) 'x' ++ ['d']) (st := mid₂)
        (by omega)
        (by simp [mid₂, tail, List.append_assoc])
        (by simp [hpre])
      have htotal := Reaches.trans hacross (Reaches.trans hdelim hrest)
      simpa [mid₁, mid₂, tail, encodeRegs, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htotal

/-- A zero-test scan crosses any initial block of complete counters. -/
theorem reaches_scanZero_prefix (P : Cslib.URM.Program) (inputs : List Nat)
    (done : Done) (zero nonzero : Code) (target current n : Nat)
    (regs : Nat → Nat) (pre post : List Char) (st : MState)
    (hbound : current + n ≤ target)
    (hs : st.str = pre ++ token (.scanZero done zero nonzero target current) ++
      encodeRegs n regs ++ post)
    (hpre : '@' ∉ pre) (hpost : '@' ∉ post)
    (hx : ∀ j, j < target →
      rule (token (.scanZero done zero nonzero target j) ++ ['x'])
        ('x' :: token (.scanZero done zero nonzero target j)) ∈
          compileRules P inputs)
    (hd : ∀ j, j < target →
      rule (token (.scanZero done zero nonzero target j) ++ ['d'])
        ('d' :: token (.scanZero done zero nonzero target (j + 1))) ∈
          compileRules P inputs) :
    Reaches (exec ({} : Config) (compileRules P inputs)) st
      { st with str := pre ++ encodeRegs n regs ++
        (token (.scanZero done zero nonzero target (current + n)) ++ post) } :=
  reaches_scan_prefix P inputs
    (fun j => .scanZero done zero nonzero target j) target current n regs
    pre post st hbound hs hpre hpost (by intro j k; simp)
    (by intro j hj r; simp [phaseRules, hj]) hx hd

/-- The two zero-test outcome rules occur in the generated family. -/
theorem zeroRules_choose_mem (done : Done) (zero nonzero : Code) (target : Nat) :
    rule (token (.scanZero done zero nonzero target target) ++ ['d'])
        ('d' :: token (.back done zero)) ∈ zeroRules done zero nonzero target ∧
    rule (token (.scanZero done zero nonzero target target) ++ ['x'])
        ('x' :: token (.back done nonzero)) ∈ zeroRules done zero nonzero target := by
  constructor
  · simp only [zeroRules, List.mem_append, List.mem_flatMap]
    left; left
    refine ⟨target, List.mem_range.mpr (by omega), ?_⟩
    simp
  · simp only [zeroRules, List.mem_append, List.mem_flatMap]
    left; left
    refine ⟨target, List.mem_range.mpr (by omega), ?_⟩
    simp

/-- A non-target zero-test scan crosses its unary run and its delimiter. -/
theorem zeroRules_scan_mem (done : Done) (zero nonzero : Code)
    (target current : Nat) (hcurrent : current < target) :
    rule (token (.scanZero done zero nonzero target current) ++ ['x'])
        ('x' :: token (.scanZero done zero nonzero target current)) ∈
      zeroRules done zero nonzero target ∧
    rule (token (.scanZero done zero nonzero target current) ++ ['d'])
        ('d' :: token (.scanZero done zero nonzero target (current + 1))) ∈
      zeroRules done zero nonzero target := by
  constructor
  · simp only [zeroRules, List.mem_append, List.mem_flatMap]
    left; left
    refine ⟨current, List.mem_range.mpr (by omega), ?_⟩
    simp [hcurrent]
  · simp only [zeroRules, List.mem_append, List.mem_flatMap]
    left; left
    refine ⟨current, List.mem_range.mpr (by omega), ?_⟩
    simp [hcurrent]

/-- Both return families occur in a zero-test block. -/
theorem zeroRules_back_mem (done : Done) (zero nonzero : Code) (target : Nat) :
    (∀ next ∈ [zero, nonzero], ∀ c ∈ ['x', 'd'],
      rule (c :: token (.back done next)) (token (.back done next) ++ [c]) ∈
        zeroRules done zero nonzero target) ∧
    (∀ next ∈ [zero, nonzero],
      rule ('b' :: token (.back done next)) (token (.exec done next) ++ ['b']) ∈
        zeroRules done zero nonzero target) := by
  constructor
  · intro next hnext c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hnext hc
    rcases hnext with rfl | rfl <;> rcases hc with rfl | rfl <;>
      simp [zeroRules, backRules]
  · intro next hnext
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hnext
    rcases hnext with rfl | rfl <;> simp [zeroRules, backRules]

/-- A zero test on a counter that holds zero installs the loop-exit
continuation and leaves every counter unchanged. -/
theorem reaches_zeroTest_zero (P : Cslib.URM.Program) (inputs : List Nat)
    (done : Done) (current zero nonzero : Code) (R target : Nat) (s : CState)
    (pre post : List Char) (st : MState) (htarget : target < R)
    (hzero : s.regs target = 0)
    (hs : st.str = pre ++ token (.exec done current) ++
      'b' :: encodeRegs R s.regs ++ post)
    (hpre : '@' ∉ pre) (hpost : '@' ∉ post)
    (hexec : ∀ r, r ∈ phaseRules (.exec done current) ↔
      r = rule (token (.exec done current) ++ ['b'])
        ('b' :: token (.scanZero done zero nonzero target 0)))
    (hstart : rule (token (.exec done current) ++ ['b'])
        ('b' :: token (.scanZero done zero nonzero target 0)) ∈
          compileRules P inputs)
    (hscanX : ∀ j, j < target →
      rule (token (.scanZero done zero nonzero target j) ++ ['x'])
        ('x' :: token (.scanZero done zero nonzero target j)) ∈
          compileRules P inputs)
    (hscanD : ∀ j, j < target →
      rule (token (.scanZero done zero nonzero target j) ++ ['d'])
        ('d' :: token (.scanZero done zero nonzero target (j + 1))) ∈
          compileRules P inputs)
    (hchoose : rule (token (.scanZero done zero nonzero target target) ++ ['d'])
        ('d' :: token (.back done zero)) ∈ compileRules P inputs)
    (hbackX : rule ('x' :: token (.back done zero))
        (token (.back done zero) ++ ['x']) ∈ compileRules P inputs)
    (hbackD : rule ('d' :: token (.back done zero))
        (token (.back done zero) ++ ['d']) ∈ compileRules P inputs)
    (hbackB : rule ('b' :: token (.back done zero))
        (token (.exec done zero) ++ ['b']) ∈ compileRules P inputs) :
    Reaches (exec ({} : Config) (compileRules P inputs)) st
      { st with str := pre ++ token (.exec done zero) ++
        'b' :: encodeRegs R s.regs ++ post } := by
  let suffix := encodeRegs (R - (target + 1))
    (fun r => s.regs (target + 1 + r))
  let p := Phase.scanZero done zero nonzero target target
  let mid₀ : MState :=
    { st with str := pre ++ 'b' :: token (.scanZero done zero nonzero target 0) ++
      encodeRegs R s.regs ++ post }
  have hentry : Reaches (exec ({} : Config) (compileRules P inputs)) st mid₀ := by
    have h := reaches_phase_right_single P inputs
      (.exec done current) 'b'
      ('b' :: token (.scanZero done zero nonzero target 0))
      pre (encodeRegs R s.regs ++ post) st
      (by simpa [List.append_assoc] using hs) hpre
      (by simp [marker_not_mem_encodeRegs, hpost]) (by decide)
      (by intro k h; cases h) hexec hstart
    simpa [mid₀, List.append_assoc] using h
  let targetTail := 'd' :: suffix ++ post
  let mid₁ : MState :=
    { mid₀ with
      str := pre ++ 'b' :: (encodeRegs target s.regs ++
        (token p ++ targetTail)) }
  have hscan : Reaches (exec ({} : Config) (compileRules P inputs)) mid₀ mid₁ := by
    have h := reaches_scanZero_prefix P inputs done zero nonzero target 0 target
      s.regs (pre ++ ['b']) targetTail mid₀ (by omega)
      (by
        simp only [mid₀]
        rw [show encodeRegs R s.regs = encodeRegs target s.regs ++
          List.replicate (s.regs target) 'x' ++ 'd' :: suffix from by
            simpa [suffix] using encodeRegs_split_at R target s.regs htarget]
        simp [targetTail, hzero, List.append_assoc])
      (by simp [hpre])
      (by simp [targetTail, suffix, hpost, marker_not_mem_encodeRegs])
      hscanX hscanD
    simpa [mid₁, p, List.append_assoc] using h
  let mid₂ : MState :=
    { mid₁ with
      str := pre ++ 'b' :: (encodeRegs target s.regs ++
        ('d' :: token (.back done zero) ++ suffix ++ post)) }
  have hdo : Reaches (exec ({} : Config) (compileRules P inputs)) mid₁ mid₂ := by
    have h := reaches_phase_right_pair P inputs p 'd' 'x'
      ('d' :: token (.back done zero)) ('x' :: token (.back done nonzero))
      (pre ++ 'b' :: encodeRegs target s.regs) (suffix ++ post) mid₁
      (by simp [mid₁, targetTail, List.append_assoc])
      (by simp [hpre, marker_not_mem_encodeRegs])
      (by simp [suffix, hpost, marker_not_mem_encodeRegs])
      (by decide) (by decide) (by intro k; simp [p])
      (by intro r; simp [p, phaseRules])
      hchoose
    simpa [mid₂, List.append_assoc] using h
  have htape : ∀ c ∈ encodeRegs target s.regs ++ ['d'], c = 'x' ∨ c = 'd' := by
    intro c hc
    simp only [List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | rfl
    · exact encodeRegs_cells target s.regs c hc
    · exact Or.inr rfl
  have hreturn := reaches_back_home P inputs done zero
    (encodeRegs target s.regs ++ ['d']) pre (suffix ++ post) mid₂
    (by simp [mid₂, List.append_assoc]) hpre
    (by simp [suffix, hpost, marker_not_mem_encodeRegs]) htape
    hbackX hbackD hbackB
  have htotal := Reaches.trans hentry
    (Reaches.trans hscan (Reaches.trans hdo hreturn))
  rw [encodeRegs_split_at R target s.regs htarget]
  simpa [mid₀, mid₁, mid₂, p, targetTail, suffix, hzero,
    List.append_assoc] using htotal

/-- A zero test on a nonzero counter installs the loop-body continuation
and leaves every counter unchanged. -/
theorem reaches_zeroTest_nonzero (P : Cslib.URM.Program) (inputs : List Nat)
    (done : Done) (current zero nonzero : Code) (R target : Nat) (s : CState)
    (pre post : List Char) (st : MState) (htarget : target < R)
    (hnz : s.regs target ≠ 0)
    (hs : st.str = pre ++ token (.exec done current) ++
      'b' :: encodeRegs R s.regs ++ post)
    (hpre : '@' ∉ pre) (hpost : '@' ∉ post)
    (hexec : ∀ r, r ∈ phaseRules (.exec done current) ↔
      r = rule (token (.exec done current) ++ ['b'])
        ('b' :: token (.scanZero done zero nonzero target 0)))
    (hstart : rule (token (.exec done current) ++ ['b'])
        ('b' :: token (.scanZero done zero nonzero target 0)) ∈
          compileRules P inputs)
    (hscanX : ∀ j, j < target →
      rule (token (.scanZero done zero nonzero target j) ++ ['x'])
        ('x' :: token (.scanZero done zero nonzero target j)) ∈
          compileRules P inputs)
    (hscanD : ∀ j, j < target →
      rule (token (.scanZero done zero nonzero target j) ++ ['d'])
        ('d' :: token (.scanZero done zero nonzero target (j + 1))) ∈
          compileRules P inputs)
    (hchoose : rule (token (.scanZero done zero nonzero target target) ++ ['x'])
        ('x' :: token (.back done nonzero)) ∈ compileRules P inputs)
    (hbackX : rule ('x' :: token (.back done nonzero))
        (token (.back done nonzero) ++ ['x']) ∈ compileRules P inputs)
    (hbackD : rule ('d' :: token (.back done nonzero))
        (token (.back done nonzero) ++ ['d']) ∈ compileRules P inputs)
    (hbackB : rule ('b' :: token (.back done nonzero))
        (token (.exec done nonzero) ++ ['b']) ∈ compileRules P inputs) :
    Reaches (exec ({} : Config) (compileRules P inputs)) st
      { st with str := pre ++ token (.exec done nonzero) ++
        'b' :: encodeRegs R s.regs ++ post } := by
  let suffix := encodeRegs (R - (target + 1))
    (fun r => s.regs (target + 1 + r))
  let p := Phase.scanZero done zero nonzero target target
  let rest := List.replicate (s.regs target - 1) 'x' ++ 'd' :: suffix ++ post
  let mid₀ : MState :=
    { st with str := pre ++ 'b' :: token (.scanZero done zero nonzero target 0) ++
      encodeRegs R s.regs ++ post }
  have hentry : Reaches (exec ({} : Config) (compileRules P inputs)) st mid₀ := by
    have h := reaches_phase_right_single P inputs
      (.exec done current) 'b'
      ('b' :: token (.scanZero done zero nonzero target 0))
      pre (encodeRegs R s.regs ++ post) st
      (by simpa [List.append_assoc] using hs) hpre
      (by simp [marker_not_mem_encodeRegs, hpost]) (by decide)
      (by intro k h; cases h) hexec hstart
    simpa [mid₀, List.append_assoc] using h
  have hcell : List.replicate (s.regs target) 'x' =
      'x' :: List.replicate (s.regs target - 1) 'x' := by
    obtain ⟨m, hm⟩ : ∃ m, s.regs target = m + 1 := ⟨s.regs target - 1, by omega⟩
    simp [hm, List.replicate_succ]
  let targetTail := List.replicate (s.regs target) 'x' ++ 'd' :: suffix ++ post
  let mid₁ : MState :=
    { mid₀ with
      str := pre ++ 'b' :: (encodeRegs target s.regs ++
        (token p ++ targetTail)) }
  have hscan : Reaches (exec ({} : Config) (compileRules P inputs)) mid₀ mid₁ := by
    have h := reaches_scanZero_prefix P inputs done zero nonzero target 0 target
      s.regs (pre ++ ['b']) targetTail mid₀ (by omega)
      (by
        simp only [mid₀]
        rw [show encodeRegs R s.regs = encodeRegs target s.regs ++
          List.replicate (s.regs target) 'x' ++ 'd' :: suffix from by
            simpa [suffix] using encodeRegs_split_at R target s.regs htarget]
        simp [targetTail, List.append_assoc])
      (by simp [hpre])
      (by simp [targetTail, suffix, hpost, marker_not_mem_encodeRegs])
      hscanX hscanD
    simpa [mid₁, p, List.append_assoc] using h
  let mid₂ : MState :=
    { mid₁ with
      str := pre ++ 'b' :: (encodeRegs target s.regs ++
        ('x' :: token (.back done nonzero) ++ rest)) }
  have hdo : Reaches (exec ({} : Config) (compileRules P inputs)) mid₁ mid₂ := by
    have h := reaches_phase_right_pair P inputs p 'x' 'd'
      ('x' :: token (.back done nonzero)) ('d' :: token (.back done zero))
      (pre ++ 'b' :: encodeRegs target s.regs) rest mid₁
      (by simp [mid₁, targetTail, rest, hcell, List.append_assoc])
      (by simp [hpre, marker_not_mem_encodeRegs])
      (by simp [rest, suffix, hpost, marker_not_mem_encodeRegs])
      (by decide) (by decide) (by intro k; simp [p])
      (by intro r; simp [p, phaseRules]; tauto)
      hchoose
    simpa [mid₂, List.append_assoc] using h
  have htape : ∀ c ∈ encodeRegs target s.regs ++ ['x'], c = 'x' ∨ c = 'd' := by
    intro c hc
    simp only [List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | rfl
    · exact encodeRegs_cells target s.regs c hc
    · exact Or.inl rfl
  have hreturn := reaches_back_home P inputs done nonzero
    (encodeRegs target s.regs ++ ['x']) pre rest mid₂
    (by simp [mid₂, List.append_assoc]) hpre
    (by simp [rest, suffix, hpost, marker_not_mem_encodeRegs]) htape
    hbackX hbackD hbackB
  have htotal := Reaches.trans hentry
    (Reaches.trans hscan (Reaches.trans hdo hreturn))
  rw [encodeRegs_split_at R target s.regs htarget]
  simpa [mid₀, mid₁, mid₂, p, targetTail, rest, suffix, hcell,
    List.append_assoc] using htotal

/-- One emit step appends a byte marker to the output prefix. -/
theorem reaches_emit (P : Cslib.URM.Program) (inputs : List Nat)
    (done : Done) (rest : Code) (R : Nat) (s : CState)
    (post : List Char) (st : MState)
    (hs : st.str = List.replicate s.out 'o' ++
      token (.exec done (.emit :: rest)) ++ 'b' :: encodeRegs R s.regs ++ post)
    (hpost : '@' ∉ post)
    (hmem : rule (token (.exec done (.emit :: rest)) ++ ['b'])
        ('o' :: token (.exec done rest) ++ ['b']) ∈ compileRules P inputs) :
    Reaches (exec ({} : Config) (compileRules P inputs)) st
      { st with str := List.replicate s.emitOne.out 'o' ++
        (token (.exec done rest) ++ 'b' :: encodeRegs R s.emitOne.regs ++ post) } := by
  have h := reaches_phase_right_single P inputs
    (.exec done (.emit :: rest)) 'b'
    ('o' :: token (.exec done rest) ++ ['b'])
    (List.replicate s.out 'o') (encodeRegs R s.regs ++ post) st
    (by simpa [List.append_assoc] using hs) (by simp)
    (by simp [marker_not_mem_encodeRegs, hpost]) (by decide)
    (by intro k h; cases h)
    (by intro r; simp [phaseRules]) hmem
  simpa [CState.emitOne, List.replicate_succ', List.append_assoc] using h

/-! ## Lifting a counter-machine derivation -/

/-- Rule generation is compositional in the code it traverses. -/
theorem generate_append (done : Done) : ∀ (c₁ c₂ suffix : Code),
    generate done (c₁ ++ c₂) suffix =
      generate done c₁ (c₂ ++ suffix) ++ generate done c₂ suffix
  | [], c₂, suffix => by simp [generate]
  | .inc a :: rest, c₂, suffix => by
      simp only [List.cons_append, generate]
      rw [generate_append done rest c₂ suffix]
      simp [List.append_assoc]
  | .dec a :: rest, c₂, suffix => by
      simp only [List.cons_append, generate]
      rw [generate_append done rest c₂ suffix]
      simp [List.append_assoc]
  | .emit :: rest, c₂, suffix => by
      simp only [List.cons_append, generate]
      rw [generate_append done rest c₂ suffix]
      simp [List.append_assoc]
  | .loop a body :: rest, c₂, suffix => by
      simp only [List.cons_append, generate]
      rw [generate_append done rest c₂ suffix]
      simp [List.append_assoc]
termination_by c₁ _ _ => codeWeight c₁
decreasing_by
  all_goals simp [codeWeight] <;> omega

/-- The rules for the head command of a continuation are generated for it. -/
theorem headRules_sub_generate (done : Done) (cmd : Cmd) (rest suffix : Code) :
    ∀ r ∈ headRules done (cmd :: (rest ++ suffix)),
      r ∈ generate done (cmd :: rest) suffix := by
  intro r hr
  cases cmd <;> simp only [generate, List.mem_append] <;> tauto

/-- Rules for the tail of a continuation are generated for the whole. -/
theorem tail_sub_generate (done : Done) (cmd : Cmd) (rest suffix : Code) :
    ∀ r ∈ generate done rest suffix, r ∈ generate done (cmd :: rest) suffix := by
  intro r hr
  cases cmd <;> simp only [generate, List.mem_append] <;> tauto

/-- Unrolling a loop needs no rules beyond the ones the loop already has. -/
theorem generate_loop_body_sub (done : Done) (a : Nat) (body rest suffix : Code) :
    ∀ r ∈ generate done (body ++ .loop a body :: rest) suffix,
      r ∈ generate done (.loop a body :: rest) suffix := by
  intro r hr
  rw [generate_append] at hr
  simp only [List.mem_append] at hr
  rcases hr with hb | ht
  · simp only [generate, List.mem_append]
    exact Or.inl (Or.inr (by simpa using hb))
  · exact ht

/-- A big-step counter-machine derivation is simulated by the deterministic
Thue rewriter: the generated rules carry the phase token from the head of
the code to the end of it, transforming the unary register tape exactly as
the derivation does, and appending one `o` for every emitted byte. -/
theorem reaches_exec (P : Cslib.URM.Program) (inputs : List Nat) (done : Done)
    {R : Nat} {code : Code} {s t : CState} (hev : Ev R code s t) :
    ∀ (suffix : Code) (post : List Char) (st : MState), '@' ∉ post →
      (∀ r ∈ generate done code suffix, r ∈ compileRules P inputs) →
      st.str = List.replicate s.out 'o' ++ token (.exec done (code ++ suffix)) ++
        'b' :: encodeRegs R s.regs ++ post →
      Reaches (exec ({} : Config) (compileRules P inputs)) st
        { st with str := List.replicate t.out 'o' ++
          (token (.exec done suffix) ++ 'b' :: encodeRegs R t.regs ++ post) } := by
  induction hev with
  | @nil s =>
      intro suffix post st _hpost _havail hs
      have heq : { st with str := List.replicate s.out 'o' ++
          (token (.exec done suffix) ++ 'b' :: encodeRegs R s.regs ++ post) } = st := by
        cases st
        simp_all [List.append_assoc]
      rw [heq]
      exact Reaches.refl (exec ({} : Config) (compileRules P inputs)) st
  | @inc reg cs s t hlt _hsub ih =>
      intro suffix post st hpost havail hs
      have hhead : ∀ x ∈ headRules done (.inc reg :: (cs ++ suffix)),
          x ∈ compileRules P inputs :=
        fun x hx => havail x (headRules_sub_generate done (.inc reg) cs suffix x hx)
      have hfam : ∀ x ∈ incRules done (cs ++ suffix) reg, x ∈ compileRules P inputs := by
        intro x hx
        exact hhead x (by simp only [headRules]; exact List.mem_cons_of_mem _ hx)
      have hback := incRules_back_mem done (cs ++ suffix) reg
      let mid : MState :=
        { st with str := List.replicate s.out 'o' ++
          (token (.exec done (cs ++ suffix)) ++
            'b' :: encodeRegs R (s.up reg).regs ++ post) }
      have hstep : Reaches (exec ({} : Config) (compileRules P inputs)) st mid := by
        have h := reaches_inc P inputs done (cs ++ suffix) R reg s
          (List.replicate s.out 'o') post st hlt (by simpa using hs) (by simp) hpost
          (hhead _ (by simp only [headRules]; exact List.mem_cons_self))
          (fun j hj => hfam _ (incRules_scan_x_mem done (cs ++ suffix) reg j hj))
          (fun j hj => hfam _ (incRules_scan_d_mem done (cs ++ suffix) reg j hj))
          (hfam _ (incRules_finish_mem done (cs ++ suffix) reg))
          (hfam _ (hback.1 'x' (by simp)))
          (hfam _ (hback.1 'd' (by simp)))
          (hfam _ hback.2)
        simpa [mid, List.append_assoc] using h
      have hrest := ih suffix post mid hpost
        (fun x hx => havail x (tail_sub_generate done (.inc reg) cs suffix x hx))
        (by simp [mid, List.append_assoc])
      have htotal := Reaches.trans hstep hrest
      simpa [mid] using htotal
  | @dec reg cs s t hlt hnz _hsub ih =>
      intro suffix post st hpost havail hs
      have hhead : ∀ x ∈ headRules done (.dec reg :: (cs ++ suffix)),
          x ∈ compileRules P inputs :=
        fun x hx => havail x (headRules_sub_generate done (.dec reg) cs suffix x hx)
      have hfam : ∀ x ∈ decRules done (cs ++ suffix) reg, x ∈ compileRules P inputs := by
        intro x hx
        exact hhead x (by simp only [headRules]; exact List.mem_cons_of_mem _ hx)
      have hback := decRules_back_mem done (cs ++ suffix) reg
      let mid : MState :=
        { st with str := List.replicate s.out 'o' ++
          (token (.exec done (cs ++ suffix)) ++
            'b' :: encodeRegs R (s.down reg).regs ++ post) }
      have hstep : Reaches (exec ({} : Config) (compileRules P inputs)) st mid := by
        have h := reaches_dec P inputs done (cs ++ suffix) R reg s
          (List.replicate s.out 'o') post st hlt hnz (by simpa using hs) (by simp) hpost
          (hhead _ (by simp only [headRules]; exact List.mem_cons_self))
          (fun j hj => hfam _ (decRules_scan_x_mem done (cs ++ suffix) reg j hj))
          (fun j hj => hfam _ (decRules_scan_d_mem done (cs ++ suffix) reg j hj))
          (hfam _ (decRules_take_mem done (cs ++ suffix) reg))
          (hfam _ (hback.1 'x' (by simp)))
          (hfam _ (hback.1 'd' (by simp)))
          (hfam _ hback.2)
        simpa [mid, List.append_assoc] using h
      have hrest := ih suffix post mid hpost
        (fun x hx => havail x (tail_sub_generate done (.dec reg) cs suffix x hx))
        (by simp [mid, List.append_assoc])
      have htotal := Reaches.trans hstep hrest
      simpa [mid] using htotal
  | @emit cs s t _hsub ih =>
      intro suffix post st hpost havail hs
      have hhead : ∀ x ∈ headRules done (.emit :: (cs ++ suffix)),
          x ∈ compileRules P inputs :=
        fun x hx => havail x (headRules_sub_generate done .emit cs suffix x hx)
      let mid : MState :=
        { st with str := List.replicate s.emitOne.out 'o' ++
          (token (.exec done (cs ++ suffix)) ++
            'b' :: encodeRegs R s.emitOne.regs ++ post) }
      have hstep : Reaches (exec ({} : Config) (compileRules P inputs)) st mid := by
        have h := reaches_emit P inputs done (cs ++ suffix) R s post st
          (by simpa using hs) hpost
          (hhead _ (by simp [headRules]))
        simpa [mid, List.append_assoc] using h
      have hrest := ih suffix post mid hpost
        (fun x hx => havail x (tail_sub_generate done .emit cs suffix x hx))
        (by simp [mid, List.append_assoc])
      have htotal := Reaches.trans hstep hrest
      simpa [mid] using htotal
  | @loopZ reg b cs s t hlt hz _hsub ih =>
      intro suffix post st hpost havail hs
      have hhead : ∀ x ∈ headRules done (.loop reg b :: (cs ++ suffix)),
          x ∈ compileRules P inputs :=
        fun x hx => havail x (headRules_sub_generate done (.loop reg b) cs suffix x hx)
      have hfam : ∀ x ∈ zeroRules done (cs ++ suffix)
          (b ++ .loop reg b :: (cs ++ suffix)) reg, x ∈ compileRules P inputs := by
        intro x hx
        exact hhead x (by simp only [headRules]; exact List.mem_cons_of_mem _ hx)
      have hchoose := zeroRules_choose_mem done (cs ++ suffix)
        (b ++ .loop reg b :: (cs ++ suffix)) reg
      have hback := zeroRules_back_mem done (cs ++ suffix)
        (b ++ .loop reg b :: (cs ++ suffix)) reg
      let mid : MState :=
        { st with str := List.replicate s.out 'o' ++
          (token (.exec done (cs ++ suffix)) ++
            'b' :: encodeRegs R s.regs ++ post) }
      have hstep : Reaches (exec ({} : Config) (compileRules P inputs)) st mid := by
        have h := reaches_zeroTest_zero P inputs done
          (.loop reg b :: (cs ++ suffix)) (cs ++ suffix)
          (b ++ .loop reg b :: (cs ++ suffix)) R reg s
          (List.replicate s.out 'o') post st hlt hz (by simpa using hs) (by simp) hpost
          (by intro r; simp [phaseRules])
          (hhead _ (by simp only [headRules]; exact List.mem_cons_self))
          (fun j hj => hfam _ (zeroRules_scan_mem done _ _ reg j hj).1)
          (fun j hj => hfam _ (zeroRules_scan_mem done _ _ reg j hj).2)
          (hfam _ hchoose.1)
          (hfam _ (hback.1 (cs ++ suffix) (by simp) 'x' (by simp)))
          (hfam _ (hback.1 (cs ++ suffix) (by simp) 'd' (by simp)))
          (hfam _ (hback.2 (cs ++ suffix) (by simp)))
        simpa [mid, List.append_assoc] using h
      have hrest := ih suffix post mid hpost
        (fun x hx => havail x (tail_sub_generate done (.loop reg b) cs suffix x hx))
        (by simp [mid, List.append_assoc])
      have htotal := Reaches.trans hstep hrest
      simpa [mid] using htotal
  | @loopS reg b cs s t hlt hnz _hsub ih =>
      intro suffix post st hpost havail hs
      have hhead : ∀ x ∈ headRules done (.loop reg b :: (cs ++ suffix)),
          x ∈ compileRules P inputs :=
        fun x hx => havail x (headRules_sub_generate done (.loop reg b) cs suffix x hx)
      have hfam : ∀ x ∈ zeroRules done (cs ++ suffix)
          (b ++ .loop reg b :: (cs ++ suffix)) reg, x ∈ compileRules P inputs := by
        intro x hx
        exact hhead x (by simp only [headRules]; exact List.mem_cons_of_mem _ hx)
      have hchoose := zeroRules_choose_mem done (cs ++ suffix)
        (b ++ .loop reg b :: (cs ++ suffix)) reg
      have hback := zeroRules_back_mem done (cs ++ suffix)
        (b ++ .loop reg b :: (cs ++ suffix)) reg
      have hunroll : (b ++ Cmd.loop reg b :: cs) ++ suffix =
          b ++ Cmd.loop reg b :: (cs ++ suffix) := by
        simp [List.append_assoc]
      let mid : MState :=
        { st with str := List.replicate s.out 'o' ++
          (token (.exec done (b ++ Cmd.loop reg b :: (cs ++ suffix))) ++
            'b' :: encodeRegs R s.regs ++ post) }
      have hstep : Reaches (exec ({} : Config) (compileRules P inputs)) st mid := by
        have h := reaches_zeroTest_nonzero P inputs done
          (.loop reg b :: (cs ++ suffix)) (cs ++ suffix)
          (b ++ .loop reg b :: (cs ++ suffix)) R reg s
          (List.replicate s.out 'o') post st hlt hnz (by simpa using hs) (by simp) hpost
          (by intro r; simp [phaseRules])
          (hhead _ (by simp only [headRules]; exact List.mem_cons_self))
          (fun j hj => hfam _ (zeroRules_scan_mem done _ _ reg j hj).1)
          (fun j hj => hfam _ (zeroRules_scan_mem done _ _ reg j hj).2)
          (hfam _ hchoose.2)
          (hfam _ (hback.1 (b ++ .loop reg b :: (cs ++ suffix)) (by simp) 'x' (by simp)))
          (hfam _ (hback.1 (b ++ .loop reg b :: (cs ++ suffix)) (by simp) 'd' (by simp)))
          (hfam _ (hback.2 (b ++ .loop reg b :: (cs ++ suffix)) (by simp)))
        simpa [mid, List.append_assoc] using h
      have hrest := ih suffix post mid hpost
        (fun x hx => havail x (generate_loop_body_sub done reg b cs suffix x hx))
        (by simp [mid, hunroll, List.append_assoc])
      have htotal := Reaches.trans hstep hrest
      simpa [mid] using htotal

/-! ## Dispatch: from the counter answer back to a source control marker -/

/-- Generated rules are determined by their two character lists. -/
theorem rule_inj {lhs₁ rhs₁ lhs₂ rhs₂ : List Char}
    (h : rule lhs₁ rhs₁ = rule lhs₂ rhs₂) : lhs₁ = lhs₂ ∧ rhs₁ = rhs₂ := by
  have h1 := congrArg (fun r => r.lhs.toList) h
  have h2 := congrArg (fun r => match r.rhs with | .str s => s.toList | _ => []) h
  simp only [rule, str, String.toList_ofList] at h1 h2
  exact ⟨h1, h2⟩

private theorem foldl_max_spec : ∀ (os : List Outcome) (n : Nat),
    n ≤ os.foldl (fun m o => max m o.count) n ∧
    ∀ o ∈ os, o.count ≤ os.foldl (fun m o => max m o.count) n := by
  intro os
  induction os with
  | nil => intro n; exact ⟨le_refl n, by simp⟩
  | cons a as ih =>
      intro n
      obtain ⟨h1, h2⟩ := ih (max n a.count)
      refine ⟨?_, ?_⟩
      · simp only [List.foldl_cons]
        exact le_trans (le_max_left n a.count) h1
      · intro o ho
        simp only [List.foldl_cons]
        rcases List.mem_cons.mp ho with rfl | ho'
        · exact le_trans (le_max_right n o.count) h1
        · exact h2 o ho'

/-- Every dispatch outcome is covered by the generated counting rules. -/
theorem maxOutcome_ge (os : List Outcome) (o : Outcome) (ho : o ∈ os) :
    o.count ≤ maxOutcome os :=
  (foldl_max_spec os 0).2 o ho

/-! ### Membership in the dispatch block -/

theorem finishRules_seek_mem (done : Done) (j : Nat) (hj : j < done.target) :
    rule (token (.seekPC done j) ++ ['x']) ('x' :: token (.seekPC done j)) ∈
      finishRules done ∧
    rule (token (.seekPC done j) ++ ['d']) ('d' :: token (.seekPC done (j + 1))) ∈
      finishRules done := by
  constructor
  · simp only [finishRules, List.mem_cons, List.mem_append, List.mem_flatMap,
      List.mem_map, List.mem_range]
    refine Or.inl (Or.inl (Or.inl (Or.inr ⟨j, by omega, ?_⟩)))
    simp [hj]
  · simp only [finishRules, List.mem_cons, List.mem_append, List.mem_flatMap,
      List.mem_map, List.mem_range]
    refine Or.inl (Or.inl (Or.inl (Or.inr ⟨j, by omega, ?_⟩)))
    simp [hj]

theorem finishRules_take_mem (done : Done) :
    rule (token (.seekPC done done.target) ++ ['x']) (token (.countPC done 1)) ∈
      finishRules done := by
  simp only [finishRules, List.mem_cons, List.mem_append, List.mem_flatMap,
    List.mem_map, List.mem_range]
  refine Or.inl (Or.inl (Or.inl (Or.inr ⟨done.target, by omega, ?_⟩)))
  simp

theorem finishRules_count_mem (done : Done) (n : Nat)
    (hn : n ≤ maxOutcome done.outcomes) :
    rule (token (.countPC done n) ++ ['x']) (token (.countPC done (n + 1))) ∈
      finishRules done := by
  simp only [finishRules, List.mem_cons, List.mem_append, List.mem_flatMap,
    List.mem_map, List.mem_range]
  refine Or.inl (Or.inl (Or.inr ⟨n, by omega, ?_⟩))
  simp

theorem finishRules_choose_mem (done : Done) (o : Outcome) (ho : o ∈ done.outcomes) :
    rule (token (.countPC done o.count) ++ ['d']) ('d' :: token (.backPC o.pc)) ∈
      finishRules done := by
  simp only [finishRules, List.mem_cons, List.mem_append, List.mem_flatMap,
    List.mem_map, List.mem_range]
  exact Or.inl (Or.inr ⟨o, ho, rfl⟩)

theorem finishRules_return_mem (done : Done) (o : Outcome) (ho : o ∈ done.outcomes) :
    rule ('x' :: token (.backPC o.pc)) (token (.backPC o.pc) ++ ['x']) ∈
      finishRules done ∧
    rule ('d' :: token (.backPC o.pc)) (token (.backPC o.pc) ++ ['d']) ∈
      finishRules done ∧
    rule ('b' :: token (.backPC o.pc)) (token (.control o.pc) ++ ['b']) ∈
      finishRules done := by
  refine ⟨?_, ?_, ?_⟩
  all_goals
    simp only [finishRules, List.mem_cons, List.mem_append, List.mem_flatMap,
      List.mem_map, List.mem_range]
    refine Or.inr ⟨o, ho, ?_⟩
    simp

/-! ### The dispatch run -/

/-- Counting consumes the unary program-counter run one cell at a time. -/
theorem reaches_count (P : Cslib.URM.Program) (inputs : List Nat) (done : Done)
    (n j : Nat) (pre post : List Char) (st : MState)
    (hs : st.str = pre ++ token (.countPC done n) ++ List.replicate j 'x' ++ post)
    (hpre : '@' ∉ pre) (hpost : '@' ∉ post)
    (hcount : ∀ i, i < n + j →
      rule (token (.countPC done i) ++ ['x']) (token (.countPC done (i + 1))) ∈
        compileRules P inputs) :
    Reaches (exec ({} : Config) (compileRules P inputs)) st
      { st with str := pre ++ token (.countPC done (n + j)) ++ post } := by
  induction j generalizing n st with
  | zero =>
      simp only [List.replicate_zero, Nat.add_zero] at hs ⊢
      have heq : { st with str := pre ++ token (.countPC done n) ++ post } = st := by
        cases st
        simp_all [List.append_assoc]
      rw [heq]
      exact Reaches.refl (exec ({} : Config) (compileRules P inputs)) st
  | succ j ih =>
      let mid : MState :=
        { st with str := pre ++
          (token (.countPC done (n + 1)) ++ List.replicate j 'x' ++ post) }
      have hstep : Reaches (exec ({} : Config) (compileRules P inputs)) st mid := by
        have h := reaches_phase_right_cell P inputs (.countPC done n) 'x'
          (token (.countPC done (n + 1))) pre (List.replicate j 'x' ++ post) st
          (by simpa [List.replicate_succ, List.append_assoc] using hs)
          hpre (by simp [hpost]) (by decide) (by intro k; simp)
          (by
            intro r hr
            simp only [phaseRules, List.mem_cons, List.mem_map] at hr
            rcases hr with rfl | ⟨o, _, rfl⟩
            · exact ⟨'x', _, rfl⟩
            · exact ⟨'d', _, rfl⟩)
          (by
            intro rep' hr
            simp only [phaseRules, List.mem_cons, List.mem_map] at hr
            rcases hr with heq | ⟨o, _, heq⟩
            · exact (rule_inj heq).2
            · exact absurd (rule_inj heq).1 (by simp))
          (hcount n (by omega))
        simpa [mid, List.append_assoc] using h
      have hrest := ih (n := n + 1) (st := mid)
        (by simp [mid, List.append_assoc])
        (by intro i hi; exact hcount i (by omega))
      have htotal := Reaches.trans hstep hrest
      simpa [mid, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htotal

/-- Clearing a bounded counter empties its unary run. -/
theorem encodeRegs_clear (R target : Nat) (regs : Nat → Nat) (hbound : target < R) :
    encodeRegs R (Function.update regs target 0) =
      encodeRegs target regs ++ 'd' :: encodeRegs (R - (target + 1))
        (fun r => regs (target + 1 + r)) := by
  rw [encodeRegs_split_at R target (Function.update regs target 0) hbound]
  have hprefix : encodeRegs target (Function.update regs target 0) =
      encodeRegs target regs :=
    encodeRegs_congr target (fun r hr => Function.update_of_ne (by omega) _ _)
  have hsuffix : encodeRegs (R - (target + 1))
      (fun r => Function.update regs target 0 (target + 1 + r)) =
      encodeRegs (R - (target + 1)) (fun r => regs (target + 1 + r)) :=
    encodeRegs_congr _ (fun r _hr => Function.update_of_ne (by omega) _ _)
  rw [hprefix, hsuffix]
  simp [Function.update_self]

/-- The dispatch block reads the counter holding `nextProgramCounter + 1`,
clears it, and installs the source control marker for that program counter. -/
theorem reaches_finish (P : Cslib.URM.Program) (inputs : List Nat) (done : Done)
    (R : Nat) (regs : Nat → Nat) (o : Outcome) (pre post : List Char) (st : MState)
    (htarget : done.target < R)
    (hmem : o ∈ done.outcomes) (hcount : regs done.target = o.count)
    (hpos : 0 < o.count) (hfun : OutcomeFunctional done.outcomes)
    (hs : st.str = pre ++ token (.exec done []) ++ 'b' :: encodeRegs R regs ++ post)
    (hpre : '@' ∉ pre) (hpost : '@' ∉ post)
    (havail : ∀ r ∈ finishRules done, r ∈ compileRules P inputs) :
    Reaches (exec ({} : Config) (compileRules P inputs)) st
      { st with str := pre ++ token (.control o.pc) ++
        'b' :: encodeRegs R (Function.update regs done.target 0) ++ post } := by
  have hmax : o.count ≤ maxOutcome done.outcomes := maxOutcome_ge _ o hmem
  let suffix := encodeRegs (R - (done.target + 1))
    (fun r => regs (done.target + 1 + r))
  let tail := List.replicate (o.count - 1) 'x' ++ 'd' :: suffix ++ post
  -- enter the dispatch block
  let mid₀ : MState :=
    { st with str := pre ++ 'b' :: token (.seekPC done 0) ++ encodeRegs R regs ++ post }
  have hentry : Reaches (exec ({} : Config) (compileRules P inputs)) st mid₀ := by
    have h := reaches_phase_right_single P inputs (.exec done []) 'b'
      ('b' :: token (.seekPC done 0)) pre (encodeRegs R regs ++ post) st
      (by simpa [List.append_assoc] using hs) hpre
      (by simp [marker_not_mem_encodeRegs, hpost]) (by decide)
      (by intro k h; cases h)
      (by intro r; simp [phaseRules])
      (havail _ (by simp [finishRules]))
    simpa [mid₀, List.append_assoc] using h
  -- walk to the program-counter counter
  let seekTail := List.replicate (regs done.target) 'x' ++ 'd' :: suffix ++ post
  let mid₁ : MState :=
    { mid₀ with str := pre ++ 'b' :: (encodeRegs done.target regs ++
        (token (.seekPC done done.target) ++ seekTail)) }
  have hseek : Reaches (exec ({} : Config) (compileRules P inputs)) mid₀ mid₁ := by
    have h := reaches_scan_prefix P inputs (fun j => .seekPC done j) done.target 0 done.target
      regs (pre ++ ['b']) seekTail mid₀ (by omega)
      (by
        simp only [mid₀]
        rw [show encodeRegs R regs = encodeRegs done.target regs ++
          List.replicate (regs done.target) 'x' ++ 'd' :: suffix from by
            simpa [suffix] using encodeRegs_split_at R done.target regs htarget]
        simp [seekTail, List.append_assoc])
      (by simp [hpre])
      (by simp [seekTail, suffix, hpost, marker_not_mem_encodeRegs])
      (by intro j k; simp)
      (by intro j hj r; simp [phaseRules, hj])
      (fun j hj => havail _ (finishRules_seek_mem done j hj).1)
      (fun j hj => havail _ (finishRules_seek_mem done j hj).2)
    simpa [mid₁, List.append_assoc] using h
  -- take the first unary cell, which starts the count at one
  have hrun : List.replicate (regs done.target) 'x' = 'x' :: List.replicate (o.count - 1) 'x' := by
    rw [hcount]
    obtain ⟨m, hm⟩ : ∃ m, o.count = m + 1 := ⟨o.count - 1, by omega⟩
    simp [hm, List.replicate_succ]
  let mid₂ : MState :=
    { mid₁ with str := pre ++ 'b' :: (encodeRegs done.target regs ++
        (token (.countPC done 1) ++ tail)) }
  have htake : Reaches (exec ({} : Config) (compileRules P inputs)) mid₁ mid₂ := by
    have h := reaches_phase_right_single P inputs (.seekPC done done.target) 'x'
      (token (.countPC done 1)) (pre ++ 'b' :: encodeRegs done.target regs) tail mid₁
      (by simp [mid₁, seekTail, tail, hrun, List.append_assoc])
      (by simp [hpre, marker_not_mem_encodeRegs])
      (by simp [tail, suffix, hpost, marker_not_mem_encodeRegs])
      (by decide) (by intro k; simp)
      (by intro r; simp [phaseRules])
      (havail _ (finishRules_take_mem done))
    simpa [mid₂, List.append_assoc] using h
  -- count the rest of the run
  let mid₃ : MState :=
    { mid₂ with str := pre ++ 'b' :: (encodeRegs done.target regs ++
        (token (.countPC done o.count) ++ 'd' :: suffix ++ post)) }
  have hcnt : Reaches (exec ({} : Config) (compileRules P inputs)) mid₂ mid₃ := by
    have h := reaches_count P inputs done 1 (o.count - 1)
      (pre ++ 'b' :: encodeRegs done.target regs) ('d' :: suffix ++ post) mid₂
      (by simp [mid₂, tail, List.append_assoc])
      (by simp [hpre, marker_not_mem_encodeRegs])
      (by simp [suffix, hpost, marker_not_mem_encodeRegs])
      (by
        intro i hi
        exact havail _ (finishRules_count_mem done i (by omega)))
    have hsum : 1 + (o.count - 1) = o.count := by omega
    simpa [mid₃, hsum, List.append_assoc] using h
  -- choose the destination and return to the left boundary
  let mid₄ : MState :=
    { mid₃ with str := pre ++ 'b' :: (encodeRegs done.target regs ++
        ('d' :: token (.backPC o.pc) ++ suffix ++ post)) }
  have hchoose : Reaches (exec ({} : Config) (compileRules P inputs)) mid₃ mid₄ := by
    have h := reaches_phase_right_cell P inputs (.countPC done o.count) 'd'
      ('d' :: token (.backPC o.pc)) (pre ++ 'b' :: encodeRegs done.target regs)
      (suffix ++ post) mid₃
      (by simp [mid₃, List.append_assoc])
      (by simp [hpre, marker_not_mem_encodeRegs])
      (by simp [suffix, hpost, marker_not_mem_encodeRegs])
      (by decide) (by intro k; simp)
      (by
        intro r hr
        simp only [phaseRules, List.mem_cons, List.mem_map] at hr
        rcases hr with rfl | ⟨o', _, rfl⟩
        · exact ⟨'x', _, rfl⟩
        · exact ⟨'d', _, rfl⟩)
      (by
        intro rep' hr
        simp only [phaseRules, List.mem_cons, List.mem_map, List.mem_filter] at hr
        rcases hr with heq | ⟨o', ⟨ho', hcnt'⟩, heq⟩
        · exact absurd (rule_inj heq).1 (by simp)
        · have hrep := (rule_inj heq).2
          have hpc : o'.pc = o.pc := by
            apply hfun o' ho' o hmem
            simpa using hcnt'
          rw [← hrep, hpc])
      (havail _ (finishRules_choose_mem done o hmem))
    simpa [mid₄, List.append_assoc] using h
  have hreturn := finishRules_return_mem done o hmem
  have htape : ∀ c ∈ encodeRegs done.target regs ++ ['d'], c = 'x' ∨ c = 'd' := by
    intro c hc
    simp only [List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | rfl
    · exact encodeRegs_cells done.target regs c hc
    · exact Or.inr rfl
  have hhome := reaches_left_home P inputs (.backPC o.pc)
    (token (.control o.pc) ++ ['b']) (encodeRegs done.target regs ++ ['d'])
    pre (suffix ++ post) mid₄
    (by simp [mid₄, List.append_assoc]) hpre
    (by simp [suffix, hpost, marker_not_mem_encodeRegs]) htape
    (by intro k h; cases h)
    (by intro r; simp [phaseRules])
    (havail _ hreturn.1) (havail _ hreturn.2.1) (havail _ hreturn.2.2)
  have htotal := Reaches.trans hentry (Reaches.trans hseek
    (Reaches.trans htake (Reaches.trans hcnt (Reaches.trans hchoose hhome))))
  rw [encodeRegs_clear R done.target regs htarget]
  simpa [mid₀, mid₁, mid₂, mid₃, mid₄, suffix, tail, seekTail,
    List.append_assoc] using htotal

/-! ## One source instruction -/

/-- A source instruction's whole generated block occurs in the rulebase. -/
theorem instrRules_mem_compileAt (B : Nat) :
    ∀ (base : Nat) (P : Cslib.URM.Program) (offset : Nat) (i : Cslib.URM.Instr),
      P[offset]? = some i →
      ∀ r ∈ instrRules B (base + offset) i, r ∈ compileAt B base P
  | _, [], _, _, h, _, _ => by simp at h
  | base, head :: rest, 0, i, h, r, hr => by
      simp at h
      subst head
      exact List.mem_append_left _ (by simpa using hr)
  | base, head :: rest, offset + 1, i, h, r, hr => by
      change rest[offset]? = some i at h
      apply List.mem_append_right (instrRules B base head)
      exact instrRules_mem_compileAt B (base + 1) rest offset i h r
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hr)

theorem instrRules_mem_compileRules (P : Cslib.URM.Program) (inputs : List Nat)
    (k : Nat) (i : Cslib.URM.Instr) (hi : P[k]? = some i) :
    ∀ r ∈ instrRules (sourceBound P inputs) k i, r ∈ compileRules P inputs := by
  intro r hr
  simpa [compileRules] using
    instrRules_mem_compileAt (sourceBound P inputs) 0 P k i hi r (by simpa using hr)

/-- Deterministic selection at a source control marker picks that
instruction's entry rule.  The canonical family of a control phase is empty,
so the only rule that can match is a control rule, and the marker fixes
which one. -/
theorem firstMatch_eq_control (P : Cslib.URM.Program) (inputs : List Nat)
    (k : Nat) (i : Cslib.URM.Instr) (hi : P[k]? = some i)
    (pre post : List Char) (hpre : '@' ∉ pre) (hpost : '@' ∉ post) :
    firstMatch (compileRules P inputs) (pre ++ token (.control k) ++ post) =
      some (pre.length, rule (token (.control k))
        (token (.exec ⟨pcReg (sourceBound P inputs), outcomes k i⟩
          (macroCode (sourceBound P inputs) k i)))) := by
  have hmem := control_rule_mem_compileRules P inputs k i hi
  have heocc : firstOccurrence? (rule (token (.control k))
      (token (.exec ⟨pcReg (sourceBound P inputs), outcomes k i⟩
        (macroCode (sourceBound P inputs) k i)))).lhs.toList
      (pre ++ token (.control k) ++ post) = some pre.length := by
    simp only [rule, str, String.toList_ofList]
    simpa using firstOccurrence_token_right (.control k) [] pre post hpre
  obtain ⟨pos, r, hselect⟩ := firstMatch_exists_of_mem hmem heocc
  obtain ⟨hr, hrocc⟩ := firstMatch_some hselect
  rcases compileRules_firstMatch_origin_at P inputs (.control k) pre post
      hpre hpost pos r hselect with hphase | hcontrol
  · simp [phaseRules] at hphase
  · obtain ⟨k', i', hp, hi', hrule⟩ := hcontrol
    have hkk : k = k' := by
      have := hp
      simpa using this
    subst hkk
    have hii : i' = i := by
      rw [hi'] at hi
      exact Option.some.inj hi
    subst hii
    subst hrule
    have hpos : pos = pre.length := by
      rw [heocc] at hrocc
      exact (Option.some.inj hrocc).symm
    simpa [hpos] using hselect

/-- Entering a source instruction installs its counter macro. -/
theorem reaches_control (P : Cslib.URM.Program) (inputs : List Nat)
    (k : Nat) (i : Cslib.URM.Instr) (hi : P[k]? = some i)
    (pre post : List Char) (hpre : '@' ∉ pre) (hpost : '@' ∉ post) (st : MState)
    (hs : st.str = pre ++ token (.control k) ++ post) :
    Reaches (exec ({} : Config) (compileRules P inputs)) st
      { st with str := pre ++ token (.exec ⟨pcReg (sourceBound P inputs),
        outcomes k i⟩ (macroCode (sourceBound P inputs) k i)) ++ post } := by
  apply reaches_of_step
  unfold step
  simp only
  rw [hs, firstMatch_eq_control P inputs k i hi pre post hpre hpost]
  simp only [Option.map_some]
  refine congrArg some ?_
  have h := applyAt_rule_right (.control k) []
    pre (token (.exec ⟨pcReg (sourceBound P inputs), outcomes k i⟩
      (macroCode (sourceBound P inputs) k i))) post st (by simpa using hs)
  simpa using h

/-- One URM transition is simulated by one complete pass of the generated
rewriter: enter the instruction's macro, run the counter code, then dispatch
on the counter it leaves behind. -/
theorem reaches_step (P : Cslib.URM.Program) (inputs : List Nat)
    {u u' : Cslib.URM.State} (hstep : Cslib.URM.Step P u u')
    (w : Nat → Nat) (out : Nat) (post : List Char) (hpost : '@' ∉ post)
    (st : MState)
    (hsrc : SourceMatches (sourceBound P inputs) w u.regs)
    (hpc : w (pcReg (sourceBound P inputs)) = 0)
    (hclean : ScratchClean (sourceBound P inputs) w)
    (hs : st.str = List.replicate out 'o' ++ token (.control u.pc) ++
      'b' :: encodeRegs (counterBound (sourceBound P inputs)) w ++ post) :
    ∃ w', SourceMatches (sourceBound P inputs) w' u'.regs ∧
      w' (pcReg (sourceBound P inputs)) = 0 ∧
      ScratchClean (sourceBound P inputs) w' ∧
      Reaches (exec ({} : Config) (compileRules P inputs)) st
        { st with str := List.replicate out 'o' ++ token (.control u'.pc) ++
          'b' :: encodeRegs (counterBound (sourceBound P inputs)) w' ++ post } := by
  obtain ⟨i, hget, hnextpc, hnextregs⟩ := step_arithmetic hstep
  have himax : i.maxRegister < sourceBound P inputs :=
    instr_below_sourceBound (List.mem_of_getElem? hget)
  obtain ⟨w₁, hev, hsrc₁, hpc₁, hclean₁, hout⟩ :=
    macroCode_correct (B := sourceBound P inputs) (k := u.pc) i u.regs himax
      ⟨w, out⟩ hsrc hpc hclean
  have havail := instrRules_mem_compileRules P inputs u.pc i hget
  have hgen : ∀ r ∈ generate ⟨pcReg (sourceBound P inputs), outcomes u.pc i⟩
      (macroCode (sourceBound P inputs) u.pc i) [], r ∈ compileRules P inputs := by
    intro r hr
    exact havail r (List.mem_append_left _ (List.mem_cons_of_mem _ hr))
  have hfin : ∀ r ∈ finishRules ⟨pcReg (sourceBound P inputs), outcomes u.pc i⟩,
      r ∈ compileRules P inputs := by
    intro r hr
    exact havail r (List.mem_append_right _ hr)
  have hptarget : pcReg (sourceBound P inputs) <
      counterBound (sourceBound P inputs) := by
    simp [pcReg, counterBound]
  -- enter the instruction
  let mid₀ : MState :=
    { st with str := List.replicate out 'o' ++
      (token (.exec ⟨pcReg (sourceBound P inputs), outcomes u.pc i⟩
        (macroCode (sourceBound P inputs) u.pc i)) ++
        'b' :: encodeRegs (counterBound (sourceBound P inputs)) w ++ post) }
  have henter : Reaches (exec ({} : Config) (compileRules P inputs)) st mid₀ := by
    have h := reaches_control P inputs u.pc i hget (List.replicate out 'o')
      ('b' :: encodeRegs (counterBound (sourceBound P inputs)) w ++ post)
      (by simp) (by simp [marker_not_mem_encodeRegs, hpost]) st
      (by simpa [List.append_assoc] using hs)
    simpa [mid₀, List.append_assoc] using h
  -- run the counter macro
  let mid₁ : MState :=
    { mid₀ with str := List.replicate out 'o' ++
      (token (.exec ⟨pcReg (sourceBound P inputs), outcomes u.pc i⟩ []) ++
        'b' :: encodeRegs (counterBound (sourceBound P inputs)) w₁ ++ post) }
  have hmacro : Reaches (exec ({} : Config) (compileRules P inputs)) mid₀ mid₁ := by
    have h := reaches_exec P inputs ⟨pcReg (sourceBound P inputs), outcomes u.pc i⟩
      hev [] post mid₀ hpost (by simpa using hgen) (by simp [mid₀, List.append_assoc])
    simpa [mid₁, List.append_assoc] using h
  -- dispatch on the counter the macro left
  let w₂ := Function.update w₁ (pcReg (sourceBound P inputs)) 0
  let mid₂ : MState :=
    { mid₁ with str := List.replicate out 'o' ++
      (token (.control u'.pc) ++
        'b' :: encodeRegs (counterBound (sourceBound P inputs)) w₂ ++ post) }
  have hdispatch : Reaches (exec ({} : Config) (compileRules P inputs)) mid₁ mid₂ := by
    have h := reaches_finish P inputs ⟨pcReg (sourceBound P inputs), outcomes u.pc i⟩
      (counterBound (sourceBound P inputs)) w₁
      ⟨w₁ (pcReg (sourceBound P inputs)), instrNextPC u.pc i u.regs⟩
      (List.replicate out 'o') post mid₁ hptarget hout rfl
      (by simp [hpc₁]) (outcomes_functional u.pc i)
      (by simp [mid₁, List.append_assoc]) (by simp)
      hpost hfin
    simpa [mid₂, w₂, hnextpc, List.append_assoc] using h
  have hsrc₂ : SourceMatches (sourceBound P inputs) w₂ u'.regs := by
    intro r hr
    have hne : r ≠ pcReg (sourceBound P inputs) := by simp [pcReg]; omega
    rw [hnextregs]
    simpa [w₂, Function.update_of_ne hne] using hsrc₁ r hr
  refine ⟨w₂, hsrc₂, by simp [w₂], ?_, ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hclean₁
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals
      simp only [w₂, savedReg, cmpXReg, cmpYReg, tmpReg, gateReg, eqReg, fallReg,
        pcReg] at *
      first
        | (rw [Function.update_of_ne (by omega)]; assumption)
  · have htotal := Reaches.trans henter (Reaches.trans hmacro hdispatch)
    simpa [mid₀, mid₁, mid₂] using htotal

/-! ## A whole halting run -/

/-- Composition of the per-instruction simulation over a URM run. -/
theorem reaches_steps (P : Cslib.URM.Program) (inputs : List Nat)
    {u u' : Cslib.URM.State} (hsteps : Cslib.URM.Steps P u u') :
    ∀ (w : Nat → Nat) (out : Nat) (post : List Char), '@' ∉ post →
      ∀ st : MState,
      SourceMatches (sourceBound P inputs) w u.regs →
      w (pcReg (sourceBound P inputs)) = 0 →
      ScratchClean (sourceBound P inputs) w →
      st.str = List.replicate out 'o' ++ token (.control u.pc) ++
        'b' :: encodeRegs (counterBound (sourceBound P inputs)) w ++ post →
      ∃ w', SourceMatches (sourceBound P inputs) w' u'.regs ∧
        w' (pcReg (sourceBound P inputs)) = 0 ∧
        ScratchClean (sourceBound P inputs) w' ∧
        Reaches (exec ({} : Config) (compileRules P inputs)) st
          { st with str := List.replicate out 'o' ++ token (.control u'.pc) ++
            'b' :: encodeRegs (counterBound (sourceBound P inputs)) w' ++ post } := by
  induction hsteps with
  | refl =>
      intro w out post _hpost st hsrc hpc hclean hs
      refine ⟨w, hsrc, hpc, hclean, ?_⟩
      have heq : { st with str := List.replicate out 'o' ++ token (.control u.pc) ++
          'b' :: encodeRegs (counterBound (sourceBound P inputs)) w ++ post } = st := by
        cases st
        simp_all
      rw [heq]
      exact Reaches.refl (exec ({} : Config) (compileRules P inputs)) st
  | @tail z _ _hprefix hlast ih =>
      intro w out post hpost st hsrc hpc hclean hs
      obtain ⟨w₁, hsrc₁, hpc₁, hclean₁, hreach₁⟩ := ih w out post hpost st hsrc hpc hclean hs
      obtain ⟨w₂, hsrc₂, hpc₂, hclean₂, hreach₂⟩ := reaches_step P inputs hlast w₁ out
        post hpost
        { st with str := List.replicate out 'o' ++ token (.control z.pc) ++
          'b' :: encodeRegs (counterBound (sourceBound P inputs)) w₁ ++ post }
        hsrc₁ hpc₁ hclean₁ rfl
      exact ⟨w₂, hsrc₂, hpc₂, hclean₂, Reaches.trans hreach₁ hreach₂⟩

/-- No rule matches once the source program counter has run off the end. -/
theorem firstMatch_control_none (P : Cslib.URM.Program) (inputs : List Nat)
    (k : Nat) (hk : P[k]? = none) (pre post : List Char)
    (hpre : '@' ∉ pre) (hpost : '@' ∉ post) :
    firstMatch (compileRules P inputs) (pre ++ token (.control k) ++ post) = none := by
  cases hm : firstMatch (compileRules P inputs) (pre ++ token (.control k) ++ post) with
  | none => rfl
  | some pr =>
      obtain ⟨pos, r⟩ := pr
      rcases compileRules_firstMatch_origin_at P inputs (.control k) pre post
          hpre hpost pos r hm with hphase | hcontrol
      · simp [phaseRules] at hphase
      · obtain ⟨k', i', hp, hi', _⟩ := hcontrol
        have hkk : k = k' := by simpa using hp
        subst hkk
        simp [hk] at hi'

/-- The interpreter is insensitive to the parts of its configuration that
the rewrite strategy does not read. -/
theorem exec_strategy_congr (cfg cfg' : Config) (h : cfg.strategy = cfg'.strategy)
    (rules : List Rule) : ∀ (fuel : Nat) (st : MState),
    exec cfg rules fuel st = exec cfg' rules fuel st := by
  intro fuel
  induction fuel with
  | zero => intro st; rfl
  | succ fuel ih =>
      intro st
      have hstep : step cfg rules st = step cfg' rules st := by
        unfold step
        rw [h]
      simp only [exec, hstep]
      split
      · rfl
      · exact ih _

/-- Total runnable compiler from a URM program and its input vector. -/
def compile (P : Cslib.URM.Program) (inputs : List Nat) : Prog :=
  let B := sourceBound P inputs
  let R := counterBound B
  { rules := compileRules P inputs
    initial := str (encodeState R ⟨Cslib.URM.Regs.ofInputs inputs, 0⟩ (.control 0)) }

/-- The compiler embeds the input vector in the generated counter program. -/
def encodeInput (_inputs : List Nat) : Input := Input.ofString ""

/-- Read register zero from the final state emitted by `Config.finalState`.
The first `b` is the left boundary of the register file, and the following
unary `x` run is register zero. -/
def decodeOutput (out : ByteArray) : Option Nat := do
  let s ← String.fromUTF8? out
  let after ← (s.toList.dropWhile (fun c => c != 'b')).tail?
  return (after.takeWhile (fun c => c == 'x')).length

theorem fromUTF8?_toUTF8 (s : String) : String.fromUTF8? s.toUTF8 = some s := by
  simp only [String.toUTF8_eq_toByteArray, String.fromUTF8?, dif_pos s.isValidUTF8,
    Option.some.injEq, ← String.toByteArray_inj]
  simp [String.fromUTF8]

private theorem dropWhile_to_boundary (pre tail : List Char) (h : 'b' ∉ pre) :
    (pre ++ 'b' :: tail).dropWhile (fun c => c != 'b') = 'b' :: tail := by
  induction pre with
  | nil => simp
  | cons a pre ih =>
    have ha : a ≠ 'b' := fun he => h (he ▸ List.mem_cons_self)
    have hp : 'b' ∉ pre := fun hb => h (List.mem_cons_of_mem a hb)
    simp [ha, ih hp]

/-- The decoder reads register zero from every represented final state. -/
theorem decodeOutput_encodeState (R : Nat) (s : CState) (phase : Phase) :
    decodeOutput
        ((String.ofList (encodeState (R + 1) s phase) ++ "\n").toUTF8) =
      some (s.regs 0) := by
  simp only [decodeOutput, fromUTF8?_toUTF8]
  change (some (String.ofList (encodeState (R + 1) s phase) ++ "\n")).bind
      (fun text =>
        ((text.toList.dropWhile (fun c => c != 'b')).tail?).bind
          (fun after => some ((after.takeWhile (fun c => c == 'x')).length))) =
    some (s.regs 0)
  rw [Option.bind_some]
  simp only [String.toList_append, String.toList_ofList]
  rw [show "\n".toList = ['\n'] by decide]
  rw [encodeState]
  rw [show List.replicate s.out 'o' ++ token phase ++
      'b' :: encodeRegs (R + 1) s.regs ++ ['q'] ++ ['\n'] =
      (List.replicate s.out 'o' ++ token phase) ++
        'b' :: (encodeRegs (R + 1) s.regs ++ ['q'] ++ ['\n']) by
    simp [List.append_assoc]]
  rw [
    dropWhile_to_boundary (List.replicate s.out 'o' ++ token phase)
      (encodeRegs (R + 1) s.regs ++ ['q'] ++ ['\n'])]
  · simp [encodeRegs]
  · simp

/-- Reading the final-state observation off a halting run. -/
theorem evalProg_of_exec (cfg : Config) (p : Prog) (input : Input) (fuel : Nat)
    (st : MState) (hcfg : cfg.strategy = .first) (hfinal : cfg.finalState = true)
    (h : exec cfg p.rules fuel
        { str := p.initial.toList, input := input, rng := 0 } =
      (st, Langlib.Common.Exit.halted))
    (hout : st.output = ByteArray.empty) :
    Langlib.Thue.evalProg cfg p input fuel =
      { output := (String.ofList st.str ++ "\n").toUTF8,
        exit := Langlib.Common.Exit.halted } := by
  unfold Langlib.Thue.evalProg
  simp only [hcfg, hfinal]
  rw [h]
  simp [hout, ByteArray.empty_append]
  exact fun hcon => absurd hcon (by decide)

/-! ## The simulation theorem -/

/-- End to end: a halting URM run is simulated by the generated Thue
program under the deterministic strategy, and the final-state observation
decodes to the contents of register zero. -/
theorem simulation (P : Cslib.URM.Program) (inputs : List Nat) (result : Nat)
    (h : Cslib.URM.HaltsWithResult P inputs result) :
    ∃ fuel,
      (Langlib.Thue.evalProg { finalState := true } (compile P inputs)
          (Input.ofString "") fuel).exit = Langlib.Common.Exit.halted ∧
      decodeOutput (Langlib.Thue.evalProg { finalState := true } (compile P inputs)
          (Input.ofString "") fuel).output = some result := by
  obtain ⟨u, hsteps, hhalt, hresult⟩ := h
  obtain ⟨hsrc0, hpc0, hclean0⟩ := initial_macro_invariant P inputs
  let st₀ : MState :=
    { str := (compile P inputs).initial.toList, input := Input.ofString "",
      output := ByteArray.empty, rng := 0 }
  have hst₀ : st₀.str = List.replicate 0 'o' ++ token (.control 0) ++
      'b' :: encodeRegs (counterBound (sourceBound P inputs))
        (Cslib.URM.Regs.ofInputs inputs) ++ ['q'] := by
    simp [st₀, compile, str, encodeState]
  obtain ⟨w, hsrc, hpc, hclean, hreach⟩ :=
    reaches_steps P inputs hsteps (Cslib.URM.Regs.ofInputs inputs) 0 ['q']
      (by simp) st₀ hsrc0 hpc0 hclean0 hst₀
  set stf : MState :=
    { st₀ with str := List.replicate 0 'o' ++ token (.control u.pc) ++
      'b' :: encodeRegs (counterBound (sourceBound P inputs)) w ++ ['q'] } with hstf
  have hgetnone : P[u.pc]? = none := List.getElem?_eq_none hhalt
  have hstr : stf.str = List.replicate 0 'o' ++ token (.control u.pc) ++
      ('b' :: encodeRegs (counterBound (sourceBound P inputs)) w ++ ['q']) := by
    simp [hstf, List.append_assoc]
  have hnone : step ({} : Config) (compileRules P inputs) stf = none := by
    unfold step
    simp only
    rw [hstr, firstMatch_control_none P inputs u.pc hgetnone
      (List.replicate 0 'o')
      ('b' :: encodeRegs (counterBound (sourceBound P inputs)) w ++ ['q'])
      (by simp) (by simp [marker_not_mem_encodeRegs])]
    rfl
  have hexec1 : exec ({} : Config) (compileRules P inputs) 1 stf =
      (stf, Langlib.Common.Exit.halted) := by
    simp [exec, hnone]
  obtain ⟨m, hm⟩ := hreach.eval 1
  have hrun : exec ({ finalState := true } : Config) (compile P inputs).rules m st₀ =
      (stf, Langlib.Common.Exit.halted) := by
    rw [exec_strategy_congr ({ finalState := true } : Config) ({} : Config) rfl]
    rw [show (compile P inputs).rules = compileRules P inputs from rfl, hm, hexec1]
  have heval : Langlib.Thue.evalProg { finalState := true } (compile P inputs)
      (Input.ofString "") m =
      { output := (String.ofList stf.str ++ "\n").toUTF8,
        exit := Langlib.Common.Exit.halted } :=
    evalProg_of_exec { finalState := true } (compile P inputs) (Input.ofString "") m
      stf rfl rfl hrun rfl
  have hw0 : w 0 = result := by
    have h0 : (0 : Nat) < sourceBound P inputs := sourceBound_pos P inputs
    have := hsrc 0 h0
    rw [this]
    exact hresult
  refine ⟨m, by rw [heval], ?_⟩
  rw [heval]
  have hstate : stf.str = encodeState (counterBound (sourceBound P inputs))
      ⟨w, 0⟩ (.control u.pc) := by
    simp [hstf, encodeState]
  have hR : counterBound (sourceBound P inputs) = (sourceBound P inputs + 7) + 1 := by
    simp [counterBound]
  rw [hstate, hR]
  simpa [hw0] using
    decodeOutput_encodeState (sourceBound P inputs + 7) ⟨w, 0⟩ (.control u.pc)

end Langlib.Computability.URMThue

namespace Langlib.Computability

open Langlib.Common

/-- The tag type naming Thue for the shared computability interface. -/
inductive ThueLang : Type

instance : ProgLang ThueLang where
  Prog := Langlib.Thue.Prog
  parse := Langlib.Thue.parse
  run := Langlib.Thue.evalProg { finalState := true }

/-- Thue is Turing complete, via the verified URM-to-Thue generator. -/
def thueComplete : TuringComplete ThueLang where
  compile := URMThue.compile
  encodeInput := URMThue.encodeInput
  decodeOutput := URMThue.decodeOutput
  simulates := fun P inputs result h => URMThue.simulation P inputs result h

end Langlib.Computability
