import Langlib.Computability.Brainfuck
import Langlib.Languages.Thue.Semantics

/-!
# A URM-to-Thue generator and its proved local obligations

The compiler reuses the structured counter machine proved correct in
`Langlib.Computability.Brainfuck`.  Its counters are rendered as finite unary
runs separated by `d`.  A self-delimiting control token contains the current
counter-code continuation.  Rewrite phases move that token to the selected
counter, perform one local operation, and move it back to the left boundary.

Every generated left-hand side contains the unique character `@`. The file
proves prefix-free phase encoding, calculates token occurrences and
`Thue.applyAt`, and shows that any rule selected by `Thue.firstMatch` on a
represented state belongs to that state's active phase. It also proves that
the counter macro for each source instruction has the right arithmetic effect.

The remaining theorem must prove that a generator-family member fixes the
rewrite result for its active phase and adjacent cell, then compose those
micro-steps over a halting URM run. Until that theorem is present this module
deliberately does not define `thueComplete`.
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

/-- Possible values written to the counter-machine program counter by source
instruction `i` at index `k`. -/
def outcomes (k : Nat) : Cslib.URM.Instr → List Outcome
  | .J m n q => if m = n then [⟨q + 1, q⟩] else [⟨q + 1, q⟩, ⟨k + 2, k + 1⟩]
  | _ => [⟨k + 2, k + 1⟩]

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

/-- The rule selected by the actual `.first` strategy on a represented state
belongs to its active phase. -/
theorem compileRules_firstMatch_active (P : Cslib.URM.Program) (inputs : List Nat)
    (R : Nat) (s : CState) (phase : Phase) (pos : Nat) (r : Rule)
    (hm : firstMatch (compileRules P inputs) (encodeState R s phase) = some (pos, r)) :
    ActiveRule phase r := by
  obtain ⟨hr, ho⟩ := firstMatch_some hm
  exact compileRules_match_active P inputs R s phase r hr pos ho

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

end Langlib.Computability.URMThue

namespace Langlib.Computability

open Langlib.Common

/-- The tag type naming Thue for the shared computability interface. -/
inductive ThueLang : Type

instance : ProgLang ThueLang where
  Prog := Langlib.Thue.Prog
  parse := Langlib.Thue.parse
  run := Langlib.Thue.evalProg { finalState := true }

end Langlib.Computability
