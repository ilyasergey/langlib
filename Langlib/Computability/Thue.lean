import Langlib.Computability.Brainfuck
import Langlib.Languages.Thue.Semantics

/-!
# A URM-to-Thue generator and its proved local obligations

The compiler reuses the structured counter machine proved correct in
`Langlib.Computability.Brainfuck`.  Its counters are rendered as finite unary
runs separated by `d`.  A self-delimiting control token contains the current
counter-code continuation.  Rewrite phases move that token to the selected
counter, perform one local operation, and move it back to the left boundary.

Every generated left-hand side is intended to contain the unique character
`@`.  The file proves that represented states have one such marker, that the
rules for each counter command are anchored by it, and that the counter macro
for each source instruction has the right arithmetic effect.

The remaining theorem must connect every intermediate phase to
`Thue.firstMatch` and `Thue.applyAt`, prove that no other generated rule is
applicable, and compose those steps over a halting URM run.  Until that theorem
is present this module deliberately does not define `thueComplete`.
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

@[simp] theorem marker_not_mem_encPhase (p : Phase) : '@' ∉ encPhase p := by
  cases p <;> simp [encPhase]

@[simp] theorem boundary_not_mem_encPhase (p : Phase) : 'b' ∉ encPhase p := by
  cases p <;> simp [encPhase, encNat]

/-- Every live machine phase is represented by one `@...$` token. -/
def token (p : Phase) : List Char := '@' :: encPhase p ++ ['$']

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

/-- Generate one finite rule block per URM instruction. -/
def compileAt (B : Nat) : Nat → Cslib.URM.Program → List Rule
  | _, [] => []
  | k, i :: rest => instrRules B k i ++ compileAt B (k + 1) rest

/-- The finite generated rulebase.  Repeated entries can arise when control
paths share a return continuation.  They are equal as `Rule` values and have
the same unique occurrence and rewrite result; the determinism theorem is
stated for distinct rule values.  Keeping the list structural also avoids a
quadratic duplicate-removal pass over the deliberately large generated code. -/
def compileRules (P : Cslib.URM.Program) (inputs : List Nat) : List Rule :=
  compileAt (sourceBound P inputs) 0 P

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
