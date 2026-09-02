import Langlib.Common.Computability
import Langlib.Computability.Counter
import Langlib.Languages.MalbolgeUnshackled

/-!
# Malbolge Unshackled: the ground floor of a completeness proof

Malbolge Unshackled (Ørjan Johansen, 2007) is claimed Turing complete, and
`docs/PLAN.md` Stage 8 wants that claim to be a `TuringComplete` witness:
a compiler from the unlimited register machine, plus a simulation theorem.
That witness does not exist yet. This file is the layer underneath it, and
it has three jobs.

**Name the language.** `MalbolgeUnshackledLang` is the `ProgLang` tag, so
the eventual claim can be stated at all. A program is a loaded `Image`, the
parser is the loader, and the runner is `evalImage` at the default
configuration (rotation width 10).

**Do the arithmetic of addresses.** Execution walks the code pointer
through the naturals by 3-adic successor, and decodes the word at each
address against that address's residue. Three facts make that walk
reasonable about: `ofNat` round-trips through `toNat?`, successor of a
natural is the next natural, and the residue of a natural is the natural
modulo 282. All three are stated below and proved from the definitions
rather than checked on examples.

**Record what stands in the way.** Two obstructions have to be understood
before a compiler can be written, and both are theorems rather than
folklore:

* `opcode_ne_encrypt`: after a word executes it is replaced by its image
  under `xlat2`, and no word at any address decodes to the same opcode
  twice running. The encryption table has no fixed point, and the 94 codes
  `33..126` are distinct modulo 94, so a code cell's opcode *always*
  changes under its own execution. Every loop in the language must
  therefore be built out of cells that cycle, which is the whole difficulty
  of Malbolge programming, inherited unchanged.
* `restTable_not_printable`: the memory fill that covers the addresses the
  loader never reached produces, at three of its six residues, values that
  are not printable naturals, so executing one hangs. A program cannot walk
  off its own end into fresh code. Whatever loops, loops inside the loaded
  image.

`docs/computability-malbolge-unshackled.md` says how the intended proof
gets past both, and what is still open.
-/

namespace Langlib.Computability

open Langlib.Common
open Langlib.MalbolgeUnshackled

/-- The tag type naming Malbolge Unshackled for the shared computability
interface. A program is a loaded image, as it is for Malbolge: the language
is loaded rather than parsed. -/
inductive MalbolgeUnshackledLang : Type

/-- The runner is the reference semantics at its default configuration:
starting rotation width 10, the loader's permissive mode. The rotation
width is a knob the language leaves open, so a completeness claim stated
through this instance is a claim about the least legal width; see
`docs/computability-malbolge-unshackled.md`. -/
instance : ProgLang MalbolgeUnshackledLang where
  Prog := Image
  parse := load
  run := evalImage {}

/-- **Malbolge Unshackled is lawful**: a completed run is a fixed point of
more fuel. Proved in `Langlib/Languages/MalbolgeUnshackled/Stability.lean`. -/
instance : LawfulProgLang MalbolgeUnshackledLang where
  halted_stable := evalImage_stable {}

namespace Unshackled

/-! ## Base-3 digits without fuel

`Value.natTrits` carries a fuel argument, which is convenient to run and
useless to reason with. `trits3` is the same function written by recursion
on the number itself, and `natTrits_eq` identifies the two. -/

/-- Base-3 digits of a natural, least significant first, no leading zeros. -/
def trits3 : Nat → List Trit
  | 0 => []
  | n + 1 => Trit.ofResidue ((n + 1) % 3) :: trits3 ((n + 1) / 3)
decreasing_by exact Nat.div_lt_self (Nat.succ_pos n) (by omega)

/-- The value a trit list denotes, least significant first. -/
def denote (l : List Trit) : Nat := l.foldr (fun t acc => acc * 3 + t.toNat) 0

/-! ### Residues as trits

`Trit.ofResidue` reduces its argument modulo 3 itself, so the outer `% 3`
that the definitions carry around can always be dropped. -/

theorem ofResidue_mod (r : Nat) : Trit.ofResidue (r % 3) = Trit.ofResidue r := by
  unfold Trit.ofResidue
  rw [show r % 3 % 3 = r % 3 by omega]

theorem ofResidue_zero {r : Nat} (h : r % 3 = 0) : Trit.ofResidue r = .t0 := by
  unfold Trit.ofResidue; rw [h]
  rfl

theorem ofResidue_one {r : Nat} (h : r % 3 = 1) : Trit.ofResidue r = .t1 := by
  unfold Trit.ofResidue; rw [h]
  rfl

theorem ofResidue_two {r : Nat} (h : r % 3 = 2) : Trit.ofResidue r = .t2 := by
  unfold Trit.ofResidue; rw [h]
  rfl

theorem ofResidue_ne_t0 {r : Nat} (h : r % 3 ≠ 0) : Trit.ofResidue r ≠ .t0 := by
  have hr : r % 3 = 1 ∨ r % 3 = 2 := by omega
  rcases hr with hr | hr
  · rw [ofResidue_one hr]; simp
  · rw [ofResidue_two hr]; simp

theorem toNat_ofResidue (r : Nat) : (Trit.ofResidue r).toNat = r % 3 := by
  have h : r % 3 = 0 ∨ r % 3 = 1 ∨ r % 3 = 2 := by omega
  rcases h with h | h | h
  · rw [ofResidue_zero h, h]; rfl
  · rw [ofResidue_one h, h]; rfl
  · rw [ofResidue_two h, h]; rfl

/-! ### Equations for `trits3`

`trits3` recurses on `n / 3`, so Lean compiles it by well-founded recursion
and its defining equations are theorems rather than reductions. Naming them
once keeps every proof below to `rw`. -/

theorem trits3_zero : trits3 0 = [] := by rw [trits3]

theorem trits3_succ (n : Nat) :
    trits3 (n + 1) = Trit.ofResidue (n + 1) :: trits3 ((n + 1) / 3) := by
  rw [trits3, ofResidue_mod]

theorem natTritsAux_eq (f : Nat) : ∀ n, n ≤ f → Value.natTritsAux f n = trits3 n := by
  induction f with
  | zero =>
    intro n hn
    have hz : n = 0 := by omega
    subst hz
    rw [trits3_zero]
    rfl
  | succ f ih =>
    intro n hn
    match n with
    | 0 => rw [trits3_zero]; rfl
    | n + 1 =>
      rw [Value.natTritsAux, ih ((n + 1) / 3) (by omega), trits3_succ, ofResidue_mod]

theorem natTrits_eq (n : Nat) : Value.natTrits n = trits3 n :=
  natTritsAux_eq n n (Nat.le_refl n)

theorem ofNat_eq (n : Nat) : Value.ofNat n = ⟨.t0, trits3 n⟩ := by
  unfold Value.ofNat
  rw [natTrits_eq]

/-! ## What a natural address is worth -/

theorem denote_trits3 (n : Nat) : denote (trits3 n) = n := by
  induction n using trits3.induct with
  | case1 => rw [trits3_zero]; rfl
  | case2 n ih =>
    rw [trits3_succ n]
    unfold denote at ih ⊢
    rw [List.foldr_cons, ih, toNat_ofResidue]
    omega

/-- A natural read back out of its value is itself. -/
theorem toNat?_ofNat (n : Nat) : (Value.ofNat n).toNat? = some n := by
  rw [ofNat_eq]
  unfold Value.toNat?
  simp only []
  exact congrArg some (denote_trits3 n)

/-- Naturals in `33..126` are exactly the printable words. -/
theorem printableCode?_ofNat {n : Nat} (h₁ : 33 ≤ n) (h₂ : n ≤ 126) :
    printableCode? (Value.ofNat n) = some n := by
  unfold printableCode?
  rw [toNat?_ofNat]
  simp [h₁, h₂]

/-! ## The residue of an address

`Value.modClass` is a decree rather than a homomorphism: Johansen shows
that no additive remainder exists on the 3-adics. On the naturals, though,
it is the honest remainder, and that is the only case instruction layout
needs, because the code pointer starts at zero and 3-adic successor keeps
it there. -/

theorem leadModClass_t0 : Value.leadModClass .t0 = 0 := by decide

theorem leadModAdjust_t0 : Value.leadModAdjust .t0 = 0 := by decide

theorem modClass_trits3 (n : Nat) :
    (trits3 n).foldr (fun t mc => (mc * 3 + t.toNat + 0) % Value.fullMod) 0
      = n % Value.fullMod := by
  induction n using trits3.induct with
  | case1 => rw [trits3_zero]; simp [Value.fullMod]
  | case2 n ih =>
    rw [trits3_succ n, List.foldr_cons, ih, toNat_ofResidue]
    simp only [Value.fullMod]
    omega

/-- The residue of a natural address is the residue of the natural. Both
the mod-94 opcode rule and the mod-6 memory fill read off this one number,
so this is the fact instruction placement rests on. -/
theorem modClass_ofNat (n : Nat) : (Value.ofNat n).modClass = n % 282 := by
  rw [ofNat_eq]
  unfold Value.modClass
  simp only [leadModClass_t0, leadModAdjust_t0]
  exact modClass_trits3 n

theorem mod94_ofNat (n : Nat) : (Value.ofNat n).mod94 = n % 94 := by
  rw [Value.mod94, modClass_ofNat]
  omega

/-! ## The code pointer walks the naturals -/

theorem trits3_ne_nil {n : Nat} (h : 0 < n) : trits3 n ≠ [] := by
  match n with
  | m + 1 => rw [trits3_succ]; simp

theorem lastTrit?_trits3 (n : Nat) : lastTrit? (trits3 n) ≠ some .t0 := by
  induction n using trits3.induct with
  | case1 => rw [trits3_zero]; simp [lastTrit?]
  | case2 n ih =>
    rw [trits3_succ n]
    by_cases h : (n + 1) / 3 = 0
    · rw [h, trits3_zero]
      simpa [lastTrit?] using ofResidue_ne_t0 (r := n + 1) (by omega)
    · have hne : trits3 ((n + 1) / 3) ≠ [] := trits3_ne_nil (by omega)
      match hd : trits3 ((n + 1) / 3) with
      | [] => exact absurd hd hne
      | x :: xs =>
        rw [hd] at ih
        simpa [lastTrit?] using ih

theorem stripLead_eq_self {t : Trit} : ∀ {l : List Trit},
    lastTrit? l ≠ some t → stripLead t l = l
  | [], _ => rfl
  | [x], h => by
    have hx : x ≠ t := by simpa [lastTrit?] using h
    simp [stripLead, hx]
  | x :: y :: ys, h => by
    have h' : lastTrit? (y :: ys) ≠ some t := by simpa [lastTrit?] using h
    have ih := stripLead_eq_self h'
    show (match stripLead t (y :: ys) with
      | [] => if x = t then [] else [x]
      | zs => x :: zs) = x :: y :: ys
    rw [ih]

theorem mk'_trits3 (n : Nat) : Value.mk' .t0 (trits3 n) = Value.ofNat n := by
  rw [ofNat_eq, Value.mk', stripLead_eq_self (lastTrit?_trits3 n)]

theorem succTrits_trits3 (n : Nat) :
    Value.succTrits .t0 (trits3 n) = (.t0, trits3 (n + 1)) := by
  induction n using trits3.induct with
  | case1 =>
    rw [trits3_zero, trits3_succ 0, trits3_zero, ofResidue_one (r := 0 + 1) (by omega)]
    rfl
  | case2 n ih =>
    simp only [Nat.succ_eq_add_one]
    rw [trits3_succ n]
    have hr : (n + 1) % 3 = 0 ∨ (n + 1) % 3 = 1 ∨ (n + 1) % 3 = 2 := by omega
    rcases hr with hr | hr | hr
    · rw [ofResidue_zero hr, Value.succTrits, trits3_succ (n + 1),
        ofResidue_one (r := n + 1 + 1) (by omega),
        show (n + 1 + 1) / 3 = (n + 1) / 3 by omega]
    · rw [ofResidue_one hr, Value.succTrits, trits3_succ (n + 1),
        ofResidue_two (r := n + 1 + 1) (by omega),
        show (n + 1 + 1) / 3 = (n + 1) / 3 by omega]
    · rw [ofResidue_two hr, Value.succTrits, ih, trits3_succ (n + 1),
        ofResidue_zero (r := n + 1 + 1) (by omega),
        show (n + 1 + 1) / 3 = (n + 1) / 3 + 1 by omega]

/-- The interpreter advances both pointers by 3-adic successor. On the
naturals that is ordinary increment, so a code pointer that starts at zero
visits `0, 1, 2, …` and its residues visit `0, 1, 2, …` modulo 282. -/
theorem succ_ofNat (n : Nat) : (Value.ofNat n).succ = Value.ofNat (n + 1) := by
  show (match Value.succTrits (Value.ofNat n).lead (Value.ofNat n).low with
    | (lead, low) => Value.mk' lead low) = Value.ofNat (n + 1)
  rw [ofNat_eq n]
  show (match Value.succTrits .t0 (trits3 n) with
    | (lead, low) => Value.mk' lead low) = Value.ofNat (n + 1)
  rw [succTrits_trits3 n]
  exact mk'_trits3 (n + 1)

/-! ## Obstruction one: self-encryption

After an instruction executes, the word at `c` is replaced by its image
under `xlat2`. Malbolge's table has no fixed point, and the 94 printable
codes `33..126` are 94 consecutive naturals, hence pairwise distinct
modulo 94. Put together: the opcode a code cell decodes to is *different*
every single time that cell executes.

That is the whole difficulty of Malbolge programming, and Unshackled
inherits it unchanged. It rules out the obvious compilation strategy, a
loop whose body is a fixed instruction sequence, and forces every loop to
be assembled from cells whose orbit under `xlat2` returns them to their
starting word after a whole number of passes. -/

set_option maxRecDepth 8000 in
/-- Encryption keeps a printable word printable, so a code cell that starts
printable stays printable for the whole run. -/
theorem encrypt_mem_range : ∀ i, i < 94 → 33 ≤ encrypt (33 + i) ∧ encrypt (33 + i) ≤ 126 := by
  decide

set_option maxRecDepth 8000 in
/-- Malbolge's encryption table has no fixed point. -/
theorem encrypt_ne_self_range : ∀ i, i < 94 → encrypt (33 + i) ≠ 33 + i := by
  decide

theorem encrypt_range {w : Nat} (h₁ : 33 ≤ w) (h₂ : w ≤ 126) :
    33 ≤ encrypt w ∧ encrypt w ≤ 126 := by
  have h := encrypt_mem_range (w - 33) (by omega)
  rwa [show 33 + (w - 33) = w by omega] at h

theorem encrypt_ne_self {w : Nat} (h₁ : 33 ≤ w) (h₂ : w ≤ 126) : encrypt w ≠ w := by
  have h := encrypt_ne_self_range (w - 33) (by omega)
  rwa [show 33 + (w - 33) = w by omega] at h

/-- The printable codes are 94 consecutive naturals, so shifting by an
address residue and reducing modulo 94 is injective on them. -/
theorem opcode_inj {a b m : Nat} (ha₁ : 33 ≤ a) (ha₂ : a ≤ 126)
    (hb₁ : 33 ≤ b) (hb₂ : b ≤ 126) (h : (a + m) % 94 = (b + m) % 94) : a = b := by
  omega

/-- **A code cell never shows the same opcode twice.** At any address, the
opcode of a printable word and the opcode of its encryption differ. -/
theorem opcode_ne_encrypt {w : Nat} (h₁ : 33 ≤ w) (h₂ : w ≤ 126) (m : Nat) :
    (encrypt w + m) % 94 ≠ (w + m) % 94 := by
  intro h
  obtain ⟨he₁, he₂⟩ := encrypt_range h₁ h₂
  exact encrypt_ne_self h₁ h₂ (opcode_inj he₁ he₂ h₁ h₂ h)

/-- The opcode of each instruction: a left inverse of `Instr.ofOpcode?`.
`outOfBounds` is not an opcode at all and is sent to a number that decodes
to nothing. -/
def opcodeOf : Instr → Nat
  | .jmp => 4
  | .out => 5
  | .inp => 23
  | .rotr => 39
  | .movd => 40
  | .crazy => 62
  | .nop => 68
  | .halt => 81
  | .outOfBounds => 0

theorem opcodeOf_ofOpcode? {q : Nat} {i : Instr} (h : Instr.ofOpcode? q = some i) :
    opcodeOf i = q := by
  unfold Instr.ofOpcode? at h
  split at h <;> simp_all [opcodeOf] <;> subst_vars <;> rfl

theorem decode_ofNat {w : Nat} (h₁ : 33 ≤ w) (h₂ : w ≤ 126) (m : Nat) :
    decode (Value.ofNat w) m = (Instr.ofOpcode? ((w + m) % 94)).getD .nop := by
  unfold decode
  rw [printableCode?_ofNat h₁ h₂]

/-- The instruction form of `opcode_ne_encrypt`: **no cell executes the
same non-`nop` instruction on two consecutive executions.** A Malbolge
Unshackled loop cannot be a straight repetition of its body; it has to be a
cycle through the encryption table's orbits. -/
theorem decode_encrypt_ne {w : Nat} (h₁ : 33 ≤ w) (h₂ : w ≤ 126) {m : Nat}
    (hne : decode (Value.ofNat w) m ≠ .nop) :
    decode (Value.ofNat (encrypt w)) m ≠ decode (Value.ofNat w) m := by
  obtain ⟨he₁, he₂⟩ := encrypt_range h₁ h₂
  rw [decode_ofNat h₁ h₂, decode_ofNat he₁ he₂] at *
  intro hEq
  -- the word's own opcode names a real instruction
  cases hw : Instr.ofOpcode? ((w + m) % 94) with
  | none => rw [hw] at hne; exact hne rfl
  | some i =>
    rw [hw] at hne hEq
    cases hc : Instr.ofOpcode? ((encrypt w + m) % 94) with
    | none => rw [hc] at hEq; exact hne hEq.symm
    | some j =>
      rw [hc] at hEq
      simp only [Option.getD_some] at hEq
      subst hEq
      exact opcode_ne_encrypt h₁ h₂ m
        ((opcodeOf_ofOpcode? hc).symm.trans (opcodeOf_ofOpcode? hw))

/-! ## A step-level reading of the interpreter

`exec` is one recursive definition with the whole loop body inline. These
three lemmas are the only way the rest of the development looks at it: one
per exit from the dispatch. Together they cover every case, so a proof
about a run is a proof by induction over them. -/

theorem exec_hang {s : State} (fuel : Nat)
    (h : decode (s.mem.get s.c) s.c.modClass = .outOfBounds) :
    exec (fuel + 1) s = exec fuel s := by
  rw [exec]
  simp only [h]

theorem exec_halt {s : State} (fuel : Nat)
    (h : decode (s.mem.get s.c) s.c.modClass = .halt) :
    exec (fuel + 1) s = (s, Exit.halted) := by
  rw [exec]
  simp only [h]

/-- The ordinary case: dispatch, execute, encrypt the word now at `c`, then
advance both pointers by 3-adic successor. Note that `c` is read *after*
the instruction, so a jump encrypts its target rather than itself. -/
theorem exec_step {s s' : State} {instr : Instr} {code : Nat} (fuel : Nat)
    (h : decode (s.mem.get s.c) s.c.modClass = instr)
    (h₁ : instr ≠ .outOfBounds) (h₂ : instr ≠ .halt)
    (hstep : step instr s = .ok s')
    (hcode : printableCode? (s'.mem.get s'.c) = some code) :
    exec (fuel + 1) s =
      exec fuel { s' with mem := s'.mem.set s'.c (Value.ofNat (encrypt code)),
                          c := s'.c.succ, d := s'.d.succ } := by
  rw [exec]
  simp only [h]
  cases instr with
  | outOfBounds => exact absurd rfl h₁
  | halt => exact absurd rfl h₂
  | jmp => simp only [hstep, hcode]
  | out => simp only [hstep, hcode]
  | inp => simp only [hstep, hcode]
  | rotr => simp only [hstep, hcode]
  | movd => simp only [hstep, hcode]
  | crazy => simp only [hstep, hcode]
  | nop => simp only [hstep, hcode]

/-! ## Obstruction two: the memory fill is not executable

The loader stores the program's characters at `0, 1, 2, …` and then covers
every remaining address with Malbolge's `mem[i] = crz mem[i-1] mem[i-2]`
iteration, whose 6-periodicity lets Johansen give the whole of the 3-adic
integers a value. The six-entry table this produces is not code: the crazy
operation of two values whose repeating trit is `0` has repeating trit `1`,
and from the third term of the iteration onward the repeating trits
alternate `1, 0, 1, 0, …`. Three of the six entries are therefore not
naturals at all, so they are not printable, so executing one hangs.

The consequence for a compiler is that a Malbolge Unshackled program cannot
run off its own end into an infinite supply of fresh instructions. Whatever
loops has to loop inside the loaded image, over cells that have already
executed, which is what makes obstruction one bite. -/

/-- The repeating trit of the `k`-th term of the memory fill, as a function
of the two seeds' repeating trits alone. -/
def leadAt : Nat → Trit → Trit → Trit
  | 0, a, _ => a
  | i + 1, a, b => leadAt i b (crzTrit b a)

theorem crz_lead (a b : Value) : (Value.crz a b).lead = crzTrit a.lead b.lead := rfl

theorem lead_getD_crzSeq : ∀ (i k : Nat) (p q : Value), i < k →
    ((crzSeq k p q).getD i Value.zero).lead = leadAt i p.lead q.lead := by
  intro i
  induction i with
  | zero =>
    intro k p q h
    match k, h with
    | k + 1, _ => rfl
  | succ i ih =>
    intro k p q h
    match k, h with
    | k + 1, h =>
      rw [crzSeq, List.getD_cons_succ, ih k q (Value.crz q p) (by omega), crz_lead]
      rfl

/-- From the third term onward the repeating trits alternate, so every
even-indexed term of a fill seeded by two naturals is not a natural. Only
the indices the loader can actually phase to are needed, and they all lie
below 13. -/
theorem leadAt_even :
    ∀ i, i < 13 → 2 ≤ i → i % 2 = 0 → leadAt i .t0 .t0 = Trit.t1 := by decide

/-- A value whose repeating trit is not `0` denotes no natural, hence is
not a printable word, hence hangs the interpreter when executed. -/
theorem printableCode?_of_lead_ne {v : Value} (h : v.lead ≠ .t0) :
    printableCode? v = none := by
  unfold printableCode? Value.toNat?
  rw [if_neg h]

theorem decode_of_lead_ne {v : Value} (h : v.lead ≠ .t0) (m : Nat) :
    decode v m = .outOfBounds := by
  unfold decode
  rw [printableCode?_of_lead_ne h]

theorem restTable_getD (p q : Value) (m j : Nat) (hj : j < 6) :
    (restTable p q m).getD j Value.zero =
      (crzSeq (2 + (10 - m % 6) % 6 + 6) p q).getD (2 + (10 - m % 6) % 6 + j)
        Value.zero := by
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
  rcases hj' with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [restTable, Array.getD]

/-- **The fill cannot be executed.** For every seeding of the loader's
memory fill by two naturals, and at every phase, one of the six residue
classes holds a value that is not a printable word. An address the loader
never wrote is, for at least one class in six, a cell whose execution
hangs. -/
theorem restTable_not_printable {p q : Value} (hp : p.lead = .t0) (hq : q.lead = .t0)
    (m : Nat) :
    ∃ j, j < 6 ∧ printableCode? ((restTable p q m).getD j Value.zero) = none := by
  have hm : m % 6 = 0 ∨ m % 6 = 1 ∨ m % 6 = 2 ∨ m % 6 = 3 ∨ m % 6 = 4 ∨ m % 6 = 5 := by
    omega
  -- the phase decides which of the two lowest entries has an even index
  have key : ∀ j, j < 6 → 2 + (10 - m % 6) % 6 + j < 13 →
      2 ≤ 2 + (10 - m % 6) % 6 + j → (2 + (10 - m % 6) % 6 + j) % 2 = 0 →
      ∃ j, j < 6 ∧ printableCode? ((restTable p q m).getD j Value.zero) = none := by
    intro j hj hlt hge heven
    refine ⟨j, hj, ?_⟩
    rw [restTable_getD p q m j hj]
    refine printableCode?_of_lead_ne ?_
    rw [lead_getD_crzSeq _ _ p q (by omega), hp, hq,
      leadAt_even _ hlt hge heven]
    simp
  rcases hm with h | h | h | h | h | h
  · exact key 0 (by omega) (by omega) (by omega) (by omega)
  · exact key 1 (by omega) (by omega) (by omega) (by omega)
  · exact key 0 (by omega) (by omega) (by omega) (by omega)
  · exact key 1 (by omega) (by omega) (by omega) (by omega)
  · exact key 0 (by omega) (by omega) (by omega) (by omega)
  · exact key 1 (by omega) (by omega) (by omega) (by omega)

/-! ## The instruction at an address

Putting the arithmetic and the decoder together: at a natural address `a`,
a printable word `w` is the instruction with opcode `(w + a) mod 94`. This
is the equation an assembler for the language has to solve, and it says
that the *address* of a cell decides which instructions it can hold. -/

theorem decode_congr_mod94 {v : Value} {m m' : Nat} (h : m % 94 = m' % 94) :
    decode v m = decode v m' := by
  unfold decode
  rcases hv : printableCode? v with _ | n
  · rfl
  · show (Instr.ofOpcode? ((n + m) % 94)).getD .nop
        = (Instr.ofOpcode? ((n + m') % 94)).getD .nop
    rw [show (n + m) % 94 = (n + m') % 94 by omega]

/-- The instruction a printable word denotes at a natural address. -/
theorem decode_at_ofNat {w : Nat} (h₁ : 33 ≤ w) (h₂ : w ≤ 126) (a : Nat) :
    decode (Value.ofNat w) (Value.ofNat a).modClass
      = (Instr.ofOpcode? ((w + a) % 94)).getD .nop := by
  rw [modClass_ofNat, decode_ofNat h₁ h₂]
  congr 2
  omega

/-! ## What a loop can be made of

Obstruction one says a cell's opcode changes every time it executes, so the
only cells whose behaviour a proof can follow for an unbounded run are
those whose orbit under `xlat2` is short. The table has one orbit of length
two, `70 ↔ 74`, and a cell holding one of those two words alternates
between exactly two opcodes forever.

`alternatingCell` records, for each of the eight instructions, an address
residue and a starting word at which that cell is the instruction on its
odd executions and a no-op on its even ones. Every entry uses the word 74,
and `alternatingCell_spec` checks both halves in the kernel.

Two things are worth reading off the table. First, every instruction in the
language is available this way, so instruction *choice* is never the
obstacle; the residue is forced modulo 94, so instruction *placement* is.
Second, the complementary phase is not loadable: at each of these residues
the word 70 decodes to no instruction at all, and the loader rejects a
program containing one. An alternating cell therefore always fires on its
first execution and no-ops on its second, never the other way round, which
is why a loop cannot be built by pairing two half-bodies of opposite
phase. -/

theorem encrypt_seventy : encrypt 70 = 74 := by decide

theorem encrypt_seventyfour : encrypt 74 = 70 := by decide

/-- An address residue and a starting word for each instruction, drawn from
the two-element orbit of the encryption table. -/
def alternatingCell : Instr → Nat × Nat
  | .jmp => (24, 74)
  | .out => (25, 74)
  | .inp => (43, 74)
  | .rotr => (59, 74)
  | .movd => (60, 74)
  | .crazy => (82, 74)
  | .nop => (88, 74)
  | .halt => (7, 74)
  | .outOfBounds => (0, 74)

set_option maxRecDepth 8000 in
/-- Each entry of the table does what it claims: the cell decodes to its
instruction, its encryption decodes to no instruction at all, and the pair
is a two-cycle, so the behaviour repeats with period two. The
`outOfBounds` row is not an instruction and is excluded. -/
theorem alternatingCell_spec (i : Instr) (h : i ≠ .outOfBounds) :
    decode (Value.ofNat (alternatingCell i).2) (alternatingCell i).1 = i
    ∧ Instr.ofOpcode? ((encrypt (alternatingCell i).2 + (alternatingCell i).1) % 94)
        = none := by
  cases i <;> first | exact absurd rfl h | decide

/-! ## The hang is a real hang

`exec` models Johansen's `hang` as a fuel-consuming spin. Nothing in the
state changes, so a run that reaches an unprintable word never halts, never
errors, and never produces another byte: it only runs out of fuel. -/

theorem exec_of_hang {s : State} (h : decode (s.mem.get s.c) s.c.modClass = .outOfBounds)
    (fuel : Nat) : exec fuel s = (s, Exit.outOfFuel) := by
  induction fuel with
  | zero => rfl
  | succ f ih => rw [exec_hang f h, ih]

/-! ## Memory behaves like a function

`Memory` stores the written cells in a `Std.HashMap` and computes the rest
from the address's residue. The two laws below are the only facts about it
any proof needs, and after them no proof has to look inside a hash map
again. They need the container laws for `Value` as a key, which hold
because its `BEq` is `decide (· = ·)` and its `Hashable` is a fold over the
same data that `DecidableEq` compares. -/

instance : LawfulBEq Value where
  eq_of_beq h := of_decide_eq_true h
  rfl := by intro a; exact decide_eq_true rfl

instance : LawfulHashable Value where
  hash_eq a b h := by rw [eq_of_beq h]

theorem get_set_self (m : Memory) (a v : Value) : (m.set a v).get a = v := by
  simp [Memory.set, Memory.get]

theorem get_set_ne (m : Memory) {a b : Value} (h : a ≠ b) (v : Value) :
    (m.set a v).get b = m.get b := by
  simp [Memory.set, Memory.get, Std.HashMap.getD_insert, h]

/-! ## The one instruction that does not destroy itself

`exec` reads the word to encrypt *after* the instruction has run. Every
instruction leaves `c` where it was, so every instruction overwrites its own
cell with its encryption, and `decode_encrypt_ne` then says it cannot do the
same thing next time. `jmp` is the exception: it has already moved `c` to
its target, so the encryption falls on the target and the jumping cell is
left exactly as it was.

This is what makes a loop possible at all in the Malbolge family. A `jmp`
cell is stable under its own execution, so it can fire unboundedly often;
every other cell in a loop is on a clock, and the loop closes only after
each of them has come back round its orbit. It is also why `exec_step`
takes the trouble to state the encryption at `s'.c` rather than `s.c`. -/

/-- A `jmp` step, with the encryption written where it actually lands. -/
theorem exec_jmp {s : State} {code : Nat} (fuel : Nat)
    (h : decode (s.mem.get s.c) s.c.modClass = .jmp)
    (hcode : printableCode? (s.mem.get (s.mem.get s.d)) = some code) :
    exec (fuel + 1) s =
      exec fuel
        { s with mem := s.mem.set (s.mem.get s.d) (Value.ofNat (encrypt code)),
                 c := (s.mem.get s.d).succ,
                 d := s.d.succ } :=
  exec_step fuel h (by simp) (by simp) rfl hcode

/-- **A `jmp` cell survives its own execution.** Provided it does not jump
to itself, the word at the jumping cell is the same after the step as
before, so the cell decodes to `jmp` again next time it is reached. -/
theorem jmp_cell_stable {s : State} {code : Nat} (hne : s.mem.get s.d ≠ s.c) :
    (s.mem.set (s.mem.get s.d) (Value.ofNat (encrypt code))).get s.c
      = s.mem.get s.c :=
  get_set_ne s.mem hne _

/-- Read together with `decode_encrypt_ne`, this is the dichotomy that
governs Malbolge control flow: an executed cell is overwritten by its own
encryption unless it is a `jmp`, in which case its target is overwritten
instead. -/
theorem exec_nonjmp_encrypts_self {s s' : State} {instr : Instr} {code : Nat}
    (fuel : Nat)
    (h : decode (s.mem.get s.c) s.c.modClass = instr)
    (h₁ : instr ≠ .outOfBounds) (h₂ : instr ≠ .halt)
    (hstep : step instr s = .ok s') (hc : s'.c = s.c)
    (hcode : printableCode? (s'.mem.get s'.c) = some code) :
    ((exec (fuel + 1) s).1 = (exec fuel
        { s' with mem := s'.mem.set s'.c (Value.ofNat (encrypt code)),
                  c := s'.c.succ, d := s'.d.succ }).1)
    ∧ (s'.mem.set s'.c (Value.ofNat (encrypt code))).get s.c
        = Value.ofNat (encrypt code) := by
  refine ⟨by rw [exec_step fuel h h₁ h₂ hstep hcode], ?_⟩
  rw [← hc]
  exact get_set_self _ _ _

/-! ## Iterating the interpreter

`exec` runs to completion, so it is the wrong shape for talking about a
loop. `step1` is one iteration as a partial function, `none` meaning the run
stopped (halted, or hit a runtime error). The out-of-bounds spin is `some s`
rather than `none`, because that is what the interpreter does: it keeps
going without changing anything.

`step1_sound` is the only bridge back to `exec`, and everything below goes
through it, so nothing here can quietly disagree with the reference
semantics. -/

/-- One iteration of the interpreter's loop, as a partial function on
states. Mirrors the body of `exec`; `step1_sound` proves they agree. -/
def step1 (s : State) : Option State :=
  match decode (s.mem.get s.c) s.c.modClass with
  | .outOfBounds => some s
  | .halt => none
  | instr =>
    match step instr s with
    | .error _ => none
    | .ok s' =>
      match printableCode? (s'.mem.get s'.c) with
      | none => none
      | some code =>
        some { s' with mem := s'.mem.set s'.c (Value.ofNat (encrypt code)),
                       c := s'.c.succ, d := s'.d.succ }

/-- The generic case of `step1_sound`: everything that is neither the spin
nor the halt. Factored out so the dispatch below is nine one-liners. -/
private theorem step1_sound_generic {s s' : State} {instr : Instr}
    (hd : decode (s.mem.get s.c) s.c.modClass = instr)
    (h₁ : instr ≠ .outOfBounds) (h₂ : instr ≠ .halt)
    (h : (match step instr s with
          | .error _ => none
          | .ok s₁ =>
            match printableCode? (s₁.mem.get s₁.c) with
            | none => none
            | some code =>
              some { s₁ with mem := s₁.mem.set s₁.c (Value.ofNat (encrypt code)),
                             c := s₁.c.succ, d := s₁.d.succ }) = some s')
    (fuel : Nat) : exec (fuel + 1) s = exec fuel s' := by
  cases hstep : step instr s with
  | error e => rw [hstep] at h; simp at h
  | ok s₁ =>
    rw [hstep] at h
    dsimp only at h
    cases hp : printableCode? (s₁.mem.get s₁.c) with
    | none => rw [hp] at h; simp at h
    | some code =>
      rw [hp] at h
      simp only [Option.some.injEq] at h
      subst h
      exact exec_step fuel hd h₁ h₂ hstep hp

theorem step1_sound {s s' : State} (h : step1 s = some s') (fuel : Nat) :
    exec (fuel + 1) s = exec fuel s' := by
  unfold step1 at h
  cases hd : decode (s.mem.get s.c) s.c.modClass <;> rw [hd] at h
  case outOfBounds =>
    simp only [Option.some.injEq] at h
    subst h
    exact exec_hang fuel hd
  case halt => simp at h
  all_goals exact step1_sound_generic hd (by simp) (by simp) h fuel

/-- Iterate `step1`. `none` means the run stopped somewhere along the way. -/
def run? : Nat → State → Option State
  | 0, s => some s
  | n + 1, s => (step1 s).bind (run? n)

/-- A run that survives `n` iterations has not finished after `n` units of
fuel, and the state it reaches is the one `exec` reports. -/
theorem exec_of_run? : ∀ {n : Nat} {s t : State}, run? n s = some t →
    exec n s = (t, Exit.outOfFuel)
  | 0, s, t, h => by
    simp only [run?, Option.some.injEq] at h
    subst h
    rfl
  | n + 1, s, t, h => by
    simp only [run?] at h
    cases hs : step1 s with
    | none => rw [hs] at h; simp at h
    | some s' =>
      rw [hs] at h
      simp only [Option.bind_some] at h
      rw [step1_sound hs n]
      exact exec_of_run? h

/-! ## The loop gadget

**A step invariant that always admits a successor proves non-termination.**
This is the shape every loop proof for this language takes: exhibit a set of
states closed under one iteration and containing the start, and the run is
shown to consume every fuel bound without ever reporting a result.

The invariant is the interesting part and is supplied per program. A
periodic run gives one for free (the finitely many states of the period); a
data-driven loop gives a larger one. Nothing here needs the invariant to be
finite, decidable, or even to mention memory. -/

/-- The reusable non-termination theorem. -/
theorem neverHalts_of_invariant {P : State → Prop}
    (hstep : ∀ s, P s → ∃ s', step1 s = some s' ∧ P s')
    {s : State} (hs : P s) (n : Nat) : (exec n s).2 = Exit.outOfFuel := by
  have key : ∀ n s, P s → ∃ t, run? n s = some t ∧ P t := by
    intro n
    induction n with
    | zero => intro s hs; exact ⟨s, rfl, hs⟩
    | succ n ih =>
      intro s hs
      obtain ⟨s', h₁, h₂⟩ := hstep s hs
      obtain ⟨t, ht, hPt⟩ := ih s' h₂
      exact ⟨t, by simp [run?, h₁, ht], hPt⟩
  obtain ⟨t, ht, _⟩ := key n s hs
  rw [exec_of_run? ht]

/-- The initial state of a run, spelled out, so that a program-level
invariant has something concrete to hold at. -/
def initialState (img : Image) (input : Input) : State :=
  { mem := img.mem, input := input, rotWidth := minRotWidth }

theorem evalImage_eq_exec (img : Image) (input : Input) (fuel : Nat) :
    evalImage {} img input fuel =
      let (s, e) := exec fuel (initialState img input)
      { output := s.output, exit := e } := rfl

/-- **A loop invariant makes the whole program non-halting**, stated where
the language interface can see it: for every fuel bound the run reports
`outOfFuel`, so no run of this image on this input ever halts or errors. -/
theorem image_neverHalts {P : State → Prop}
    (hstep : ∀ s, P s → ∃ s', step1 s = some s' ∧ P s')
    {img : Image} {input : Input} (hs : P (initialState img input)) (n : Nat) :
    (evalImage {} img input n).exit = Exit.outOfFuel := by
  show (exec n (initialState img input)).2 = Exit.outOfFuel
  exact neverHalts_of_invariant hstep hs n

/-- The same fact in the vocabulary the computability interface uses: the
image never halts, for any fuel. -/
theorem not_halts_of_invariant {P : State → Prop}
    (hstep : ∀ s, P s → ∃ s', step1 s = some s' ∧ P s')
    {img : Image} {input : Input} (hs : P (initialState img input)) :
    ¬ ∃ n, (ProgLang.run (L := MalbolgeUnshackledLang) img input n).exit = Exit.halted := by
  rintro ⟨n, hn⟩
  rw [show ProgLang.run (L := MalbolgeUnshackledLang) img input n
        = evalImage {} img input n from rfl, image_neverHalts hstep hs n] at hn
  exact Exit.noConfusion hn

/-! ## The crazy operation consumes its operand

`p` writes the result to `mem[d]`, the very cell it read the operand from.
So the constant a compiler places for one crazy operation is **destroyed by
using it**, and a value cannot be built by returning to a cell and combining
against it repeatedly. Two operations against two constants set the
accumulator to anything (`crz_two_steps`), and they leave two spent cells
behind.

The second thing this lemma pins down is why `d` must differ from `c`. The
crazy operation writes at `d`; the encryption that follows reads at `c`. If
they coincide the encryption sees the result of the crazy operation, which
is essentially never a printable word, and the interpreter crashes. That is
the runtime error the test suite records as "a crazy-operated word has no
encryption", and it is why the two pointers have to be separated before any
arithmetic happens. -/

/-- One `p` step, with both writes it performs spelled out: the operand cell
is overwritten by the result, and the code cell by its own encryption. -/
theorem exec_crazy {s : State} {code : Nat} (fuel : Nat)
    (h : decode (s.mem.get s.c) s.c.modClass = .crazy)
    (hne : s.d ≠ s.c)
    (hcode : printableCode? (s.mem.get s.c) = some code) :
    exec (fuel + 1) s =
      exec fuel
        { s with a := Value.crz s.a (s.mem.get s.d),
                 mem := (s.mem.set s.d (Value.crz s.a (s.mem.get s.d))).set s.c
                          (Value.ofNat (encrypt code)),
                 c := s.c.succ, d := s.d.succ } := by
  refine exec_step fuel h (by simp) (by simp) rfl ?_
  show printableCode? ((s.mem.set s.d (Value.crz s.a (s.mem.get s.d))).get s.c) = some code
  rw [get_set_ne _ hne]
  exact hcode

/-- The operand cell afterwards holds the result, not the constant that was
there before: **using a constant destroys it**. -/
theorem crazy_consumes_operand (s : State) :
    (s.mem.set s.d (Value.crz s.a (s.mem.get s.d))).get s.d
      = Value.crz s.a (s.mem.get s.d) :=
  get_set_self _ _ _

/-! ## What a loadable jump table can look like

`jmp_cell_stable` says a `jmp` cell survives its own execution, so the way
to loop in this language is a stable `jmp` reading a *table* of targets:
`d` walks forward one cell per step, and each entry either sends control
back into the loop or out of it. `cat.mu` is built exactly this way, and
its table is read at consecutive addresses.

Consecutive is close to forced. A table entry is a memory cell, and in a
program the loader accepted, every cell's word must decode to one of the
eight opcodes at its own address. So if the same target value has to appear
at two addresses `g` apart, the two opcodes it produces differ by `g`
modulo 94, and `g` must be a difference of two opcodes. Only 43 of the 94
gaps are, and among the small ones only 0, 1 and 6: in particular **not 2**,
which is what a naive two-jump loop body would need. -/

/-- The eight opcodes, listed so the arithmetic below is decidable. -/
def opcodes : List Nat := [4, 5, 23, 39, 40, 62, 68, 81]

theorem mem_opcodes_range : ∀ q, q < 94 → (Instr.ofOpcode? q).isSome = true → q ∈ opcodes := by
  decide

/-- The gaps at which one word can sit twice over and still load. -/
def loadableGaps : List Nat :=
  opcodes.flatMap fun p => opcodes.map fun q => (q + 94 - p) % 94

theorem gaps_sound : ∀ p ∈ opcodes, ∀ q ∈ opcodes, (q + 94 - p) % 94 ∈ loadableGaps := by
  decide

/-- **The jump-table spacing law.** If a loadable program holds the same
word at two addresses `g` apart, `g` modulo 94 is a difference of two
opcodes. -/
theorem gap_of_repeated_word {v a g : Nat}
    (h₁ : (Instr.ofOpcode? ((v + a) % 94)).isSome = true)
    (h₂ : (Instr.ofOpcode? ((v + a + g) % 94)).isSome = true) :
    g % 94 ∈ loadableGaps := by
  have hp := mem_opcodes_range _ (Nat.mod_lt _ (by omega)) h₁
  have hq := mem_opcodes_range _ (Nat.mod_lt _ (by omega)) h₂
  have hmem := gaps_sound _ hp _ hq
  rwa [show ((v + a + g) % 94 + 94 - (v + a) % 94) % 94 = g % 94 by omega] at hmem

/-- **Two cells apart is impossible.** No two of the eight opcodes differ
by 2, so the shortest jump-table loop a compiler might reach for, one that
reads its return target at `d` and again at `d + 2`, cannot be loaded. This
is why `cat.mu` reads its table at consecutive addresses instead. -/
theorem no_repeated_word_gap_two {v a : Nat}
    (h₁ : (Instr.ofOpcode? ((v + a) % 94)).isSome = true)
    (h₂ : (Instr.ofOpcode? ((v + a + 2) % 94)).isSome = true) : False := by
  have h := gap_of_repeated_word h₁ h₂
  revert h
  decide

/-! ## A Malbolge Unshackled program that provably loops for ever

Everything above says what a loop has to look like. This section builds one
and discharges the invariant, so LangLib actually asserts that a particular
program in this language never halts.

The loop is three steps long and lives at three addresses:

* **155** holds the word 37. At an address congruent to 61 modulo 94 that
  decodes to `jmp`, and a `jmp` never encrypts itself, so this cell is
  *never written* for the whole run. It fires twice per cycle.
* **154** holds the word 74. At an address congruent to 60 modulo 94 that
  decodes to `movd`. It is encrypted twice per cycle, once by executing and
  once by being the first jump's target, and `74 ↦ 70 ↦ 74` is the
  two-cycle of `xlat2`, so it comes back every cycle. This is the trick:
  a cell that is both executed and jumped onto advances twice.
* **153** is the second jump's target. It is encrypted once per cycle, so
  its word wanders through a long orbit. The invariant does not track it:
  encryption keeps a printable word printable, and printable is all this
  cell has to be.

The jump table is at 198 and 199, read at consecutive `d`, which is the
only short spacing `gap_of_repeated_word` leaves available. Cell 200 holds
197, three less than its own address, which is what returns `d` to where it
started.

The cycle is `movd` at 154, then `jmp` at 155 twice: the first jump lands
back on 155 (its target 154 is one below), the second lands on 154. -/

namespace Loop

/-- The part of the invariant that every phase shares. It constrains only
memory, so it survives the register updates unread. -/
structure Frame (m : Memory) : Prop where
  /-- 155 holds the `jmp`, and nothing ever writes here. -/
  jmpCell : m.get (Value.ofNat 155) = Value.ofNat 37
  /-- First table entry: jump to 154, landing back on 155. -/
  table₀ : m.get (Value.ofNat 198) = Value.ofNat 154
  /-- Second table entry: jump to 153, landing on 154. -/
  table₁ : m.get (Value.ofNat 199) = Value.ofNat 153
  /-- `movd` reads this and sends `d` three back, to 197, whence two
  increments return it to 200 at the top of the next cycle. -/
  reset : m.get (Value.ofNat 200) = Value.ofNat 197
  /-- The scratch cell only has to stay printable, which encryption
  guarantees. Its word is not tracked. -/
  scratch : ∃ w, 33 ≤ w ∧ w ≤ 126 ∧ m.get (Value.ofNat 153) = Value.ofNat w

/-- Top of the cycle: about to run `movd` at 154. -/
def Phase₀ (s : State) : Prop :=
  Frame s.mem ∧ s.c = Value.ofNat 154 ∧ s.d = Value.ofNat 200
    ∧ s.mem.get (Value.ofNat 154) = Value.ofNat 74

/-- About to run the first `jmp`, with 154 encrypted once. -/
def Phase₁ (s : State) : Prop :=
  Frame s.mem ∧ s.c = Value.ofNat 155 ∧ s.d = Value.ofNat 198
    ∧ s.mem.get (Value.ofNat 154) = Value.ofNat 70

/-- About to run the second `jmp`, with 154 encrypted back to 74. -/
def Phase₂ (s : State) : Prop :=
  Frame s.mem ∧ s.c = Value.ofNat 155 ∧ s.d = Value.ofNat 199
    ∧ s.mem.get (Value.ofNat 154) = Value.ofNat 74

/-- The loop invariant. -/
def Looping (s : State) : Prop := Phase₀ s ∨ Phase₁ s ∨ Phase₂ s

/-- A write anywhere the frame does not mention leaves it standing. -/
theorem Frame.set {m : Memory} (h : Frame m) {a v : Value}
    (h₁ : a ≠ Value.ofNat 155) (h₂ : a ≠ Value.ofNat 198)
    (h₃ : a ≠ Value.ofNat 199) (h₄ : a ≠ Value.ofNat 200)
    (h₅ : a ≠ Value.ofNat 153) : Frame (m.set a v) := by
  obtain ⟨j, t₀, t₁, r, w, hw₁, hw₂, hw₃⟩ := h
  exact ⟨by rw [get_set_ne _ h₁]; exact j, by rw [get_set_ne _ h₂]; exact t₀,
    by rw [get_set_ne _ h₃]; exact t₁, by rw [get_set_ne _ h₄]; exact r,
    ⟨w, hw₁, hw₂, by rw [get_set_ne _ h₅]; exact hw₃⟩⟩

/-- Writing a printable word to the scratch cell also leaves it standing:
this is the write the second jump performs every cycle. -/
theorem Frame.setScratch {m : Memory} (h : Frame m) {w : Nat}
    (h₁ : 33 ≤ w) (h₂ : w ≤ 126) :
    Frame (m.set (Value.ofNat 153) (Value.ofNat w)) := by
  obtain ⟨j, t₀, t₁, r, _⟩ := h
  exact ⟨by rw [get_set_ne _ (by decide)]; exact j,
    by rw [get_set_ne _ (by decide)]; exact t₀,
    by rw [get_set_ne _ (by decide)]; exact t₁,
    by rw [get_set_ne _ (by decide)]; exact r,
    ⟨w, h₁, h₂, get_set_self _ _ _⟩⟩

theorem step_phase₀ {s : State} (h : Phase₀ s) : ∃ s', step1 s = some s' ∧ Phase₁ s' := by
  obtain ⟨hf, hc, hd, h154⟩ := h
  have hword : s.mem.get s.c = Value.ofNat 74 := by rw [hc]; exact h154
  have hnd : s.mem.get s.d = Value.ofNat 197 := by rw [hd]; exact hf.reset
  have hdec : decode (s.mem.get s.c) s.c.modClass = Instr.movd := by
    rw [hword, hc, decode_at_ofNat (by omega) (by omega)]
    decide
  cases hst : step Instr.movd s with
  | error e =>
    exfalso
    simp only [step, hnd] at hst
    split at hst <;> simp at hst
  | ok s₁ =>
    have hfields : s₁.mem = s.mem ∧ s₁.c = s.c ∧ s₁.d = Value.ofNat 197 := by
      simp only [step, hnd] at hst
      split at hst <;>
        · injection hst with hst
          subst hst
          exact ⟨rfl, rfl, rfl⟩
    obtain ⟨hm, hcc, hdd⟩ := hfields
    have hc₁ : s₁.c = Value.ofNat 154 := by rw [hcc, hc]
    have hpc : printableCode? (s₁.mem.get s₁.c) = some 74 := by
      rw [hm, hcc, hword]
      exact printableCode?_ofNat (by omega) (by omega)
    have hstep1 : step1 s = some { s₁ with mem := s₁.mem.set s₁.c (Value.ofNat (encrypt 74)), c := s₁.c.succ, d := s₁.d.succ } := by
      unfold step1
      rw [hdec]
      dsimp only
      rw [hst]
      dsimp only
      rw [hpc]
    refine ⟨_, hstep1, ?_, ?_, ?_, ?_⟩
    · show Frame (s₁.mem.set s₁.c (Value.ofNat (encrypt 74)))
      rw [hc₁, hm]
      exact hf.set (by decide) (by decide) (by decide) (by decide) (by decide)
    · show s₁.c.succ = Value.ofNat 155
      rw [hc₁]; exact succ_ofNat 154
    · show s₁.d.succ = Value.ofNat 198
      rw [hdd]; exact succ_ofNat 197
    · show (s₁.mem.set s₁.c (Value.ofNat (encrypt 74))).get (Value.ofNat 154)
        = Value.ofNat 70
      rw [hc₁, get_set_self]
      rfl

theorem step_phase₁ {s : State} (h : Phase₁ s) : ∃ s', step1 s = some s' ∧ Phase₂ s' := by
  obtain ⟨hf, hc, hd, h154⟩ := h
  have hword : s.mem.get s.c = Value.ofNat 37 := by rw [hc]; exact hf.jmpCell
  have hdec : decode (s.mem.get s.c) s.c.modClass = Instr.jmp := by
    rw [hword, hc, decode_at_ofNat (by omega) (by omega)]
    decide
  have htgt : s.mem.get s.d = Value.ofNat 154 := by rw [hd]; exact hf.table₀
  have hpc : printableCode? (s.mem.get (s.mem.get s.d)) = some 70 := by
    rw [htgt, h154]
    exact printableCode?_ofNat (by omega) (by omega)
  have hstep1 : step1 s = some { s with mem := s.mem.set (s.mem.get s.d) (Value.ofNat (encrypt 70)), c := (s.mem.get s.d).succ, d := s.d.succ } := by
    unfold step1
    rw [hdec]
    dsimp only [step]
    rw [hpc]
  refine ⟨_, hstep1, ?_, ?_, ?_, ?_⟩
  · show Frame (s.mem.set (s.mem.get s.d) (Value.ofNat (encrypt 70)))
    rw [htgt]
    exact hf.set (by decide) (by decide) (by decide) (by decide) (by decide)
  · show (s.mem.get s.d).succ = Value.ofNat 155
    rw [htgt]; exact succ_ofNat 154
  · show s.d.succ = Value.ofNat 199
    rw [hd]; exact succ_ofNat 198
  · show (s.mem.set (s.mem.get s.d) (Value.ofNat (encrypt 70))).get (Value.ofNat 154)
      = Value.ofNat 74
    rw [htgt, get_set_self]
    rfl

theorem step_phase₂ {s : State} (h : Phase₂ s) : ∃ s', step1 s = some s' ∧ Phase₀ s' := by
  obtain ⟨hf, hc, hd, h154⟩ := h
  obtain ⟨w, hw₁, hw₂, hw₃⟩ := hf.scratch
  have hword : s.mem.get s.c = Value.ofNat 37 := by rw [hc]; exact hf.jmpCell
  have hdec : decode (s.mem.get s.c) s.c.modClass = Instr.jmp := by
    rw [hword, hc, decode_at_ofNat (by omega) (by omega)]
    decide
  have htgt : s.mem.get s.d = Value.ofNat 153 := by rw [hd]; exact hf.table₁
  have hpc : printableCode? (s.mem.get (s.mem.get s.d)) = some w := by
    rw [htgt, hw₃]
    exact printableCode?_ofNat hw₁ hw₂
  obtain ⟨he₁, he₂⟩ := encrypt_range hw₁ hw₂
  have hstep1 : step1 s = some { s with mem := s.mem.set (s.mem.get s.d) (Value.ofNat (encrypt w)), c := (s.mem.get s.d).succ, d := s.d.succ } := by
    unfold step1
    rw [hdec]
    dsimp only [step]
    rw [hpc]
  refine ⟨_, hstep1, ?_, ?_, ?_, ?_⟩
  · show Frame (s.mem.set (s.mem.get s.d) (Value.ofNat (encrypt w)))
    rw [htgt]
    exact hf.setScratch he₁ he₂
  · show (s.mem.get s.d).succ = Value.ofNat 154
    rw [htgt]; exact succ_ofNat 153
  · show s.d.succ = Value.ofNat 200
    rw [hd]; exact succ_ofNat 199
  · show (s.mem.set (s.mem.get s.d) (Value.ofNat (encrypt w))).get (Value.ofNat 154)
      = Value.ofNat 74
    rw [htgt, get_set_ne _ (by decide)]
    exact h154

/-- The invariant is closed under one iteration. -/
theorem looping_step {s : State} (h : Looping s) : ∃ s', step1 s = some s' ∧ Looping s' := by
  rcases h with h | h | h
  · obtain ⟨s', h₁, h₂⟩ := step_phase₀ h; exact ⟨s', h₁, Or.inr (Or.inl h₂)⟩
  · obtain ⟨s', h₁, h₂⟩ := step_phase₁ h; exact ⟨s', h₁, Or.inr (Or.inr h₂)⟩
  · obtain ⟨s', h₁, h₂⟩ := step_phase₂ h; exact ⟨s', h₁, Or.inl h₂⟩

/-- **A Malbolge Unshackled run that never halts.** From any state in the
loop, every fuel bound is consumed without the interpreter reporting a
result: no halt, no runtime error, for ever. -/
theorem neverHalts {s : State} (h : Looping s) (n : Nat) :
    (exec n s).2 = Exit.outOfFuel :=
  neverHalts_of_invariant (fun _ hs => looping_step hs) h n

end Loop


/-! ## The algebra of the crazy operation

A backend that avoids `rot`, for the reasons in
`docs/malbolge-unshackled/compiler.md`, has exactly one data operation:
`p`, which sets both the accumulator and `mem[d]` to `crz a mem[d]`. Since
the compiler chooses what sits in memory, the question that decides what
such a backend can compute is: **which values can one crazy operation
against a chosen constant reach?**

The answer is the point of this section. `crz` is tritwise, so it is
settled position by position, and reading the table by rows gives

| accumulator trit | results reachable by varying the memory trit |
|---|---|
| 0 | 1, 2 |
| 1 | 0, 2 |
| 2 | 0, 1, 2 |

One operation is therefore not enough: from an accumulator trit of 0 you
can never produce a 0. Two always are, because every row can reach 2, and
the row for 2 reaches everything. `crz_two_steps` below is that argument,
and it is the fact a compiler needs in order to write a computed address
into a jump table, which is what a data-driven branch is made of. -/

/-! ### List helpers

`List.getD l i d` is `l[i]?.getD d`; these four are the only facts about it
the tritwise arguments need. -/

theorem getD_nil (i : Nat) (d : Trit) : ([] : List Trit).getD i d = d := rfl

theorem getD_cons_zero (x : Trit) (xs : List Trit) (d : Trit) :
    (x :: xs).getD 0 d = x := rfl

theorem getD_cons_succ (x : Trit) (xs : List Trit) (i : Nat) (d : Trit) :
    (x :: xs).getD (i + 1) d = xs.getD i d := rfl

theorem getD_lt {l : List Trit} {i : Nat} (h : i < l.length) (d : Trit) :
    l.getD i d = l[i] := by
  simp [List.getD, List.getElem?_eq_getElem h]

theorem getD_ge {l : List Trit} {i : Nat} (h : l.length ≤ i) (d : Trit) :
    l.getD i d = d := by
  simp [List.getD, List.getElem?_eq_none h]

/-! ### `stripLead` and `padTo` are invisible to `trit` -/

theorem getD_stripLead (t : Trit) : ∀ (l : List Trit) (i : Nat),
    (stripLead t l).getD i t = l.getD i t
  | [], _ => rfl
  | x :: xs, i => by
    have ih := getD_stripLead t xs
    show (match stripLead t xs with
      | [] => if x = t then [] else [x]
      | ys => x :: ys).getD i t = (x :: xs).getD i t
    cases hs : stripLead t xs with
    | nil =>
      rw [hs] at ih
      have hxs : ∀ j, xs.getD j t = t := fun j => (ih j).symm.trans (getD_nil j t)
      by_cases hx : x = t
      · rw [if_pos hx]
        cases i with
        | zero => rw [getD_nil, getD_cons_zero, hx]
        | succ j => rw [getD_nil, getD_cons_succ, hxs j]
      · rw [if_neg hx]
        cases i with
        | zero => rw [getD_cons_zero, getD_cons_zero]
        | succ j => rw [getD_cons_succ, getD_cons_succ, getD_nil, hxs j]
    | cons y ys =>
      rw [hs] at ih
      cases i with
      | zero => rw [getD_cons_zero, getD_cons_zero]
      | succ j => rw [getD_cons_succ, getD_cons_succ]; exact ih j

theorem trit_mk' (l : Trit) (L : List Trit) (i : Nat) :
    (Value.mk' l L).trit i = L.getD i l :=
  getD_stripLead l L i

theorem length_padTo (n : Nat) (t : Trit) (l : List Trit) (h : l.length ≤ n) :
    (Value.padTo n t l).length = n := by
  simp only [Value.padTo, List.length_append, List.length_replicate]
  omega

theorem getD_padTo (n : Nat) (t : Trit) (l : List Trit) (i : Nat) :
    (Value.padTo n t l).getD i t = l.getD i t := by
  unfold Value.padTo
  rcases Nat.lt_or_ge i l.length with h | h
  · rw [getD_lt (by simp; omega), getD_lt h, List.getElem_append_left h]
  · rw [getD_ge h]
    rcases Nat.lt_or_ge i (l ++ List.replicate (n - l.length) t).length with h' | h'
    · rw [getD_lt h', List.getElem_append_right h]
      simp
    · rw [getD_ge h']

/-- **The crazy operation is tritwise**, at every position and in the
repeating trit, which is what makes reasoning about it position by
position sound. -/
theorem crz_trit (a b : Value) (i : Nat) :
    (Value.crz a b).trit i = crzTrit (a.trit i) (b.trit i) := by
  have hla : a.low.length ≤ max a.low.length b.low.length := Nat.le_max_left _ _
  have hlb : b.low.length ≤ max a.low.length b.low.length := Nat.le_max_right _ _
  rw [Value.crz, trit_mk']
  have hAlen : (Value.padTo (max a.low.length b.low.length) a.lead a.low).length
      = max a.low.length b.low.length := length_padTo _ _ _ hla
  have hBlen : (Value.padTo (max a.low.length b.low.length) b.lead b.low).length
      = max a.low.length b.low.length := length_padTo _ _ _ hlb
  rcases Nat.lt_or_ge i (max a.low.length b.low.length) with h | h
  · rw [getD_lt (by simp [hAlen, hBlen]; omega), List.getElem_zipWith]
    rw [← getD_lt (l := Value.padTo _ a.lead a.low) (by omega) a.lead,
      ← getD_lt (l := Value.padTo _ b.lead b.low) (by omega) b.lead,
      getD_padTo, getD_padTo]
    rfl
  · rw [getD_ge (by simp [hAlen, hBlen]; omega)]
    rw [Value.trit, Value.trit, getD_ge (by omega), getD_ge (by omega)]

/-! ### Value extensionality

Two normalised values with the same repeating trit and the same trit at
every position are the same value. This is what lets a tritwise argument
conclude an equation between values. -/

theorem value_ext {v w : Value} (hl : v.lead = w.lead) (hlow : v.low = w.low) : v = w := by
  cases v; cases w; simp_all

theorem lastTrit?_eq_getD : ∀ {l : List Trit}, l ≠ [] → ∀ t : Trit,
    lastTrit? l = some (l.getD (l.length - 1) t)
  | [], h, _ => absurd rfl h
  | [x], _, t => rfl
  | x :: y :: ys, _, t => by
    rw [show lastTrit? (x :: y :: ys) = lastTrit? (y :: ys) from rfl,
      lastTrit?_eq_getD (by simp) t]
    simp only [List.length_cons]
    rw [show ys.length + 1 - 1 = ys.length by omega,
      show ys.length + 1 + 1 - 1 = ys.length + 1 by omega, getD_cons_succ]

theorem length_eq_of_trits {v w : Value} (hn : v.Normalized) (hm : w.Normalized)
    (hl : v.lead = w.lead) (ht : ∀ i, v.trit i = w.trit i) :
    v.low.length = w.low.length := by
  by_contra hne
  rcases Nat.lt_or_ge v.low.length w.low.length with h | h
  · have hw : w.low ≠ [] := by intro hz; rw [hz] at h; simp at h
    have hi := ht (w.low.length - 1)
    rw [Value.trit, Value.trit, getD_ge (by omega)] at hi
    exact hm (by rw [lastTrit?_eq_getD hw w.lead, ← hi, hl])
  · have hlt : w.low.length < v.low.length := by omega
    have hv : v.low ≠ [] := by intro hz; rw [hz] at hlt; simp at hlt
    have hi := ht (v.low.length - 1)
    rw [Value.trit, Value.trit, getD_ge (l := w.low) (by omega)] at hi
    exact hn (by rw [lastTrit?_eq_getD hv v.lead, hi, hl])

/-- Normalised values are determined by their repeating trit and their
trits. -/
theorem ext_of_trits {v w : Value} (hn : v.Normalized) (hm : w.Normalized)
    (hl : v.lead = w.lead) (ht : ∀ i, v.trit i = w.trit i) : v = w := by
  refine value_ext hl (List.ext_getElem (length_eq_of_trits hn hm hl ht) ?_)
  intro i h₁ h₂
  have hi := ht i
  rw [Value.trit, Value.trit, getD_lt h₁, getD_lt h₂] at hi
  exact hi

/-! ### Reaching any value in two operations -/

/-- The memory trit that turns an accumulator trit into 2. -/
def toTwo : Trit → Trit
  | .t0 => .t2
  | .t1 => .t2
  | .t2 => .t1

/-- The memory trit that turns an accumulator trit of 2 into a chosen
target. -/
def fromTwo : Trit → Trit
  | .t0 => .t0
  | .t1 => .t2
  | .t2 => .t1

theorem crzTrit_toTwo (x : Trit) : crzTrit x (toTwo x) = .t2 := by cases x <;> rfl

theorem crzTrit_fromTwo (t : Trit) : crzTrit .t2 (fromTwo t) = t := by cases t <;> rfl

/-- One operation is genuinely not enough: an accumulator trit of 0 can
never produce a 0, and one of 1 can never produce a 1, whatever the memory
holds. That is why `crz_two_steps` needs two. -/
theorem crzTrit_zero_ne_zero (y : Trit) : crzTrit .t0 y ≠ .t0 := by cases y <;> decide

theorem crzTrit_one_ne_one (y : Trit) : crzTrit .t1 y ≠ .t1 := by cases y <;> decide

/-- The constant that drives any value to `...222`. -/
def toTwoConst (a : Value) : Value := Value.mk' (toTwo a.lead) (a.low.map toTwo)

/-- The constant that drives `...222` to `t`. -/
def fromTwoConst (t : Value) : Value := Value.mk' (fromTwo t.lead) (t.low.map fromTwo)

private theorem trit_mapConst (f : Trit → Trit) (v : Value) (i : Nat) :
    (Value.mk' (f v.lead) (v.low.map f)).trit i = f (v.trit i) := by
  rw [trit_mk', Value.trit]
  rcases Nat.lt_or_ge i v.low.length with h | h
  · rw [getD_lt (by simpa using h), getD_lt h, List.getElem_map]
  · rw [getD_ge (by simpa using h), getD_ge h]

theorem trit_toTwoConst (a : Value) (i : Nat) :
    (toTwoConst a).trit i = toTwo (a.trit i) := trit_mapConst _ _ _

theorem trit_fromTwoConst (t : Value) (i : Nat) :
    (fromTwoConst t).trit i = fromTwo (t.trit i) := trit_mapConst _ _ _

/-- One crazy operation against `toTwoConst a` sends any accumulator to
`...222`, the end-of-file value. -/
theorem crz_toTwoConst (a : Value) : Value.crz a (toTwoConst a) = Value.eof := by
  refine ext_of_trits (Value.normalized_mk' _ _)
    (by simp [Value.Normalized, Value.eof, lastTrit?]) ?_ ?_
  · show crzTrit a.lead (toTwoConst a).lead = Trit.t2
    exact crzTrit_toTwo a.lead
  · intro i
    rw [crz_trit, trit_toTwoConst, crzTrit_toTwo]
    rfl

/-- One crazy operation against `fromTwoConst t` sends `...222` to any
normalised `t`. -/
theorem crz_fromTwoConst {t : Value} (h : t.Normalized) :
    Value.crz Value.eof (fromTwoConst t) = t := by
  refine ext_of_trits (Value.normalized_mk' _ _) h ?_ ?_
  · show crzTrit Trit.t2 (fromTwoConst t).lead = t.lead
    exact crzTrit_fromTwo t.lead
  · intro i
    rw [crz_trit, trit_fromTwoConst, show Value.eof.trit i = Trit.t2 from rfl]
    exact crzTrit_fromTwo (t.trit i)

/-- **Two crazy operations reach anything.** From any accumulator `a` and
any normalised target `t` there are two constants such that running `p`
against them in turn leaves both the accumulator and the cell holding `t`.

One operation does not suffice, by `crzTrit_zero_ne_zero`. This is the
whole arithmetic a rot-free backend has, and it is enough to write a
computed address into a jump table, which is what a data-driven branch is
made of. -/
theorem crz_two_steps (a : Value) {t : Value} (h : t.Normalized) :
    ∃ k₁ k₂, Value.crz (Value.crz a k₁) k₂ = t :=
  ⟨toTwoConst a, fromTwoConst t, by rw [crz_toTwoConst, crz_fromTwoConst h]⟩

/-! ## The width algebra: where unboundedness lives

Malbolge Unshackled is "Malbolge without the memory bound", but the
unboundedness has to enter through some instruction, and this section pins
down which one. Three width facts, all proved from the definitions:

* the crazy operation never widens (`width_crz_le`);
* successor widens by at most one trit, and successor applies only to `c`
  and `d`, which no instruction can store into memory;
* rotation is the one operation that can widen a *stored* value, up to the
  current rotation width (`width_rot_le`).

`widthBounded_step1` assembles them: a step whose instruction is not `*`
preserves any width bound `W ≥ 13` on the accumulator and on every memory
cell (13 because an input character's code point is below `3^13`). So in a
run that never rotates, every storable value stays inside a **finite
alphabet**: values of width at most `W` with one of three repeating trits.
Every `j` and `i` target is a stored value, so every teleport lands inside
that finite set; the only way past it is `d`'s one-cell-per-step walk.

The door the language actually opens is the feedback between `*` and `j`:
`rot` lifts a narrow value to the full rotation width, `j` on the widened
value raises `maxWidth`, and the width then doubles (`growRotWidth`). That
loop, and nothing else, manufactures unboundedly wide values, which is to
say unboundedly many nameable addresses. `docs/malbolge-unshackled/compiler.md`
draws the consequences for a compiler. -/

theorem length_stripLead_le (t : Trit) : ∀ l : List Trit,
    (stripLead t l).length ≤ l.length
  | [] => Nat.le_refl 0
  | x :: xs => by
    have ih := length_stripLead_le t xs
    show (match stripLead t xs with
      | [] => if x = t then [] else [x]
      | ys => x :: ys).length ≤ xs.length + 1
    cases hs : stripLead t xs with
    | nil =>
      by_cases hx : x = t
      · simp [hx]
      · simp [hx]
    | cons y ys =>
      rw [hs] at ih
      simpa using ih

theorem width_mk'_le (l : Trit) (L : List Trit) : (Value.mk' l L).width ≤ L.length :=
  length_stripLead_le l L

/-- **The crazy operation never widens a value.** Every value a rot-free
program can ever store has the width of some initial value. -/
theorem width_crz_le (a b : Value) : (Value.crz a b).width ≤ max a.width b.width := by
  unfold Value.crz
  refine Nat.le_trans (width_mk'_le _ _) ?_
  rw [List.length_zipWith,
    length_padTo _ _ _ (Nat.le_max_left _ _),
    length_padTo _ _ _ (Nat.le_max_right _ _)]
  exact Nat.le_of_eq (Nat.min_self _)

/-- **Rotation is the widening operation**: it can lift any value up to the
current rotation width, and no further. With `movd`'s width doubling this
is the language's one door to unboundedly wide values. -/
theorem width_rot_le (w : Nat) (v : Value) : (Value.rot w v).width ≤ max w v.width := by
  unfold Value.rot
  cases hw : (List.range w).map v.trit with
  | nil =>
    have h0 : w = 0 := by simpa using congrArg List.length hw
    subst h0
    exact Nat.le_max_right 0 v.width
  | cons x xs =>
    have hlen := congrArg List.length hw
    simp only [List.length_map, List.length_range, List.length_cons] at hlen
    refine Nat.le_trans (width_mk'_le _ _) ?_
    simp only [List.length_append, List.length_cons, List.length_drop,
      List.length_nil, Value.width]
    omega

theorem length_succTrits_le (lead : Trit) : ∀ l : List Trit,
    (Value.succTrits lead l).2.length ≤ l.length + 1
  | [] => by cases lead <;> simp [Value.succTrits]
  | .t0 :: rest => by simp [Value.succTrits]
  | .t1 :: rest => by simp [Value.succTrits]
  | .t2 :: rest => by
    have ih := length_succTrits_le lead rest
    show (match Value.succTrits lead rest with
      | (lead', rest') => (lead', Trit.t0 :: rest')).2.length ≤ rest.length + 1 + 1
    cases hs : Value.succTrits lead rest with
    | mk lead' rest' =>
      rw [hs] at ih
      simpa using ih

/-- Successor widens by at most one trit. It applies only to `c` and `d`,
which no instruction can store, so it never widens a memory cell. -/
theorem width_succ_le (v : Value) : v.succ.width ≤ v.width + 1 := by
  show (match Value.succTrits v.lead v.low with
    | (lead, low) => Value.mk' lead low).width ≤ v.low.length + 1
  have h := length_succTrits_le v.lead v.low
  cases hs : Value.succTrits v.lead v.low with
  | mk lead' low' =>
    rw [hs] at h
    exact Nat.le_trans (width_mk'_le _ _) h

/-! ### The bounds an interpreter step needs -/

theorem length_trits3_le : ∀ n, ∀ k : Nat, n < 3 ^ k → (trits3 n).length ≤ k := by
  intro n
  induction n using trits3.induct with
  | case1 => intro k _; rw [trits3_zero]; exact Nat.zero_le k
  | case2 n ih =>
    intro k hk
    cases k with
    | zero => simp at hk
    | succ k =>
      rw [trits3_succ]
      simp only [List.length_cons]
      have hdiv : (n + 1) / 3 < 3 ^ k := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]
        calc n + 1 < 3 ^ (k + 1) := hk
          _ = 3 ^ k * 3 := by rw [Nat.pow_succ]
      exact Nat.succ_le_succ (ih k hdiv)

theorem width_ofNat_le {n k : Nat} (h : n < 3 ^ k) : (Value.ofNat n).width ≤ k := by
  rw [ofNat_eq]
  exact length_trits3_le n k h

/-- A character's code point is below `3^13 = 1594323`, so an input
character is at most 13 trits wide. -/
theorem width_ofChar_le (c : Char) : (Value.ofChar c).width ≤ 13 := by
  refine width_ofNat_le ?_
  have h := c.valid
  unfold Char.toNat
  show c.val.toNat < 1594323
  rcases h with h | h <;> omega

theorem printableCode?_bounds {v : Value} {n : Nat}
    (h : printableCode? v = some n) : 33 ≤ n ∧ n ≤ 126 := by
  unfold printableCode? at h
  cases ht : v.toNat? with
  | none => rw [ht] at h; simp at h
  | some m =>
    rw [ht] at h
    dsimp only at h
    split at h
    · rename_i hcond
      simp only [Option.some.injEq] at h
      subst h
      simpa using hcond
    · simp at h

/-- The word the postal stage writes is at most 5 trits wide: encryption
stays inside `33..126 < 3^5`. -/
theorem width_encrypt_le {code : Nat} (h₁ : 33 ≤ code) (h₂ : code ≤ 126) :
    (Value.ofNat (encrypt code)).width ≤ 5 := by
  obtain ⟨_, he₂⟩ := encrypt_range h₁ h₂
  exact width_ofNat_le (by omega)

/-! ### The step theorem -/

/-- Every value the machine can store or accumulate is at most `W` trits
wide. `c` and `d` are deliberately absent: they grow by successor and
cannot be stored, so no bound on them is needed or true. -/
def WidthBounded (W : Nat) (s : State) : Prop :=
  s.a.width ≤ W ∧ ∀ addr, (s.mem.get addr).width ≤ W

theorem widthBounded_set {m : Memory} {W : Nat}
    (h : ∀ addr, (m.get addr).width ≤ W) {v : Value} (hv : v.width ≤ W)
    (x : Value) : ∀ addr, ((m.set x v).get addr).width ≤ W := by
  intro addr
  by_cases hx : x = addr
  · subst hx; rw [get_set_self]; exact hv
  · rw [get_set_ne _ hx]; exact h addr

private theorem doOutput_frame {s s₁ : State} (h : doOutput s = .ok s₁) :
    s₁.a = s.a ∧ s₁.mem = s.mem := by
  unfold doOutput at h
  split at h
  · injection h with h; subst h; exact ⟨rfl, rfl⟩
  · split at h
    · simp at h
    · split at h
      · injection h with h; subst h; exact ⟨rfl, rfl⟩
      · cases hn : s.a.toNat? with
        | none => rw [hn] at h; simp at h
        | some n =>
          rw [hn] at h
          dsimp only at h
          split at h
          · injection h with h; subst h; exact ⟨rfl, rfl⟩
          · simp at h

private theorem doInput_width {W : Nat} (hW : 13 ≤ W) {s s₁ : State}
    (h : doInput s = .ok s₁) :
    s₁.a.width ≤ W ∧ s₁.mem = s.mem := by
  unfold doInput at h
  cases hr : readChar? s.input with
  | error e =>
    rw [hr] at h
    simp only [bind, Except.bind] at h
    cases h
  | ok r =>
    rw [hr] at h
    simp only [bind, Except.bind] at h
    cases r with
    | none =>
      injection h with h
      subst h
      refine ⟨?_, rfl⟩
      show Value.eof.width ≤ W
      exact Nat.le_trans (by decide) hW
    | some p =>
      obtain ⟨ch, i⟩ := p
      injection h with h
      subst h
      refine ⟨?_, rfl⟩
      show (if ch == '\n' then Value.eol else Value.ofChar ch).width ≤ W
      split
      · exact Nat.le_trans (by decide) hW
      · exact Nat.le_trans (width_ofChar_le ch) hW

/-- One instruction of the pure step, minus the postal stage: every
instruction except `*` preserves a width bound of at least 13. -/
theorem step_widthBounded {W : Nat} (hW : 13 ≤ W) {instr : Instr} {s s₁ : State}
    (h : WidthBounded W s) (hrot : instr ≠ .rotr)
    (hstep : step instr s = .ok s₁) : WidthBounded W s₁ := by
  obtain ⟨ha, hm⟩ := h
  cases instr with
  | rotr => exact absurd rfl hrot
  | jmp =>
    simp only [step] at hstep
    injection hstep with hstep
    subst hstep
    exact ⟨ha, hm⟩
  | out =>
    simp only [step] at hstep
    obtain ⟨ha', hm'⟩ := doOutput_frame hstep
    exact ⟨ha' ▸ ha, fun addr => hm' ▸ hm addr⟩
  | inp =>
    simp only [step] at hstep
    obtain ⟨ha', hm'⟩ := doInput_width hW hstep
    exact ⟨ha', fun addr => hm' ▸ hm addr⟩
  | movd =>
    simp only [step] at hstep
    split at hstep <;>
      · injection hstep with hstep
        subst hstep
        exact ⟨ha, hm⟩
  | crazy =>
    simp only [step] at hstep
    injection hstep with hstep
    subst hstep
    have hv : (Value.crz s.a (s.mem.get s.d)).width ≤ W :=
      Nat.le_trans (width_crz_le _ _) (Nat.max_le.mpr ⟨ha, hm s.d⟩)
    exact ⟨hv, widthBounded_set hm hv s.d⟩
  | nop =>
    simp only [step] at hstep
    injection hstep with hstep
    subst hstep
    exact ⟨ha, hm⟩
  | halt =>
    simp only [step] at hstep
    injection hstep with hstep
    subst hstep
    exact ⟨ha, hm⟩
  | outOfBounds =>
    simp only [step] at hstep
    injection hstep with hstep
    subst hstep
    exact ⟨ha, hm⟩

/-- **A step that does not rotate preserves any width bound `W ≥ 13`.**
The consequence for architecture: in a run that never executes `*`, every
storable value lives in the finite set of values at most `W` trits wide, so
every `j` and `i` teleports into a finite set of addresses, for the whole
of the run. Rotation is not a convenience the compiler may decline; the
`rot`/`movd` width-doubling feedback is the language's only supply of
unboundedly many nameable addresses. -/
private theorem widthBounded_step1_generic {W : Nat} (hW : 13 ≤ W)
    {instr : Instr} {s s' : State}
    (_ : decode (s.mem.get s.c) s.c.modClass = instr)
    (h : WidthBounded W s) (hrot : instr ≠ .rotr)
    (hstep : (match step instr s with
              | .error _ => none
              | .ok s₁ =>
                match printableCode? (s₁.mem.get s₁.c) with
                | none => none
                | some code =>
                  some { s₁ with mem := s₁.mem.set s₁.c (Value.ofNat (encrypt code)),
                                 c := s₁.c.succ, d := s₁.d.succ }) = some s') :
    WidthBounded W s' := by
  cases hst : step instr s with
  | error e => rw [hst] at hstep; simp at hstep
  | ok s₁ =>
    rw [hst] at hstep
    dsimp only at hstep
    cases hp : printableCode? (s₁.mem.get s₁.c) with
    | none => rw [hp] at hstep; simp at hstep
    | some code =>
      rw [hp] at hstep
      simp only [Option.some.injEq] at hstep
      subst hstep
      obtain ⟨hc₁, hc₂⟩ := printableCode?_bounds hp
      have h₁ : WidthBounded W s₁ := step_widthBounded hW h hrot hst
      exact ⟨h₁.1,
        widthBounded_set h₁.2
          (Nat.le_trans (width_encrypt_le hc₁ hc₂) (by omega)) s₁.c⟩

/-- **A step that does not rotate preserves any width bound `W ≥ 13`.**
The consequence for architecture: in a run that never executes `*`, every
storable value lives in the finite set of values at most `W` trits wide, so
every `j` and `i` teleports into a finite set of addresses, for the whole
of the run. Rotation is not a convenience the compiler may decline; the
`rot`/`movd` width-doubling feedback is the language's only supply of
unboundedly many nameable addresses. -/
theorem widthBounded_step1 {W : Nat} (hW : 13 ≤ W) {s s' : State}
    (h : WidthBounded W s)
    (hrot : decode (s.mem.get s.c) s.c.modClass ≠ .rotr)
    (hstep : step1 s = some s') : WidthBounded W s' := by
  unfold step1 at hstep
  cases hd : decode (s.mem.get s.c) s.c.modClass <;> rw [hd] at hstep
  case outOfBounds =>
    simp only [Option.some.injEq] at hstep
    subst hstep
    exact h
  case halt => simp at hstep
  case rotr => exact absurd hd hrot
  all_goals exact widthBounded_step1_generic hW hd h (by simp) hstep

/-! ### The escalator

The positive half of the width story: how a program actually manufactures a
wide value. Rotating the value `1` at rotation width `w` moves its single
set trit to the top of the window, producing `3^(w-1)`, a value of width
exactly `w`. A `j` through that value then raises `maxWidth` to `w` and the
rotation width to `2w` (`growRotWidth`). Rotate `1` again and the next
value has width `2w`. Iterating mints addresses of width `10, 20, 40, …`:
this loop is the allocator of any compiler targeting this language, and the
concrete meaning of "Unshackled". -/

theorem trits3_three_mul {m : Nat} (hm : 0 < m) :
    trits3 (3 * m) = .t0 :: trits3 m := by
  rw [show 3 * m = (3 * m - 1) + 1 by omega, trits3_succ,
    show (3 * m - 1) + 1 = 3 * m by omega,
    ofResidue_zero (by omega), Nat.mul_div_cancel_left m (by omega)]

theorem trits3_one : trits3 1 = [.t1] := by
  rw [show (1:Nat) = 0 + 1 from rfl, trits3_succ, ofResidue_one (by omega),
    show (0 + 1) / 3 = 0 by omega, trits3_zero]

theorem trits3_pow3 : ∀ k, trits3 (3 ^ k) = List.replicate k .t0 ++ [.t1]
  | 0 => by rw [show (3:Nat) ^ 0 = 1 from rfl, trits3_one]; rfl
  | k + 1 => by
    rw [show (3:Nat) ^ (k + 1) = 3 * 3 ^ k by rw [Nat.pow_succ, Nat.mul_comm],
      trits3_three_mul (Nat.pow_pos (by omega)), trits3_pow3 k]
    rfl

theorem trit_ofNat_one : ∀ i, (Value.ofNat 1).trit i = if i = 0 then .t1 else .t0 := by
  intro i
  rw [ofNat_eq]
  show (trits3 1).getD i .t0 = _
  rw [show (1:Nat) = 0 + 1 from rfl, trits3_succ, trits3_zero]
  cases i with
  | zero => rfl
  | succ j => simp [List.getD]

/-- **Rotation mints a wide value from a narrow one**: the value `1` at
rotation width `w` becomes `3^(w-1)`. -/
theorem rot_one (w : Nat) (hw : 1 ≤ w) :
    Value.rot w (Value.ofNat 1) = Value.ofNat (3 ^ (w - 1)) := by
  have hmap : (List.range w).map (Value.ofNat 1).trit
      = .t1 :: List.replicate (w - 1) .t0 := by
    rw [show w = (w - 1) + 1 by omega, List.range_succ_eq_map, List.map_cons,
      List.map_map, trit_ofNat_one 0, if_pos rfl]
    congr 1
    have hall : ∀ b ∈ (List.range (w - 1)).map ((Value.ofNat 1).trit ∘ (· + 1)),
        b = Trit.t0 := by
      intro b hb
      obtain ⟨i, _, hi⟩ := List.mem_map.mp hb
      rw [← hi]
      show (Value.ofNat 1).trit (i + 1) = .t0
      rw [trit_ofNat_one]
      simp
    calc (List.range (w - 1)).map ((Value.ofNat 1).trit ∘ (· + 1))
        = List.replicate ((List.range (w - 1)).map ((Value.ofNat 1).trit ∘ (· + 1))).length .t0 :=
          List.eq_replicate_of_mem hall
      _ = List.replicate (w - 1) .t0 := by simp
  have hdrop : (Value.ofNat 1).low.drop w = [] := by
    apply List.drop_eq_nil_of_le
    rw [ofNat_eq]
    show (trits3 1).length ≤ w
    exact Nat.le_trans (length_trits3_le 1 1 (by omega)) hw
  unfold Value.rot
  rw [hmap, hdrop]
  show Value.mk' Trit.t0 (List.replicate (w - 1) Trit.t0 ++ [Trit.t1] ++ []) = _
  rw [List.append_nil]
  have hlast : lastTrit? (List.replicate (w - 1) Trit.t0 ++ [Trit.t1]) ≠ some Trit.t0 := by
    rw [lastTrit?_eq_getD (by simp) Trit.t0]
    rw [getD_lt (by simp)]
    rw [List.getElem_append_right (by simp)]
    simp
  rw [Value.mk', stripLead_eq_self hlast, ofNat_eq, trits3_pow3]

/-- The width really is `w`: rotation reached the top of its window. -/
theorem width_rot_one (w : Nat) (hw : 1 ≤ w) :
    (Value.rot w (Value.ofNat 1)).width = w := by
  rw [rot_one w hw, ofNat_eq]
  show (trits3 (3 ^ (w - 1))).length = w
  rw [trits3_pow3]
  simp
  omega

/-- **The doubling**: a `j` that raises the maximum seen width to the
current rotation width doubles the rotation width. With `rot_one` this is
the allocator loop: rotate `1` into a width-`w` address, `j` through it,
and the window is `2w`. -/
theorem growRotWidth_double (w : Nat) : growRotWidth w w = 2 * w := by
  unfold growRotWidth
  omega

/-! ## The branch arithmetic

A branch in this language is a `jmp` whose target cell holds a *computed*
address, so the whole difficulty of branching is arithmetic: turn a data
value into one of two chosen targets using only the crazy operation. This
section solves that in seven `p` operations against constants an assembler
can compute.

The pipeline, per trit position (the crazy operation is tritwise, so the
whole design is per-position):

1. **Absorb** (2 ops). `crzTrit (crzTrit x 2) 0 = 0` for every `x`, so two
   operations against the constants `...222` and `...000` force the
   accumulator to zero from any starting value. No knowledge of `a` needed.
2. **Load** (1 op). With the flag cell holding `...000` or `...222`, one
   operation gives `crz 0 flag = ...111` or `...222`: two uniform values.
3. **Shape** (4 ops). The three columns of the crazy table, as maps of the
   accumulator trit, are `[1,0,0]`, `[1,0,2]` and `[2,2,1]`. Compositions
   of four of them realise **every** function `{1 ↦ p, 2 ↦ q}` (three do
   not: `(1,0)` needs four), and `cols` tabulates a witness for each of
   the nine pairs. Four constants, built per-position from the two
   targets' trits, then send `...111` to `t₀` and `...222` to `t₁`.

Both branch cases execute the *same seven instructions*; only the data
differs, which is what a Malbolge Unshackled control flow graph needs,
since instructions cannot be chosen per-case at runtime. -/

/-- Tritwise combination of two values, the shape shared by the crazy
operation and by the constant-builders below. -/
def map2 (f : Trit → Trit → Trit) (a b : Value) : Value :=
  let n := max a.low.length b.low.length
  Value.mk' (f a.lead b.lead)
    ((Value.padTo n a.lead a.low).zipWith f (Value.padTo n b.lead b.low))

theorem crz_eq_map2 (a b : Value) : Value.crz a b = map2 crzTrit a b := rfl

/-- `map2` really is tritwise: the generalisation of `crz_trit`, proved the
same way. -/
theorem trit_map2 (f : Trit → Trit → Trit) (a b : Value) (i : Nat) :
    (map2 f a b).trit i = f (a.trit i) (b.trit i) := by
  have hla : a.low.length ≤ max a.low.length b.low.length := Nat.le_max_left _ _
  have hlb : b.low.length ≤ max a.low.length b.low.length := Nat.le_max_right _ _
  rw [map2, trit_mk']
  have hAlen : (Value.padTo (max a.low.length b.low.length) a.lead a.low).length
      = max a.low.length b.low.length := length_padTo _ _ _ hla
  have hBlen : (Value.padTo (max a.low.length b.low.length) b.lead b.low).length
      = max a.low.length b.low.length := length_padTo _ _ _ hlb
  rcases Nat.lt_or_ge i (max a.low.length b.low.length) with h | h
  · rw [getD_lt (by simp [hAlen, hBlen]; omega), List.getElem_zipWith]
    rw [← getD_lt (l := Value.padTo _ a.lead a.low) (by omega) a.lead,
      ← getD_lt (l := Value.padTo _ b.lead b.low) (by omega) b.lead,
      getD_padTo, getD_padTo]
    rfl
  · rw [getD_ge (by simp [hAlen, hBlen]; omega)]
    rw [Value.trit, Value.trit, getD_ge (by omega), getD_ge (by omega)]

theorem map2_normalized (f : Trit → Trit → Trit) (a b : Value) :
    (map2 f a b).Normalized := Value.normalized_mk' _ _

theorem crz_normalized (a b : Value) : (Value.crz a b).Normalized :=
  Value.normalized_mk' _ _

/-- The value whose every trit is `t`. `uniform .t0` is zero and
`uniform .t2` is `...222`, the end-of-file value. -/
def uniform (t : Trit) : Value := ⟨t, []⟩

theorem trit_uniform (t : Trit) (i : Nat) : (uniform t).trit i = t := rfl

theorem uniform_normalized (t : Trit) : (uniform t).Normalized := by
  simp [uniform, Value.Normalized, lastTrit?]

/-! ### Step 1: the absorber -/

/-- **Two crazy operations forget the accumulator**: against `...222` and
then `...000`, every starting value becomes zero. Per trit this is
`crzTrit (crzTrit x 2) 0 = 0` in all three cases. The second constant is
also self-restoring: the operation writes `...000` over the cell that
held `...000`. -/
theorem crz_absorb (a : Value) :
    Value.crz (Value.crz a Value.eof) Value.zero = Value.zero := by
  refine ext_of_trits (crz_normalized _ _) (uniform_normalized .t0) ?_ ?_
  · show crzTrit (crzTrit a.lead (Value.eof).lead) (Value.zero).lead = Trit.t0
    cases a.lead <;> rfl
  · intro i
    rw [crz_trit, crz_trit]
    show crzTrit (crzTrit (a.trit i) Trit.t2) Trit.t0 = Trit.t0
    cases a.trit i <;> rfl

/-! ### Step 2: loading the flag -/

theorem crz_zero_zero : Value.crz Value.zero Value.zero = uniform .t1 := by decide

theorem crz_zero_eof : Value.crz Value.zero Value.eof = uniform .t2 := by decide

/-! ### Step 3: the shaper -/

/-- For each target pair `(p, q)`, four columns of the crazy table whose
composition sends the trit `1` to `p` and the trit `2` to `q`. The table
was found by enumeration; `cols_spec` checks it in the kernel. Three
columns do not suffice: the pair `(1, 0)` is not reachable at depth
three. -/
def cols : Trit → Trit → Trit × Trit × Trit × Trit
  | .t0, .t0 => (.t0, .t0, .t2, .t0)
  | .t0, .t1 => (.t1, .t2, .t1, .t0)
  | .t0, .t2 => (.t1, .t2, .t2, .t1)
  | .t1, .t0 => (.t1, .t0, .t0, .t0)
  | .t1, .t1 => (.t0, .t0, .t0, .t0)
  | .t1, .t2 => (.t1, .t1, .t1, .t1)
  | .t2, .t0 => (.t1, .t1, .t2, .t1)
  | .t2, .t1 => (.t1, .t1, .t1, .t2)
  | .t2, .t2 => (.t0, .t0, .t0, .t2)

theorem cols_spec : ∀ p q : Trit,
    crzTrit (crzTrit (crzTrit (crzTrit .t1 (cols p q).1) (cols p q).2.1)
        (cols p q).2.2.1) (cols p q).2.2.2 = p
  ∧ crzTrit (crzTrit (crzTrit (crzTrit .t2 (cols p q).1) (cols p q).2.1)
        (cols p q).2.2.1) (cols p q).2.2.2 = q := by
  intro p q
  cases p <;> cases q <;> exact ⟨rfl, rfl⟩

/-- The four shaping constants, built per trit position from the two
targets. These are what an assembler computes and lays out in memory. -/
def k1Of (t₀ t₁ : Value) : Value := map2 (fun p q => (cols p q).1) t₀ t₁
def k2Of (t₀ t₁ : Value) : Value := map2 (fun p q => (cols p q).2.1) t₀ t₁
def k3Of (t₀ t₁ : Value) : Value := map2 (fun p q => (cols p q).2.2.1) t₀ t₁
def k4Of (t₀ t₁ : Value) : Value := map2 (fun p q => (cols p q).2.2.2) t₀ t₁

/-- The shaper: four crazy operations against the four constants. -/
def shape (t₀ t₁ v : Value) : Value :=
  Value.crz (Value.crz (Value.crz (Value.crz v (k1Of t₀ t₁)) (k2Of t₀ t₁))
    (k3Of t₀ t₁)) (k4Of t₀ t₁)

theorem shape_uniform₁ {t₀ : Value} (t₁ : Value) (h₀ : t₀.Normalized) :
    shape t₀ t₁ (uniform .t1) = t₀ := by
  refine ext_of_trits (crz_normalized _ _) h₀ ?_ ?_
  · show crzTrit (crzTrit (crzTrit (crzTrit (uniform Trit.t1).lead
        (cols t₀.lead t₁.lead).1) (cols t₀.lead t₁.lead).2.1)
        (cols t₀.lead t₁.lead).2.2.1) (cols t₀.lead t₁.lead).2.2.2 = t₀.lead
    exact (cols_spec t₀.lead t₁.lead).1
  · intro i
    show (Value.crz (Value.crz (Value.crz (Value.crz (uniform .t1) (k1Of t₀ t₁))
      (k2Of t₀ t₁)) (k3Of t₀ t₁)) (k4Of t₀ t₁)).trit i = t₀.trit i
    rw [crz_trit, crz_trit, crz_trit, crz_trit,
      show (k1Of t₀ t₁).trit i = (cols (t₀.trit i) (t₁.trit i)).1 from trit_map2 _ _ _ i,
      show (k2Of t₀ t₁).trit i = (cols (t₀.trit i) (t₁.trit i)).2.1 from trit_map2 _ _ _ i,
      show (k3Of t₀ t₁).trit i = (cols (t₀.trit i) (t₁.trit i)).2.2.1 from trit_map2 _ _ _ i,
      show (k4Of t₀ t₁).trit i = (cols (t₀.trit i) (t₁.trit i)).2.2.2 from trit_map2 _ _ _ i,
      trit_uniform]
    exact (cols_spec (t₀.trit i) (t₁.trit i)).1

theorem shape_uniform₂ (t₀ : Value) {t₁ : Value} (h₁ : t₁.Normalized) :
    shape t₀ t₁ (uniform .t2) = t₁ := by
  refine ext_of_trits (crz_normalized _ _) h₁ ?_ ?_
  · show crzTrit (crzTrit (crzTrit (crzTrit (uniform Trit.t2).lead
        (cols t₀.lead t₁.lead).1) (cols t₀.lead t₁.lead).2.1)
        (cols t₀.lead t₁.lead).2.2.1) (cols t₀.lead t₁.lead).2.2.2 = t₁.lead
    exact (cols_spec t₀.lead t₁.lead).2
  · intro i
    show (Value.crz (Value.crz (Value.crz (Value.crz (uniform .t2) (k1Of t₀ t₁))
      (k2Of t₀ t₁)) (k3Of t₀ t₁)) (k4Of t₀ t₁)).trit i = t₁.trit i
    rw [crz_trit, crz_trit, crz_trit, crz_trit,
      show (k1Of t₀ t₁).trit i = (cols (t₀.trit i) (t₁.trit i)).1 from trit_map2 _ _ _ i,
      show (k2Of t₀ t₁).trit i = (cols (t₀.trit i) (t₁.trit i)).2.1 from trit_map2 _ _ _ i,
      show (k3Of t₀ t₁).trit i = (cols (t₀.trit i) (t₁.trit i)).2.2.1 from trit_map2 _ _ _ i,
      show (k4Of t₀ t₁).trit i = (cols (t₀.trit i) (t₁.trit i)).2.2.2 from trit_map2 _ _ _ i,
      trit_uniform]
    exact (cols_spec (t₀.trit i) (t₁.trit i)).2

/-! ### The pipeline -/

/-- The full branch pipeline: seven crazy operations. The first six
constants (`...222`, `...000`, the flag cell, `k₁`, `k₂`, `k₃`) are read
where `d` happens to be, the seventh produces the target. -/
def branchChain (t₀ t₁ a flag : Value) : Value :=
  shape t₀ t₁ (Value.crz (Value.crz (Value.crz a Value.eof) Value.zero) flag)

/-- **The branch arithmetic.** For any two normalised targets there are
seven constants, computed from the targets alone, such that seven crazy
operations turn *any* accumulator into `t₀` when the flag cell holds
`...000` and into `t₁` when it holds `...222`. Both cases run the same
instructions; only the flag differs. Together with `exec_jmp` this is a
data-driven two-way branch: write the result into a jump table and jump
through it. -/
theorem branch_arith (t₀ t₁ : Value) (h₀ : t₀.Normalized) (h₁ : t₁.Normalized)
    (a : Value) :
    branchChain t₀ t₁ a Value.zero = t₀ ∧ branchChain t₀ t₁ a Value.eof = t₁ := by
  constructor
  · rw [branchChain, crz_absorb, crz_zero_zero]
    exact shape_uniform₁ t₁ h₀
  · rw [branchChain, crz_absorb, crz_zero_eof]
    exact shape_uniform₂ t₀ h₁

/-! ## Step lemmas for `step1`

The `exec_*` lemmas above read the interpreter one dispatch at a time; the
gadget proofs below work over `run?`, so they need the same readings at the
`step1` level. `step1_eq` is the generic form, one lemma per instruction
follows, and `ofNat_ne` supplies the address inequalities every frame
argument runs on. -/

theorem ofNat_inj {m n : Nat} (h : Value.ofNat m = Value.ofNat n) : m = n := by
  have hm := toNat?_ofNat m
  rw [h, toNat?_ofNat] at hm
  exact (Option.some.inj hm).symm

theorem ofNat_ne {m n : Nat} (h : m ≠ n) : Value.ofNat m ≠ Value.ofNat n :=
  fun he => h (ofNat_inj he)

theorem step1_eq {s s₁ : State} {instr : Instr} {code : Nat}
    (hdec : decode (s.mem.get s.c) s.c.modClass = instr)
    (h₁ : instr ≠ .outOfBounds) (h₂ : instr ≠ .halt)
    (hstep : step instr s = .ok s₁)
    (hcode : printableCode? (s₁.mem.get s₁.c) = some code) :
    step1 s = some { s₁ with mem := s₁.mem.set s₁.c (Value.ofNat (encrypt code)),
                             c := s₁.c.succ, d := s₁.d.succ } := by
  unfold step1
  rw [hdec]
  cases instr with
  | outOfBounds => exact absurd rfl h₁
  | halt => exact absurd rfl h₂
  | jmp => dsimp only; rw [hstep]; dsimp only; rw [hcode]
  | out => dsimp only; rw [hstep]; dsimp only; rw [hcode]
  | inp => dsimp only; rw [hstep]; dsimp only; rw [hcode]
  | rotr => dsimp only; rw [hstep]; dsimp only; rw [hcode]
  | movd => dsimp only; rw [hstep]; dsimp only; rw [hcode]
  | crazy => dsimp only; rw [hstep]; dsimp only; rw [hcode]
  | nop => dsimp only; rw [hstep]; dsimp only; rw [hcode]

/-- A crazy step at the `step1` level, with both writes spelled out. The
inequality keeps the postal encryption off the cell the operation just
wrote, which would crash the reference interpreter. -/
theorem step1_crazy {s : State} {code : Nat}
    (hdec : decode (s.mem.get s.c) s.c.modClass = .crazy)
    (hne : s.d ≠ s.c)
    (hcode : printableCode? (s.mem.get s.c) = some code) :
    step1 s = some { s with
      a := Value.crz s.a (s.mem.get s.d),
      mem := (s.mem.set s.d (Value.crz s.a (s.mem.get s.d))).set s.c
               (Value.ofNat (encrypt code)),
      c := s.c.succ, d := s.d.succ } := by
  refine step1_eq hdec (by simp) (by simp) rfl ?_
  show printableCode? ((s.mem.set s.d (Value.crz s.a (s.mem.get s.d))).get s.c)
    = some code
  rw [get_set_ne _ hne]
  exact hcode

/-- A movd step at the `step1` level. Both width registers are carried
along as conditionals; a caller who never rotates can ignore them. -/
theorem step1_movd {s : State} {code : Nat}
    (hdec : decode (s.mem.get s.c) s.c.modClass = .movd)
    (hcode : printableCode? (s.mem.get s.c) = some code) :
    step1 s = some { s with
      mem := s.mem.set s.c (Value.ofNat (encrypt code)),
      c := s.c.succ, d := (s.mem.get s.d).succ,
      maxWidth := if (s.mem.get s.d).width > s.maxWidth
                  then (s.mem.get s.d).width else s.maxWidth,
      rotWidth := if (s.mem.get s.d).width > s.maxWidth
                  then growRotWidth s.rotWidth (s.mem.get s.d).width
                  else s.rotWidth } := by
  have hstep : step .movd s = .ok { s with
      d := s.mem.get s.d,
      maxWidth := if (s.mem.get s.d).width > s.maxWidth
                  then (s.mem.get s.d).width else s.maxWidth,
      rotWidth := if (s.mem.get s.d).width > s.maxWidth
                  then growRotWidth s.rotWidth (s.mem.get s.d).width
                  else s.rotWidth } := by
    show (if (s.mem.get s.d).width > s.maxWidth then _ else _) = _
    split <;> rfl
  exact step1_eq hdec (by simp) (by simp) hstep hcode

/-- A jmp step at the `step1` level: the encryption lands on the target,
never on the jumping cell (`jmp_cell_stable` is this fact in isolation). -/
theorem step1_jmp {s : State} {code : Nat}
    (hdec : decode (s.mem.get s.c) s.c.modClass = .jmp)
    (hcode : printableCode? (s.mem.get (s.mem.get s.d)) = some code) :
    step1 s = some { s with
      mem := s.mem.set (s.mem.get s.d) (Value.ofNat (encrypt code)),
      c := (s.mem.get s.d).succ, d := s.d.succ } :=
  step1_eq hdec (by simp) (by simp) rfl hcode

/-- A nop step at the `step1` level: even doing nothing encrypts the cell
that did it. -/
theorem step1_nop {s : State} {code : Nat}
    (hdec : decode (s.mem.get s.c) s.c.modClass = .nop)
    (hcode : printableCode? (s.mem.get s.c) = some code) :
    step1 s = some { s with
      mem := s.mem.set s.c (Value.ofNat (encrypt code)),
      c := s.c.succ, d := s.d.succ } :=
  step1_eq hdec (by simp) (by simp) rfl hcode

/-! ## Straight-line runs of the crazy operation

The crazy operation is the only arithmetic a rot-free region has, so
straight-line arithmetic code is a row of consecutive `p` cells with `d`
walking a row of operands alongside. `crazy_run` executes any such row in
one induction: the accumulator computes a fold of `crz` over the operand
cells, the operand cells hold the intermediate results, the code cells
hold their own encryptions, and nothing else changes. The branch gadget is
this lemma at `k = 7`. -/

theorem run?_add (m n : Nat) (s : State) :
    run? (m + n) s = (run? m s).bind (run? n) := by
  induction m generalizing s with
  | zero => simp [run?]
  | succ m ih =>
    rw [show m + 1 + n = (m + n) + 1 by omega]
    show (step1 s).bind (run? (m + n)) = ((step1 s).bind (run? m)).bind (run? n)
    rw [Option.bind_assoc]
    cases step1 s with
    | none => rfl
    | some s' => simp only [Option.bind_some]; exact ih s'

theorem run?_one (s : State) : run? 1 s = step1 s := by
  show (step1 s).bind (run? 0) = step1 s
  cases step1 s <;> rfl

/-- The fold a row of `k` crazy operations computes: each step combines the
accumulator with the *original* contents of the next operand cell (the run
never revisits an operand, so the initial memory is the right thing to
fold over). -/
def crzFold (m : Memory) (d₀ : Nat) (a : Value) : Nat → Value
  | 0 => a
  | j + 1 => Value.crz (crzFold m d₀ a j) (m.get (Value.ofNat (d₀ + j)))

/-- **A row of crazy cells is a fold.** From `c = c₀, d = d₀`, if the `k`
cells at `c₀, …, c₀+k-1` decode to `p` and are printable, and the code row
is disjoint from the operand row (`c₀ + k ≤ d₀`), then the run survives
`k` steps and ends with: the folded accumulator; each operand cell holding
its intermediate; each code cell encrypted once; everything else
untouched. -/
theorem crazy_run (k : Nat) {s₀ : State} {c₀ d₀ : Nat} (w : Nat → Nat)
    (hc : s₀.c = Value.ofNat c₀) (hd : s₀.d = Value.ofNat d₀)
    (hsep : c₀ + k ≤ d₀)
    (hdec : ∀ i < k, decode (s₀.mem.get (Value.ofNat (c₀ + i)))
      (Value.ofNat (c₀ + i)).modClass = .crazy)
    (hprint : ∀ i < k, printableCode? (s₀.mem.get (Value.ofNat (c₀ + i)))
      = some (w i)) :
    ∃ s', run? k s₀ = some s'
      ∧ s'.a = crzFold s₀.mem d₀ s₀.a k
      ∧ s'.c = Value.ofNat (c₀ + k)
      ∧ s'.d = Value.ofNat (d₀ + k)
      ∧ (∀ j < k, s'.mem.get (Value.ofNat (d₀ + j)) = crzFold s₀.mem d₀ s₀.a (j + 1))
      ∧ (∀ i < k, s'.mem.get (Value.ofNat (c₀ + i)) = Value.ofNat (encrypt (w i)))
      ∧ (∀ addr, (∀ i < k, addr ≠ Value.ofNat (c₀ + i)) →
          (∀ j < k, addr ≠ Value.ofNat (d₀ + j)) → s'.mem.get addr = s₀.mem.get addr)
      ∧ s'.input = s₀.input ∧ s'.output = s₀.output ∧ s'.outClosed = s₀.outClosed
      ∧ s'.rotWidth = s₀.rotWidth ∧ s'.maxWidth = s₀.maxWidth := by
  induction k with
  | zero =>
    refine ⟨s₀, rfl, rfl, by simpa using hc, by simpa using hd,
      fun j hj => absurd hj (by omega), fun i hi => absurd hi (by omega),
      fun addr _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩
  | succ k ih =>
    obtain ⟨sk, hrun, hA, hC, hD, hDs, hCs, hframe, hin, hout, hoc, hrw, hmw⟩ :=
      ih (by omega) (fun i hi => hdec i (by omega)) (fun i hi => hprint i (by omega))
    -- the cell about to execute is untouched: it is not among the first k
    -- code cells nor among the first k operand cells
    have hcell : sk.mem.get (Value.ofNat (c₀ + k)) = s₀.mem.get (Value.ofNat (c₀ + k)) :=
      hframe _ (fun i hi => ofNat_ne (by omega)) (fun j hj => ofNat_ne (by omega))
    have hoper : sk.mem.get (Value.ofNat (d₀ + k)) = s₀.mem.get (Value.ofNat (d₀ + k)) :=
      hframe _ (fun i hi => ofNat_ne (by omega)) (fun j hj => ofNat_ne (by omega))
    have hstep := step1_crazy (s := sk) (code := w k)
      (by rw [hC, hcell]; exact hdec k (by omega))
      (by rw [hC, hD]; exact ofNat_ne (by omega))
      (by rw [hC, hcell]; exact hprint k (by omega))
    -- name the two writes
    set res := Value.crz sk.a (sk.mem.get sk.d) with hres
    have hresEq : res = crzFold s₀.mem d₀ s₀.a (k + 1) := by
      rw [hres, hA, hD, hoper]
      rfl
    set snext : State := { sk with a := res, mem := (sk.mem.set sk.d res).set sk.c (Value.ofNat (encrypt (w k))), c := sk.c.succ, d := sk.d.succ } with hsnext
    have hrun' : run? (k + 1) s₀ = some snext := by
      rw [run?_add k 1, hrun, Option.bind_some, run?_one]
      exact hstep
    refine ⟨snext, hrun', hresEq, ?_, ?_, ?_, ?_, ?_, hin, hout, hoc, hrw, hmw⟩
    · show sk.c.succ = _
      rw [hC, succ_ofNat, Nat.add_assoc]
    · show sk.d.succ = _
      rw [hD, succ_ofNat, Nat.add_assoc]
    · -- operand cells: the new write at d₀+k, older ones framed
      intro j hj
      show ((sk.mem.set sk.d res).set sk.c (Value.ofNat (encrypt (w k)))).get
        (Value.ofNat (d₀ + j)) = _
      rw [get_set_ne _ (by rw [hC]; exact ofNat_ne (by omega))]
      by_cases hjk : j = k
      · subst hjk
        rw [hD, get_set_self]
        exact hresEq
      · rw [get_set_ne _ (by rw [hD]; exact ofNat_ne (by omega))]
        exact hDs j (by omega)
    · -- code cells: the new encryption at c₀+k, older ones framed
      intro i hi
      show ((sk.mem.set sk.d res).set sk.c (Value.ofNat (encrypt (w k)))).get
        (Value.ofNat (c₀ + i)) = _
      by_cases hik : i = k
      · subst hik
        rw [hC, get_set_self]
      · rw [get_set_ne _ (by rw [hC]; exact ofNat_ne (by omega)),
          get_set_ne _ (by rw [hD]; exact ofNat_ne (by omega))]
        exact hCs i (by omega)
    · -- frame
      intro addr hac had
      show ((sk.mem.set sk.d res).set sk.c (Value.ofNat (encrypt (w k)))).get addr = _
      rw [get_set_ne _ (by rw [hC]; exact (hac k (by omega)).symm),
        get_set_ne _ (by rw [hD]; exact (had k (by omega)).symm)]
      exact hframe addr (fun i hi => hac i (by omega)) (fun j hj => had j (by omega))

/-! ## The branch gadget

The machine half of `branch_arith`: eight instructions that leave a
computed jump target under `d`. Seven `p` cells run the branch pipeline
while `d` walks the seven constants; the constants end spent (each holds
an intermediate of the chain), the result lands in the cell that held
`k₄`; then one `j`-style `movd` cell reads a pointer laid at `d₀+7` and
re-aims `d` back at that result. A subsequent `jmp` (`step1_jmp`) reads
the target and completes the branch; that step is generic and left to the
caller, because the caller owns the landing sites. -/

theorem branch_gadget (t₀ t₁ : Value) {s₀ : State} {c₀ d₀ : Nat}
    (w : Nat → Nat) {flag : Value}
    (hc : s₀.c = Value.ofNat c₀) (hd : s₀.d = Value.ofNat d₀)
    (hsep : c₀ + 8 ≤ d₀)
    (hdec : ∀ i < 7, decode (s₀.mem.get (Value.ofNat (c₀ + i)))
      (Value.ofNat (c₀ + i)).modClass = .crazy)
    (hmovd : decode (s₀.mem.get (Value.ofNat (c₀ + 7)))
      (Value.ofNat (c₀ + 7)).modClass = .movd)
    (hprint : ∀ i < 8, printableCode? (s₀.mem.get (Value.ofNat (c₀ + i)))
      = some (w i))
    (hK0 : s₀.mem.get (Value.ofNat d₀) = Value.eof)
    (hK1 : s₀.mem.get (Value.ofNat (d₀ + 1)) = Value.zero)
    (hKf : s₀.mem.get (Value.ofNat (d₀ + 2)) = flag)
    (hKk1 : s₀.mem.get (Value.ofNat (d₀ + 3)) = k1Of t₀ t₁)
    (hKk2 : s₀.mem.get (Value.ofNat (d₀ + 4)) = k2Of t₀ t₁)
    (hKk3 : s₀.mem.get (Value.ofNat (d₀ + 5)) = k3Of t₀ t₁)
    (hKk4 : s₀.mem.get (Value.ofNat (d₀ + 6)) = k4Of t₀ t₁)
    (hKp : s₀.mem.get (Value.ofNat (d₀ + 7)) = Value.ofNat (d₀ + 5)) :
    ∃ s', run? 8 s₀ = some s'
      ∧ s'.a = branchChain t₀ t₁ s₀.a flag
      ∧ s'.c = Value.ofNat (c₀ + 8)
      ∧ s'.d = Value.ofNat (d₀ + 6)
      ∧ s'.mem.get (Value.ofNat (d₀ + 6)) = branchChain t₀ t₁ s₀.a flag
      ∧ (∀ addr, (∀ i < 8, addr ≠ Value.ofNat (c₀ + i)) →
          (∀ j < 7, addr ≠ Value.ofNat (d₀ + j)) →
          s'.mem.get addr = s₀.mem.get addr)
      ∧ s'.input = s₀.input ∧ s'.output = s₀.output ∧ s'.outClosed = s₀.outClosed := by
  obtain ⟨s₇, hrun7, hA, hC, hD, hDs, hCs, hframe, hin, hout, hoc, hrw, hmw⟩ :=
    crazy_run 7 w hc hd (by omega) (fun i hi => hdec i hi)
      (fun i hi => hprint i (by omega))
  -- what the fold computed is exactly the branch pipeline
  have hfold : crzFold s₀.mem d₀ s₀.a 7 = branchChain t₀ t₁ s₀.a flag := by
    show Value.crz (Value.crz (Value.crz (Value.crz (Value.crz (Value.crz
      (Value.crz s₀.a (s₀.mem.get (Value.ofNat (d₀ + 0))))
      (s₀.mem.get (Value.ofNat (d₀ + 1)))) (s₀.mem.get (Value.ofNat (d₀ + 2))))
      (s₀.mem.get (Value.ofNat (d₀ + 3)))) (s₀.mem.get (Value.ofNat (d₀ + 4))))
      (s₀.mem.get (Value.ofNat (d₀ + 5)))) (s₀.mem.get (Value.ofNat (d₀ + 6)))
      = branchChain t₀ t₁ s₀.a flag
    rw [show d₀ + 0 = d₀ from rfl, hK0, hK1, hKf, hKk1, hKk2, hKk3, hKk4]
    rfl
  -- the movd cell and its pointer operand are untouched by the seven steps
  have hcell7 : s₇.mem.get (Value.ofNat (c₀ + 7)) = s₀.mem.get (Value.ofNat (c₀ + 7)) :=
    hframe _ (fun i hi => ofNat_ne (by omega)) (fun j hj => ofNat_ne (by omega))
  have hop7 : s₇.mem.get (Value.ofNat (d₀ + 7)) = Value.ofNat (d₀ + 5) := by
    rw [hframe _ (fun i hi => ofNat_ne (by omega)) (fun j hj => ofNat_ne (by omega))]
    exact hKp
  have hstep := step1_movd (s := s₇) (code := w 7)
    (by rw [hC, hcell7]; exact hmovd)
    (by rw [hC, hcell7]; exact hprint 7 (by omega))
  rw [hD, hop7, hC] at hstep
  rw [succ_ofNat, succ_ofNat, show c₀ + 7 + 1 = c₀ + 8 by omega,
    show d₀ + 5 + 1 = d₀ + 6 by omega] at hstep
  set s₈ : State := { s₇ with mem := s₇.mem.set (Value.ofNat (c₀ + 7)) (Value.ofNat (encrypt (w 7))), c := Value.ofNat (c₀ + 8), d := Value.ofNat (d₀ + 6), maxWidth := if (Value.ofNat (d₀ + 5)).width > s₇.maxWidth then (Value.ofNat (d₀ + 5)).width else s₇.maxWidth, rotWidth := if (Value.ofNat (d₀ + 5)).width > s₇.maxWidth then growRotWidth s₇.rotWidth (Value.ofNat (d₀ + 5)).width else s₇.rotWidth } with hs₈
  have hrun8 : run? 8 s₀ = some s₈ := by
    rw [show (8 : Nat) = 7 + 1 from rfl, run?_add 7 1, hrun7, Option.bind_some,
      run?_one]
    exact hstep
  refine ⟨s₈, hrun8, ?_, rfl, rfl, ?_, ?_, hin, hout, hoc⟩
  · show s₇.a = _
    rw [hA]
    exact hfold
  · show (s₇.mem.set (Value.ofNat (c₀ + 7)) (Value.ofNat (encrypt (w 7)))).get
      (Value.ofNat (d₀ + 6)) = _
    rw [get_set_ne _ (ofNat_ne (by omega)), show d₀ + 6 = d₀ + 6 from rfl,
      hDs 6 (by omega)]
    exact hfold
  · intro addr hac had
    show (s₇.mem.set (Value.ofNat (c₀ + 7)) (Value.ofNat (encrypt (w 7)))).get addr = _
    rw [get_set_ne _ (Ne.symm (hac 7 (by omega)))]
    exact hframe addr (fun i hi => hac i (by omega)) had

/-- The two cases of the gadget, read through `branch_arith`: the flag cell
decides which of the two targets is under `d` afterwards. -/
theorem branch_gadget_cases {t₀ t₁ : Value} (h₀ : t₀.Normalized) (h₁ : t₁.Normalized)
    {a : Value} {flag : Value} :
    (flag = Value.zero → branchChain t₀ t₁ a flag = t₀)
    ∧ (flag = Value.eof → branchChain t₀ t₁ a flag = t₁) :=
  ⟨fun h => h ▸ (branch_arith t₀ t₁ h₀ h₁ a).1,
   fun h => h ▸ (branch_arith t₀ t₁ h₀ h₁ a).2⟩

/-! ## The copy algebra: moving a value you do not know

`branch_arith` writes compile-time constants; a register machine also has
to *move* runtime values between cells. The crazy operation offers exactly
two per-trit bijections: reading through `...222` (the row `x = 2` of the
table is the permutation swapping 1 and 2) and writing through `...111`
(the column `y = 1` swaps 0 and 1). One read-write hop therefore applies
the 3-cycle `0 ↦ 1 ↦ 2 ↦ 0` to every trit; three hops are the identity,
and a value can be copied exactly, three cells downstream, without ever
being known. The two constants involved, `...222` and `...111`, are
self-restoring in the read (`crz eof v` overwrites the source cell with
the read image, but the `...222` accumulator load `crz zero eof = eof`
restores its own cell), so the only consumed cell per hop is the source,
which a copy is allowed to consume. -/

/-- Apply a trit function to every trit of a value. -/
def vmap (f : Trit → Trit) (v : Value) : Value :=
  Value.mk' (f v.lead) (v.low.map f)

theorem trit_vmap (f : Trit → Trit) (v : Value) (i : Nat) :
    (vmap f v).trit i = f (v.trit i) := by
  rw [vmap, trit_mk', Value.trit]
  rcases Nat.lt_or_ge i v.low.length with h | h
  · rw [getD_lt (by simpa using h), getD_lt h, List.getElem_map]
  · rw [getD_ge (by simpa using h), getD_ge h]

theorem vmap_normalized (f : Trit → Trit) (v : Value) : (vmap f v).Normalized :=
  Value.normalized_mk' _ _

/-- The 3-cycle a read-write hop applies: `0 ↦ 1 ↦ 2 ↦ 0`. -/
def tau : Trit → Trit
  | .t0 => .t1
  | .t1 => .t2
  | .t2 => .t0

/-- One hop: read the source through `...222` (the accumulator becomes the
`swap12` image, and is what the crazy operation also left in the source
cell), then write through a cell holding `...111`. -/
def hop (v : Value) : Value := Value.crz (Value.crz Value.eof v) (uniform .t1)

/-- A hop is the 3-cycle, tritwise. -/
theorem hop_eq_vmap (v : Value) : hop v = vmap tau v := by
  refine ext_of_trits (crz_normalized _ _) (vmap_normalized _ _) ?_ ?_
  · show crzTrit (crzTrit Trit.t2 v.lead) Trit.t1 = tau v.lead
    cases v.lead <;> rfl
  · intro i
    rw [trit_vmap]
    show (Value.crz (Value.crz Value.eof v) (uniform .t1)).trit i = tau (v.trit i)
    rw [crz_trit, crz_trit]
    show crzTrit (crzTrit ((uniform .t2).trit i) (v.trit i)) ((uniform .t1).trit i)
      = tau (v.trit i)
    rw [trit_uniform, trit_uniform]
    cases v.trit i <;> rfl

theorem vmap_vmap (f g : Trit → Trit) (v : Value) :
    vmap f (vmap g v) = vmap (f ∘ g) v := by
  refine ext_of_trits (vmap_normalized _ _) (vmap_normalized _ _) ?_ ?_
  · show f ((vmap g v).lead) = (f ∘ g) v.lead
    show f (g v.lead) = f (g v.lead)
    rfl
  · intro i
    rw [trit_vmap, trit_vmap, trit_vmap]
    rfl

theorem vmap_id {f : Trit → Trit} (hf : ∀ t, f t = t) {v : Value}
    (hv : v.Normalized) : vmap f v = v := by
  refine ext_of_trits (vmap_normalized _ _) hv ?_ ?_
  · exact hf v.lead
  · intro i
    rw [trit_vmap]
    exact hf (v.trit i)

/-- **Three hops copy exactly.** The 3-cycle cubed is the identity, so a
value passed through three read-write hops arrives unchanged, without the
program ever knowing what it was. -/
theorem hop_hop_hop {v : Value} (hv : v.Normalized) : hop (hop (hop v)) = v := by
  rw [hop_eq_vmap, hop_eq_vmap, hop_eq_vmap, vmap_vmap, vmap_vmap]
  exact vmap_id (fun t => by cases t <;> rfl) hv

/-! ## Why the unbounded part cannot live in fresh memory

`widthBounded_step1` says a rot-free run keeps every storable value in a
finite alphabet, so rotation is mandatory for unbounded storage. The
tempting way to dodge self-encryption is then to put the unbounded
computation in memory the loader never wrote and *never re-execute a cell*:
a compiler builds its `Image` directly, so unlike a loaded program it may
choose all six entries of `rest` and make fresh memory executable.

The addresses of one such phase are the naturals congruent to `j` modulo 6,
all holding the same word, so their opcodes are `(w + a) mod 94` as `a`
runs through that phase. Two consequences, and they are what close the
question. Opcodes in a phase all have the same parity, because addresses in
a phase do; the four even opcodes are `jmp`, `movd`, `crazy` and `nop`, and
the four odd ones are `out`, `inp`, `rotr` and `halt`. So a phase that can
rotate is a phase that can halt, and precisely:

```lean
theorem rotr_forces_halt … (hrot : decode (Value.ofNat w) (Value.ofNat a).modClass = .rotr) :
    (a + 42) % 6 = a % 6
    ∧ decode (Value.ofNat w) (Value.ofNat (a + 42)).modClass = .halt
```

`81 - 39 = 42`, and 42 is a multiple of 6, so the halt sits in the *same*
phase, 42 addresses along. A compiler that runs its unbounded computation
through fresh memory must therefore either forgo rotation, and with it
unbounded storage, or steer past a halt every 42 addresses of every
rotating phase. That is not a contradiction, and this file does not claim
one; it is a standing tax that makes the finite self-modifying code region,
with its `xlat2` orbits managed across passes, the cheaper architecture.
`docs/malbolge-unshackled/compiler.md` records the decision. -/

/-- Reading an opcode back off a decoded instruction. -/
theorem opcode_of_decode {w a : Nat} (h₁ : 33 ≤ w) (h₂ : w ≤ 126) {instr : Instr}
    (hdec : decode (Value.ofNat w) (Value.ofNat a).modClass = instr)
    (hne : instr ≠ .nop) : (w + a) % 94 = opcodeOf instr := by
  rw [decode_at_ofNat h₁ h₂] at hdec
  cases hq : Instr.ofOpcode? ((w + a) % 94) with
  | none => rw [hq] at hdec; exact absurd hdec.symm hne
  | some i =>
    rw [hq] at hdec
    simp only [Option.getD_some] at hdec
    subst hdec
    exact (opcodeOf_ofOpcode? hq).symm

/-- Every address of one virgin phase holds the same word, so their opcodes
share a parity. -/
theorem virgin_phase_parity (w a a' : Nat) (h : a % 2 = a' % 2) :
    ((w + a) % 94) % 2 = ((w + a') % 94) % 2 := by omega

/-- **A virgin phase that can rotate can also halt**, 42 addresses along
and in the same phase. Rotation is the language's only source of
unboundedly wide values (`widthBounded_step1`), so a compiler that puts its
unbounded computation in never-re-executed fresh memory pays this tax
everywhere it rotates. -/
theorem rotr_forces_halt {w a : Nat} (h₁ : 33 ≤ w) (h₂ : w ≤ 126)
    (hrot : decode (Value.ofNat w) (Value.ofNat a).modClass = .rotr) :
    (a + 42) % 6 = a % 6
    ∧ decode (Value.ofNat w) (Value.ofNat (a + 42)).modClass = .halt := by
  have h39 : (w + a) % 94 = 39 := opcode_of_decode h₁ h₂ hrot (by simp)
  refine ⟨by omega, ?_⟩
  rw [decode_at_ofNat h₁ h₂, show (w + (a + 42)) % 94 = 81 by omega]
  rfl

/-- The converse direction of the same arithmetic: a phase offering `halt`
offers `rotr` 42 addresses earlier, so the two really are inseparable. -/
theorem halt_forces_rotr {w a : Nat} (h₁ : 33 ≤ w) (h₂ : w ≤ 126)
    (hhalt : decode (Value.ofNat w) (Value.ofNat (a + 42)).modClass = .halt) :
    decode (Value.ofNat w) (Value.ofNat a).modClass = .rotr := by
  have h81 : (w + (a + 42)) % 94 = 81 := opcode_of_decode h₁ h₂ hhalt (by simp)
  rw [decode_at_ofNat h₁ h₂, show (w + a) % 94 = 39 by omega]
  rfl

/-! ## Re-enterable rows: the nop sweep

`loop.mu` restores its `movd` cell by having it both executed and jumped
onto in one pass, two orbit steps, which a word from the `70 ↔ 74` cycle
survives. The general form of that trick needs no jumps at all. A cell
holding a two-cycle word alternates *instruction, no-op*, so a row of such
cells run **twice** — once doing its work, once as no-ops — comes back to
exactly where it started, and the row is re-enterable.

`crazy_run` executes the work sweep. `nop_run` here executes the no-op
sweep, and `encrypt_encrypt_two_cycle` is the arithmetic that closes the
circle. Unlike `crazy_run` this lemma constrains `d` not at all: a no-op
reads no operand, so wherever `d` happens to be it simply advances, and the
frame covers every address outside the code row. -/

theorem encrypt_encrypt_two_cycle {w : Nat} (h : w = 70 ∨ w = 74) :
    encrypt (encrypt w) = w := by
  rcases h with h | h <;> subst h <;> rfl

/-- **A row of no-op cells sweeps in one induction.** The accumulator, the
input and the output are untouched, `c` advances by `k`, `d` advances by
`k` successors from wherever it was, each cell is replaced by its own
encryption, and every other address is unchanged. -/
theorem nop_run (k : Nat) {s₀ : State} {c₀ : Nat} (w : Nat → Nat)
    (hc : s₀.c = Value.ofNat c₀)
    (hdec : ∀ i < k, decode (s₀.mem.get (Value.ofNat (c₀ + i)))
      (Value.ofNat (c₀ + i)).modClass = .nop)
    (hprint : ∀ i < k, printableCode? (s₀.mem.get (Value.ofNat (c₀ + i)))
      = some (w i)) :
    ∃ s', run? k s₀ = some s'
      ∧ s'.a = s₀.a
      ∧ s'.c = Value.ofNat (c₀ + k)
      ∧ s'.d = (Value.succ^[k]) s₀.d
      ∧ (∀ i < k, s'.mem.get (Value.ofNat (c₀ + i)) = Value.ofNat (encrypt (w i)))
      ∧ (∀ addr, (∀ i < k, addr ≠ Value.ofNat (c₀ + i)) →
          s'.mem.get addr = s₀.mem.get addr)
      ∧ s'.input = s₀.input ∧ s'.output = s₀.output ∧ s'.outClosed = s₀.outClosed
      ∧ s'.rotWidth = s₀.rotWidth ∧ s'.maxWidth = s₀.maxWidth := by
  induction k with
  | zero =>
    exact ⟨s₀, rfl, rfl, by simpa using hc, rfl,
      fun i hi => absurd hi (by omega), fun addr _ => rfl, rfl, rfl, rfl, rfl, rfl⟩
  | succ k ih =>
    obtain ⟨sk, hrun, hA, hC, hD, hCs, hframe, hin, hout, hoc, hrw, hmw⟩ :=
      ih (fun i hi => hdec i (by omega)) (fun i hi => hprint i (by omega))
    have hcell : sk.mem.get (Value.ofNat (c₀ + k)) = s₀.mem.get (Value.ofNat (c₀ + k)) :=
      hframe _ (fun i hi => ofNat_ne (by omega))
    have hstep := step1_nop (s := sk) (code := w k)
      (by rw [hC, hcell]; exact hdec k (by omega))
      (by rw [hC, hcell]; exact hprint k (by omega))
    set snext : State := { sk with mem := sk.mem.set sk.c (Value.ofNat (encrypt (w k))), c := sk.c.succ, d := sk.d.succ } with hsnext
    have hrun' : run? (k + 1) s₀ = some snext := by
      rw [run?_add k 1, hrun, Option.bind_some, run?_one]
      exact hstep
    refine ⟨snext, hrun', hA, ?_, ?_, ?_, ?_, hin, hout, hoc, hrw, hmw⟩
    · show sk.c.succ = _
      rw [hC, succ_ofNat, Nat.add_assoc]
    · show sk.d.succ = _
      rw [hD, Function.iterate_succ_apply']
    · intro i hi
      show (sk.mem.set sk.c (Value.ofNat (encrypt (w k)))).get (Value.ofNat (c₀ + i)) = _
      by_cases hik : i = k
      · subst hik; rw [hC, get_set_self]
      · rw [get_set_ne _ (by rw [hC]; exact ofNat_ne (by omega))]
        exact hCs i (by omega)
    · intro addr hac
      show (sk.mem.set sk.c (Value.ofNat (encrypt (w k)))).get addr = _
      rw [get_set_ne _ (by rw [hC]; exact (hac k (by omega)).symm)]
      exact hframe addr (fun i hi => hac i (by omega))

/-- **A two-cycle row is restored by the sweep that follows it.** If every
cell of the row held a word of the `70 ↔ 74` cycle before the work sweep,
then after the work sweep (which encrypted each once) and the no-op sweep
(which encrypts each again) the row holds exactly its original words: the
gadget is ready to run again. -/
theorem row_restored {m : Memory} {c₀ k : Nat} {v : Nat → Nat}
    (hcycle : ∀ i < k, v i = 70 ∨ v i = 74)
    (hbefore : ∀ i < k, m.get (Value.ofNat (c₀ + i)) = Value.ofNat (v i))
    {m' : Memory}
    (hafter : ∀ i < k, m'.get (Value.ofNat (c₀ + i))
      = Value.ofNat (encrypt (encrypt (v i)))) :
    ∀ i < k, m'.get (Value.ofNat (c₀ + i)) = m.get (Value.ofNat (c₀ + i)) := by
  intro i hi
  rw [hafter i hi, hbefore i hi, encrypt_encrypt_two_cycle (hcycle i hi)]

/-! ## Terminating runs

`neverHalts_of_invariant` covers loops that must not stop. A simulation
needs the opposite: the compiled program has to *halt*, with the right
output, whenever the machine it simulates does. Three pieces.

`exec_run?_add` splits a run at any point, so a proof can reason gadget by
gadget and stitch the pieces together. `exec_halts_of_run?` is the ending:
a run that reaches a cell decoding to `halt` reports `Exit.halted`, which is
what `TuringComplete` demands. And `run_of_measure` is the loop rule: an
invariant, a measure that strictly decreases each time round, and an exit
condition at zero. Together they are the shape a simulation proof takes,
with `run_of_measure` carrying the simulated machine's remaining step count
as the measure. -/

/-- A run splits anywhere: `n` steps of `run?` followed by `m` of `exec`. -/
theorem exec_run?_add : ∀ {n : Nat} {s t : State}, run? n s = some t →
    ∀ m, exec (n + m) s = exec m t
  | 0, s, t, h, m => by
    simp only [run?, Option.some.injEq] at h
    subst h
    simp
  | n + 1, s, t, h, m => by
    simp only [run?] at h
    cases hs : step1 s with
    | none => rw [hs] at h; simp at h
    | some s' =>
      rw [hs] at h
      simp only [Option.bind_some] at h
      rw [show n + 1 + m = (n + m) + 1 by omega, step1_sound hs (n + m)]
      exact exec_run?_add h m

/-- **The ending a simulation needs.** A run that survives `n` steps and
arrives at a cell decoding to `halt` reports `Exit.halted`, with the output
the run accumulated. -/
theorem exec_halts_of_run? {n : Nat} {s t : State} (h : run? n s = some t)
    (hhalt : decode (t.mem.get t.c) t.c.modClass = .halt) :
    exec (n + 1) s = (t, Exit.halted) := by
  rw [exec_run?_add h 1]
  exact exec_halt 0 hhalt

/-- The same at the language interface: the image halts, and the output is
the one the run produced. -/
theorem image_halts_of_run? {img : Image} {input : Input} {n : Nat} {t : State}
    (h : run? n (initialState img input) = some t)
    (hhalt : decode (t.mem.get t.c) t.c.modClass = .halt) :
    evalImage {} img input (n + 1) = { output := t.output, exit := Exit.halted } := by
  show (fun (r : State × Exit) => ({ output := r.1.output, exit := r.2 } : RunResult))
      (exec (n + 1) (initialState img input)) = _
  rw [exec_halts_of_run? h hhalt]

/-- **The loop rule.** An invariant `P`, a measure `μ` that strictly
decreases on each pass, and an exit predicate `Q` that holds when the
measure runs out: then the run reaches a state satisfying `Q` in finitely
many steps. This is how a simulation discharges a bounded loop, with `μ`
the number of steps the simulated machine has left. -/
theorem run_of_measure {P Q : State → Prop} {μ : State → Nat}
    (hstep : ∀ s, P s → μ s ≠ 0 →
      ∃ k s', run? k s = some s' ∧ P s' ∧ μ s' < μ s)
    (hexit : ∀ s, P s → μ s = 0 → Q s) :
    ∀ s, P s → ∃ n t, run? n s = some t ∧ Q t := by
  intro s hs
  -- strong induction on the measure
  suffices h : ∀ b s, P s → μ s ≤ b → ∃ n t, run? n s = some t ∧ Q t from
    h (μ s) s hs (Nat.le_refl _)
  intro b
  induction b with
  | zero =>
    intro s hs hb
    exact ⟨0, s, rfl, hexit s hs (by omega)⟩
  | succ b ih =>
    intro s hs hb
    by_cases hz : μ s = 0
    · exact ⟨0, s, rfl, hexit s hs hz⟩
    · obtain ⟨k, s', hrun, hP', hlt⟩ := hstep s hs hz
      obtain ⟨n, t, hrun', hQ⟩ := ih s' hP' (by omega)
      exact ⟨k + n, t, by rw [run?_add, hrun, Option.bind_some]; exact hrun', hQ⟩

/-! ### The flag a branch reads

`branch_arith` takes its decision from a cell holding `...000` or `...222`.
Those are `Value.zero` and `Value.eof`, so a register cell that stores a
unary digit as "blank or mark" with exactly that encoding **is** a branch
flag: testing it costs no instructions at all. This matters because the
crazy operation is tritwise and cannot aggregate information across trit
positions, so a zero test on a wide value would need rotations and a loop,
while a zero test on a blank-or-mark cell needs nothing. -/

theorem flag_zero_is_blank : Value.zero = uniform .t0 := rfl

theorem flag_eof_is_mark : Value.eof = uniform .t2 := rfl

/-- Reading a blank-or-mark cell decides a branch outright. -/
theorem branch_on_mark (t₀ t₁ : Value) (h₀ : t₀.Normalized) (h₁ : t₁.Normalized)
    (a : Value) {flag : Value} (hflag : flag = Value.zero ∨ flag = Value.eof) :
    branchChain t₀ t₁ a flag = if flag = Value.zero then t₀ else t₁ := by
  rcases hflag with h | h <;> subst h
  · rw [if_pos rfl]; exact (branch_arith t₀ t₁ h₀ h₁ a).1
  · rw [if_neg (by decide)]; exact (branch_arith t₀ t₁ h₀ h₁ a).2

/-! ## Mixed rows

`crazy_run` executes a row of consecutive `p` cells and `nop_run` a row of
consecutive no-ops. Neither is quite what a gadget looks like, because a
`crazy` cell that is to be re-enterable must sit at residue 82 or 86 modulo
94, so the working cells of a gadget are *not* adjacent: they are spaced,
with padding between. `row_run` is the general straight-line executor, a
row of `L` consecutive cells each of which is either a `p` or a no-op,
selected by a Boolean. It subsumes both special cases and is what the
gadget proofs actually use.

The accumulator computes `rowFold`, a fold of the crazy operation over the
operand cells at the working positions only; padding advances `d` past its
operand without touching it. -/

/-- The fold a mixed row computes: the crazy operation is applied at the
working positions and skipped at the padding. -/
def rowFold (m : Memory) (d₀ : Nat) (isC : Nat → Bool) (a : Value) : Nat → Value
  | 0 => a
  | j + 1 =>
    if isC j then Value.crz (rowFold m d₀ isC a j) (m.get (Value.ofNat (d₀ + j)))
    else rowFold m d₀ isC a j

/-- **A mixed straight-line row executes in one induction.** Working cells
consume their operand and fold it into the accumulator; padding cells leave
their operand alone. Every executed cell is replaced by its own encryption,
and everything outside the code row and the operand row is untouched. -/
theorem row_run (L : Nat) {s₀ : State} {c₀ d₀ : Nat} (isC : Nat → Bool) (w : Nat → Nat)
    (hc : s₀.c = Value.ofNat c₀) (hd : s₀.d = Value.ofNat d₀)
    (hsep : c₀ + L ≤ d₀)
    (hdec : ∀ i < L, decode (s₀.mem.get (Value.ofNat (c₀ + i)))
      (Value.ofNat (c₀ + i)).modClass = if isC i then .crazy else .nop)
    (hprint : ∀ i < L, printableCode? (s₀.mem.get (Value.ofNat (c₀ + i)))
      = some (w i)) :
    ∃ s', run? L s₀ = some s'
      ∧ s'.a = rowFold s₀.mem d₀ isC s₀.a L
      ∧ s'.c = Value.ofNat (c₀ + L)
      ∧ s'.d = Value.ofNat (d₀ + L)
      ∧ (∀ j, j < L → isC j = true →
          s'.mem.get (Value.ofNat (d₀ + j)) = rowFold s₀.mem d₀ isC s₀.a (j + 1))
      ∧ (∀ j < L, isC j = false →
          s'.mem.get (Value.ofNat (d₀ + j)) = s₀.mem.get (Value.ofNat (d₀ + j)))
      ∧ (∀ i < L, s'.mem.get (Value.ofNat (c₀ + i)) = Value.ofNat (encrypt (w i)))
      ∧ (∀ addr, (∀ i < L, addr ≠ Value.ofNat (c₀ + i)) →
          (∀ j < L, addr ≠ Value.ofNat (d₀ + j)) → s'.mem.get addr = s₀.mem.get addr)
      ∧ s'.input = s₀.input ∧ s'.output = s₀.output ∧ s'.outClosed = s₀.outClosed
      ∧ s'.rotWidth = s₀.rotWidth ∧ s'.maxWidth = s₀.maxWidth := by
  induction L with
  | zero =>
    refine ⟨s₀, rfl, rfl, by simpa using hc, by simpa using hd,
      fun j hj _ => absurd hj (by omega), fun j hj _ => absurd hj (by omega),
      fun i hi => absurd hi (by omega), fun addr _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩
  | succ L ih =>
    obtain ⟨sL, hrun, hA, hC, hD, hDc, hDn, hCs, hframe, hin, hout, hoc, hrw, hmw⟩ :=
      ih (by omega) (fun i hi => hdec i (by omega)) (fun i hi => hprint i (by omega))
    have hcell : sL.mem.get (Value.ofNat (c₀ + L)) = s₀.mem.get (Value.ofNat (c₀ + L)) :=
      hframe _ (fun i hi => ofNat_ne (by omega)) (fun j hj => ofNat_ne (by omega))
    have hoper : sL.mem.get (Value.ofNat (d₀ + L)) = s₀.mem.get (Value.ofNat (d₀ + L)) :=
      hframe _ (fun i hi => ofNat_ne (by omega)) (fun j hj => ofNat_ne (by omega))
    have hdecL := hdec L (by omega)
    have hprintL := hprint L (by omega)
    cases hsel : isC L with
    | true =>
      -- a working cell: one crazy step
      have hstep := step1_crazy (s := sL) (code := w L)
        (by rw [hC, hcell, hdecL, hsel]; rfl)
        (by rw [hC, hD]; exact ofNat_ne (by omega))
        (by rw [hC, hcell]; exact hprintL)
      set res := Value.crz sL.a (sL.mem.get sL.d) with hres
      have hresEq : res = rowFold s₀.mem d₀ isC s₀.a (L + 1) := by
        rw [hres, hA, hD, hoper]
        show _ = if isC L then _ else _
        rw [hsel]
        rfl
      set snext : State := { sL with a := res, mem := (sL.mem.set sL.d res).set sL.c (Value.ofNat (encrypt (w L))), c := sL.c.succ, d := sL.d.succ } with hsnext
      have hrun' : run? (L + 1) s₀ = some snext := by
        rw [run?_add L 1, hrun, Option.bind_some, run?_one]; exact hstep
      refine ⟨snext, hrun', hresEq, ?_, ?_, ?_, ?_, ?_, ?_, hin, hout, hoc, hrw, hmw⟩
      · show sL.c.succ = _; rw [hC, succ_ofNat, Nat.add_assoc]
      · show sL.d.succ = _; rw [hD, succ_ofNat, Nat.add_assoc]
      · intro j hj hjc
        show ((sL.mem.set sL.d res).set sL.c (Value.ofNat (encrypt (w L)))).get
          (Value.ofNat (d₀ + j)) = _
        rw [get_set_ne _ (by rw [hC]; exact ofNat_ne (by omega))]
        by_cases hjL : j = L
        · subst hjL; rw [hD, get_set_self]; exact hresEq
        · rw [get_set_ne _ (by rw [hD]; exact ofNat_ne (by omega))]
          exact hDc j (by omega) hjc
      · intro j hj hjc
        show ((sL.mem.set sL.d res).set sL.c (Value.ofNat (encrypt (w L)))).get
          (Value.ofNat (d₀ + j)) = _
        have hjL : j ≠ L := by intro h; subst h; rw [hsel] at hjc; exact Bool.noConfusion hjc
        rw [get_set_ne _ (by rw [hC]; exact ofNat_ne (by omega)),
          get_set_ne _ (by rw [hD]; exact ofNat_ne (by omega))]
        exact hDn j (by omega) hjc
      · intro i hi
        show ((sL.mem.set sL.d res).set sL.c (Value.ofNat (encrypt (w L)))).get
          (Value.ofNat (c₀ + i)) = _
        by_cases hiL : i = L
        · subst hiL; rw [hC, get_set_self]
        · rw [get_set_ne _ (by rw [hC]; exact ofNat_ne (by omega)),
            get_set_ne _ (by rw [hD]; exact ofNat_ne (by omega))]
          exact hCs i (by omega)
      · intro addr hac had
        show ((sL.mem.set sL.d res).set sL.c (Value.ofNat (encrypt (w L)))).get addr = _
        rw [get_set_ne _ (by rw [hC]; exact (hac L (by omega)).symm),
          get_set_ne _ (by rw [hD]; exact (had L (by omega)).symm)]
        exact hframe addr (fun i hi => hac i (by omega)) (fun j hj => had j (by omega))
    | false =>
      -- padding: one no-op step
      have hstep := step1_nop (s := sL) (code := w L)
        (by rw [hC, hcell, hdecL, hsel]; rfl)
        (by rw [hC, hcell]; exact hprintL)
      set snext : State := { sL with mem := sL.mem.set sL.c (Value.ofNat (encrypt (w L))), c := sL.c.succ, d := sL.d.succ } with hsnext
      have hrun' : run? (L + 1) s₀ = some snext := by
        rw [run?_add L 1, hrun, Option.bind_some, run?_one]; exact hstep
      have hfoldEq : rowFold s₀.mem d₀ isC s₀.a (L + 1) = rowFold s₀.mem d₀ isC s₀.a L := by
        show (if isC L then _ else _) = _
        simp [hsel]
      refine ⟨snext, hrun', by rw [hfoldEq]; exact hA, ?_, ?_, ?_, ?_, ?_, ?_,
        hin, hout, hoc, hrw, hmw⟩
      · show sL.c.succ = _; rw [hC, succ_ofNat, Nat.add_assoc]
      · show sL.d.succ = _; rw [hD, succ_ofNat, Nat.add_assoc]
      · intro j hj hjc
        have hjL : j ≠ L := by intro h; subst h; rw [hsel] at hjc; exact Bool.noConfusion hjc
        show (sL.mem.set sL.c (Value.ofNat (encrypt (w L)))).get (Value.ofNat (d₀ + j)) = _
        rw [get_set_ne _ (by rw [hC]; exact ofNat_ne (by omega))]
        exact hDc j (by omega) hjc
      · intro j hj hjc
        show (sL.mem.set sL.c (Value.ofNat (encrypt (w L)))).get (Value.ofNat (d₀ + j)) = _
        rw [get_set_ne _ (by rw [hC]; exact ofNat_ne (by omega))]
        by_cases hjL : j = L
        · subst hjL; exact hoper
        · exact hDn j (by omega) hjc
      · intro i hi
        show (sL.mem.set sL.c (Value.ofNat (encrypt (w L)))).get (Value.ofNat (c₀ + i)) = _
        by_cases hiL : i = L
        · subst hiL; rw [hC, get_set_self]
        · rw [get_set_ne _ (by rw [hC]; exact ofNat_ne (by omega))]
          exact hCs i (by omega)
      · intro addr hac had
        show (sL.mem.set sL.c (Value.ofNat (encrypt (w L)))).get addr = _
        rw [get_set_ne _ (by rw [hC]; exact (hac L (by omega)).symm)]
        exact hframe addr (fun i hi => hac i (by omega)) (fun j hj => had j (by omega))

/-! ## The two-sweep gadget

Putting the pieces together. A gadget is a mixed row at `b+1 … b+L`
followed by one `jmp` cell at `b+L+1`, and it runs in `2L + 2` steps:

* the **work sweep** executes the row, folding the operands into the
  accumulator, and leaves every cell encrypted once;
* the `jmp` reads the first table entry, `b`, so control lands back on
  `b+1` — the jump encrypts `b`, never itself;
* the **no-op sweep** executes the same row again, now all no-ops,
  encrypting each cell a second time and so restoring the two-cycle words;
* the `jmp` reads the second table entry and control leaves.

`d` walks the operand row during the work sweep and walks past it during
the no-op sweep, which is why the two table entries sit at `d₀+L` and
`d₀+2L+1`. Because the gadget restores itself, it may be entered any
number of times, which is what makes a compiled loop body possible. -/

/-- A row of pure padding folds to nothing. -/
theorem rowFold_false (m : Memory) (d₀ : Nat) (a : Value) : ∀ L : Nat,
    rowFold m d₀ (fun _ => false) a L = a
  | 0 => rfl
  | L + 1 => by
    show (if (false : Bool) = true then _ else rowFold m d₀ (fun _ => false) a L) = a
    simp [rowFold_false m d₀ a L]

theorem two_sweep (L : Nat) {s₀ : State} {b d₀ E : Nat} (isC : Nat → Bool)
    (w : Nat → Nat) {wb wE : Nat}
    (hc : s₀.c = Value.ofNat (b + 1)) (hd : s₀.d = Value.ofNat d₀)
    (hsep : b + L + 2 ≤ d₀)
    -- the row, on entry
    (hdec : ∀ i < L, decode (s₀.mem.get (Value.ofNat (b + 1 + i)))
      (Value.ofNat (b + 1 + i)).modClass = if isC i then .crazy else .nop)
    (hprint : ∀ i < L, printableCode? (s₀.mem.get (Value.ofNat (b + 1 + i)))
      = some (w i))
    -- the row, on the second sweep: every cell is a no-op once encrypted
    (hdec2 : ∀ i < L, decode (Value.ofNat (encrypt (w i)))
      (Value.ofNat (b + 1 + i)).modClass = .nop)
    (hrange : ∀ i < L, 33 ≤ w i ∧ w i ≤ 126)
    -- the jump cell, stable throughout
    (hJdec : decode (s₀.mem.get (Value.ofNat (b + 1 + L)))
      (Value.ofNat (b + 1 + L)).modClass = .jmp)
    -- the two table entries
    (hT0 : s₀.mem.get (Value.ofNat (d₀ + L)) = Value.ofNat b)
    (hT1 : s₀.mem.get (Value.ofNat (d₀ + 2 * L + 1)) = Value.ofNat E)
    -- the two jump targets are printable and outside the gadget
    (hbw : s₀.mem.get (Value.ofNat b) = Value.ofNat wb)
    (hbr : 33 ≤ wb ∧ wb ≤ 126)
    (hEw : s₀.mem.get (Value.ofNat E) = Value.ofNat wE)
    (hEr : 33 ≤ wE ∧ wE ≤ 126)
    (hEsep : ∀ i < L, E ≠ b + 1 + i)
    (hEsep' : E ≠ b + 1 + L) (hEb : E ≠ b)
    (hEd : ∀ j ≤ 2 * L + 1, E ≠ d₀ + j) :
    ∃ s', run? (2 * L + 2) s₀ = some s'
      ∧ s'.a = rowFold s₀.mem d₀ isC s₀.a L
      ∧ s'.c = Value.ofNat (E + 1)
      ∧ s'.d = Value.ofNat (d₀ + 2 * L + 2)
      ∧ (∀ i < L, s'.mem.get (Value.ofNat (b + 1 + i))
          = Value.ofNat (encrypt (encrypt (w i))))
      ∧ s'.mem.get (Value.ofNat (b + 1 + L))
          = s₀.mem.get (Value.ofNat (b + 1 + L))
      ∧ s'.input = s₀.input ∧ s'.output = s₀.output ∧ s'.outClosed = s₀.outClosed := by
  -- sweep one
  obtain ⟨s₁, hr1, hA1, hC1, hD1, _, _, hCs1, hfr1, hin1, hout1, hoc1, hrw1, hmw1⟩ :=
    row_run L isC w hc hd (by omega) hdec hprint
  -- the jump cell survived sweep one
  have hJ1 : s₁.mem.get (Value.ofNat (b + 1 + L)) = s₀.mem.get (Value.ofNat (b + 1 + L)) :=
    hfr1 _ (fun i hi => ofNat_ne (by omega)) (fun j hj => ofNat_ne (by omega))
  have hT01 : s₁.mem.get (Value.ofNat (d₀ + L)) = Value.ofNat b := by
    rw [hfr1 _ (fun i hi => ofNat_ne (by omega)) (fun j hj => ofNat_ne (by omega))]
    exact hT0
  have hb1 : s₁.mem.get (Value.ofNat b) = Value.ofNat wb := by
    rw [hfr1 _ (fun i hi => ofNat_ne (by omega)) (fun j hj => ofNat_ne (by omega))]
    exact hbw
  -- the first jump: back to b, landing on b+1
  have hstepJ1 := step1_jmp (s := s₁) (code := wb)
    (by rw [hC1, hJ1]; exact hJdec)
    (by rw [hD1, hT01, hb1]; exact printableCode?_ofNat hbr.1 hbr.2)
  rw [hD1, hT01] at hstepJ1
  set m₂ := s₁.mem.set (Value.ofNat b) (Value.ofNat (encrypt wb)) with hm₂
  set s₂ : State := { s₁ with mem := m₂, c := (Value.ofNat b).succ, d := (Value.ofNat (d₀ + L)).succ } with hs₂
  have hr2 : run? (L + 1) s₀ = some s₂ := by
    rw [run?_add L 1, hr1, Option.bind_some, run?_one]
    exact hstepJ1
  have hC2 : s₂.c = Value.ofNat (b + 1) := succ_ofNat b
  have hD2 : s₂.d = Value.ofNat (d₀ + L + 1) := succ_ofNat _
  -- sweep two: every row cell is now a no-op
  have hdecN : ∀ i < L, decode (s₂.mem.get (Value.ofNat (b + 1 + i)))
      (Value.ofNat (b + 1 + i)).modClass = .nop := by
    intro i hi
    show decode (m₂.get (Value.ofNat (b + 1 + i))) _ = _
    rw [hm₂, get_set_ne _ (ofNat_ne (by omega)), hCs1 i hi]
    exact hdec2 i hi
  have hprintN : ∀ i < L, printableCode? (s₂.mem.get (Value.ofNat (b + 1 + i)))
      = some (encrypt (w i)) := by
    intro i hi
    show printableCode? (m₂.get (Value.ofNat (b + 1 + i))) = _
    rw [hm₂, get_set_ne _ (ofNat_ne (by omega)), hCs1 i hi]
    obtain ⟨h1, h2⟩ := encrypt_range (hrange i hi).1 (hrange i hi).2
    exact printableCode?_ofNat h1 h2
  obtain ⟨s₃, hr3, hA3, hC3, hD3, _, _, hCs3, hfr3, hin3, hout3, hoc3, _, _⟩ :=
    row_run L (fun _ => false) (fun i => encrypt (w i)) hC2 hD2 (by omega)
      (by intro i hi; simpa using hdecN i hi) hprintN
  -- the jump cell survived sweep two
  have hJ3 : s₃.mem.get (Value.ofNat (b + 1 + L)) = s₀.mem.get (Value.ofNat (b + 1 + L)) := by
    rw [hfr3 _ (fun i hi => ofNat_ne (by omega)) (fun j hj => ofNat_ne (by omega))]
    show m₂.get (Value.ofNat (b + 1 + L)) = _
    rw [hm₂, get_set_ne _ (ofNat_ne (by omega))]
    exact hJ1
  have hT13 : s₃.mem.get (Value.ofNat (d₀ + 2 * L + 1)) = Value.ofNat E := by
    rw [hfr3 _ (fun i hi => ofNat_ne (by omega)) (fun j hj => ofNat_ne (by omega))]
    show m₂.get (Value.ofNat (d₀ + 2 * L + 1)) = _
    rw [hm₂, get_set_ne _ (ofNat_ne (by omega))]
    rw [hfr1 _ (fun i hi => ofNat_ne (by omega)) (fun j hj => ofNat_ne (by omega))]
    exact hT1
  have hE3 : s₃.mem.get (Value.ofNat E) = Value.ofNat wE := by
    rw [hfr3 _ (fun i hi => ofNat_ne (hEsep i hi))
      (fun j hj => ofNat_ne (by have := hEd (L + 1 + j) (by omega); omega))]
    show m₂.get (Value.ofNat E) = _
    rw [hm₂, get_set_ne _ (ofNat_ne (Ne.symm hEb))]
    rw [hfr1 _ (fun i hi => ofNat_ne (hEsep i hi))
      (fun j hj => ofNat_ne (by have := hEd j (by omega); omega))]
    exact hEw
  -- the second jump: out to E, landing on E+1
  have hstepJ2 := step1_jmp (s := s₃) (code := wE)
    (by rw [hC3, hJ3]; exact hJdec)
    (by rw [hD3, show d₀ + L + 1 + L = d₀ + 2 * L + 1 by omega, hT13, hE3]
        exact printableCode?_ofNat hEr.1 hEr.2)
  rw [hD3, show d₀ + L + 1 + L = d₀ + 2 * L + 1 by omega, hT13] at hstepJ2
  set s₄ : State := { s₃ with mem := s₃.mem.set (Value.ofNat E) (Value.ofNat (encrypt wE)), c := (Value.ofNat E).succ, d := (Value.ofNat (d₀ + 2 * L + 1)).succ } with hs₄
  refine ⟨s₄, ?_, ?_, succ_ofNat E, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 2 * L + 2 = (L + 1 + L) + 1 by omega, run?_add (L + 1 + L) 1,
      run?_add (L + 1) L, hr2, Option.bind_some, hr3, Option.bind_some, run?_one]
    exact hstepJ2
  · show s₃.a = _
    rw [hA3, rowFold_false, hA1]
  · show (Value.ofNat (d₀ + 2 * L + 1)).succ = _
    rw [succ_ofNat]
  · intro i hi
    show (s₃.mem.set (Value.ofNat E) (Value.ofNat (encrypt wE))).get
      (Value.ofNat (b + 1 + i)) = _
    rw [get_set_ne _ (ofNat_ne (hEsep i hi)), hCs3 i hi]
  · show (s₃.mem.set (Value.ofNat E) (Value.ofNat (encrypt wE))).get
      (Value.ofNat (b + 1 + L)) = _
    rw [get_set_ne _ (ofNat_ne hEsep'), hJ3]
  · exact hin3.trans hin1
  · exact hout3.trans hout1
  · exact hoc3.trans hoc1

/-! ## Emitting, and reading the answer back

The counter machine's `emit` appends one byte, and its `CState` records
only *how many*, because every byte a compiled program emits is the same.
That makes the output side of a completeness witness nearly free: the
gadget for `emit` sets the accumulator to a fixed printable natural and
executes one `<`, and the answer decoder is the byte count.

`42` is the byte chosen, which is `'*'`: a one-byte UTF-8 character, not
`...22` (which would close the stream) and not `...21` (a newline), so
`doOutput` takes its ordinary branch. -/

theorem doOutput_star {s : State} (ha : s.a = Value.ofNat 42)
    (hc : s.outClosed = false) :
    doOutput s = .ok { s with output := s.output ++ "*".toUTF8 } := by
  unfold doOutput
  rw [ha, hc]
  simp only [beq_iff_eq, Bool.false_eq_true, if_false]
  rw [if_neg (by decide : ¬ (Value.ofNat 42 = Value.eof)),
    if_neg (by decide : ¬ (Value.ofNat 42 = Value.eol)), toNat?_ofNat]
  rfl

/-- An output step at the `step1` level. -/
theorem step1_out {s : State} {code : Nat}
    (hdec : decode (s.mem.get s.c) s.c.modClass = .out)
    (ha : s.a = Value.ofNat 42) (hoc : s.outClosed = false)
    (hcode : printableCode? (s.mem.get s.c) = some code) :
    step1 s = some { s with output := s.output ++ "*".toUTF8,
                            mem := s.mem.set s.c (Value.ofNat (encrypt code)),
                            c := s.c.succ, d := s.d.succ } :=
  step1_eq hdec (by simp) (by simp) (doOutput_star ha hoc) hcode

/-- One `emit` adds exactly one byte. -/
theorem size_append_star (bs : ByteArray) : (bs ++ "*".toUTF8).size = bs.size + 1 := by
  simp [show "*".utf8ByteSize = 1 from rfl]

/-- **The answer decoder.** Every byte the compiled program emits is the
same, so the machine's answer is the number of bytes. -/
def decodeBytes (bs : ByteArray) : Option Nat := some bs.size

theorem decodeBytes_append_star (bs : ByteArray) :
    decodeBytes (bs ++ "*".toUTF8) = some (bs.size + 1) := by
  rw [decodeBytes, size_append_star]

/-- Emitting leaves the stream open, so emits compose. -/
theorem outClosed_of_step1_out {s : State} {code : Nat}
    (hdec : decode (s.mem.get s.c) s.c.modClass = .out)
    (ha : s.a = Value.ofNat 42) (hoc : s.outClosed = false)
    (hcode : printableCode? (s.mem.get s.c) = some code) :
    ∃ s', step1 s = some s' ∧ s'.outClosed = false
      ∧ s'.output.size = s.output.size + 1 ∧ s'.a = s.a := by
  refine ⟨_, step1_out hdec ha hoc hcode, hoc, ?_, rfl⟩
  exact size_append_star s.output

/-! ## The register encoding: blank, mark, flag

The counter machine's registers want three operations on a cell — set it,
clear it, and test it — and the encoding decides how many instructions each
costs. Taking **blank = `...000` and mark = `...111`** makes all three cost
exactly *one* crazy operation, which is the least the language allows,
since `p` is the only instruction that writes.

Reading the table by the accumulator trit:

| accumulator | on blank `0` | on mark `1` | effect |
|---|---|---|---|
| `...000` | `1` | — | **set**: blank becomes mark |
| `...111` | — | `0` | **clear**: mark becomes blank |
| `...222` | `0` | `2` | **test**: blank gives `...000`, mark gives `...222` |

The third row is the one that matters. `p` leaves its result in the
accumulator *and* in the cell, so testing a register cell against `...222`
puts exactly the flag `branch_arith` wants into the accumulator: `Value.zero`
for blank, `Value.eof` for mark. The zero test therefore costs one
instruction and needs no broadcasting, which the crazy operation could not
do anyway, being tritwise. That is the argument for a unary representation,
made by the table rather than by taste.

The cost is that the test is destructive: a mark reads as `...222` and has
to be restored, which `crz_restore_mark` does with one more operation
against the same constant. Blanks survive the round trip untouched. -/

/-- Blank: the cell of a register that holds nothing. -/
abbrev blank : Value := uniform .t0

/-- Mark: one unit of a unary register. -/
abbrev mark : Value := uniform .t1

theorem blank_eq_zero : blank = Value.zero := rfl

theorem flagMark_eq_eof : uniform .t2 = Value.eof := rfl

/-- **Set**: one crazy operation against `...000` turns a blank into a
mark. -/
theorem crz_set_mark : Value.crz blank blank = mark := by decide

/-- **Clear**: one crazy operation against `...111` turns a mark into a
blank. -/
theorem crz_clear_mark : Value.crz mark mark = blank := by decide

/-- **Test, blank**: against `...222` a blank reads as `Value.zero`, the
flag `branch_arith` takes for its first target. -/
theorem crz_test_blank : Value.crz Value.eof blank = Value.zero := by decide

/-- **Test, mark**: against `...222` a mark reads as `Value.eof`, the flag
for the second target. -/
theorem crz_test_mark : Value.crz Value.eof mark = Value.eof := by decide

/-- The test is destructive on a mark, which now reads `...222`; one more
operation against the same constant puts it back. A blank is unchanged by
both, so the pair is a non-destructive test whichever the cell held. -/
theorem crz_restore_mark : Value.crz Value.eof Value.eof = mark := by decide

theorem crz_restore_blank : Value.crz Value.eof Value.zero = blank := by decide

/-- **The register cell round trip.** Testing a cell against `...222` and
then restoring it leaves the cell exactly as it was, and the intermediate
accumulator is the branch flag: `Value.zero` for a blank, `Value.eof` for a
mark. This is the zero test the compiled `loop` will use. -/
theorem register_test_roundtrip {v : Value} (h : v = blank ∨ v = mark) :
    Value.crz Value.eof (Value.crz Value.eof v) = v
    ∧ (Value.crz Value.eof v = Value.zero ↔ v = blank)
    ∧ (Value.crz Value.eof v = Value.eof ↔ v = mark) := by
  rcases h with h | h <;> subst h
  · exact ⟨by decide, by decide, by decide⟩
  · exact ⟨by decide, by decide, by decide⟩

/-! ## Chains: working cells joined by stable jumps

`row_run` lays a gadget out as one contiguous row, which forces padding
into the gaps between working cells, and padding is awkward: a re-enterable
`crazy` must sit at residue 82 or 86 modulo 94, while the cells in between
fall wherever they fall, including the sixteen residues at which no
two-cycle word is harmless in both phases.

Interleaving removes the problem. Put a `jmp` immediately after each
working cell and let it carry control to the next one. A `jmp` never
encrypts itself, so it is stable for the whole run and **the control path
is identical on every pass**, while the working cells alternate between
their instruction and a no-op. The cells jumped over are never executed, so
they need no words at all; only the landing cell is encrypted, and
encryption keeps a printable word printable.

`d` advances two per link, so each link owns two data cells at a known
stride: the operand the `crazy` reads at `D`, and the address the `jmp`
reads at `D + 1`. Both are placed statically. `chain_link` is one link and
`chain_run` is `n` of them. -/

/-- One link: a working `crazy` cell, then a stable `jmp` to the next link.
Two steps. -/
theorem chain_link {s : State} {a D t : Nat} {wc wt : Nat}
    (hc : s.c = Value.ofNat a) (hd : s.d = Value.ofNat D)
    (hdecC : decode (s.mem.get (Value.ofNat a)) (Value.ofNat a).modClass = .crazy)
    (hprC : printableCode? (s.mem.get (Value.ofNat a)) = some wc)
    (hdecJ : decode (s.mem.get (Value.ofNat (a + 1))) (Value.ofNat (a + 1)).modClass = .jmp)
    (hDne : D ≠ a) (hDne'' : D ≠ a + 1) (hD1a : D + 1 ≠ a)
    (htgt : s.mem.get (Value.ofNat (D + 1)) = Value.ofNat t)
    (hprT : printableCode? (s.mem.get (Value.ofNat t)) = some wt)
    (htne : t ≠ a) (htne' : t ≠ D) (htne'' : t ≠ a + 1) :
    ∃ s', run? 2 s = some s'
      ∧ s'.a = Value.crz s.a (s.mem.get (Value.ofNat D))
      ∧ s'.c = Value.ofNat (t + 1)
      ∧ s'.d = Value.ofNat (D + 2)
      ∧ s'.mem.get (Value.ofNat D) = Value.crz s.a (s.mem.get (Value.ofNat D))
      ∧ s'.mem.get (Value.ofNat a) = Value.ofNat (encrypt wc)
      ∧ s'.mem.get (Value.ofNat (a + 1)) = s.mem.get (Value.ofNat (a + 1))
      ∧ (∀ x : Nat, x ≠ D → x ≠ a → x ≠ t →
          s'.mem.get (Value.ofNat x) = s.mem.get (Value.ofNat x))
      ∧ s'.input = s.input ∧ s'.output = s.output ∧ s'.outClosed = s.outClosed := by
  -- step one: the crazy cell
  have hstep1 := step1_crazy (s := s) (code := wc)
    (by rw [hc]; exact hdecC) (by rw [hc, hd]; exact ofNat_ne hDne)
    (by rw [hc]; exact hprC)
  rw [hc, hd] at hstep1
  set v := Value.crz s.a (s.mem.get (Value.ofNat D)) with hv
  set m₁ := (s.mem.set (Value.ofNat D) v).set (Value.ofNat a) (Value.ofNat (encrypt wc)) with hm₁
  set s₁ : State := { s with a := v, mem := m₁, c := (Value.ofNat a).succ, d := (Value.ofNat D).succ } with hs₁
  -- step two: the stable jump
  have hc₁ : s₁.c = Value.ofNat (a + 1) := succ_ofNat a
  have hd₁ : s₁.d = Value.ofNat (D + 1) := succ_ofNat D
  have hJ₁ : m₁.get (Value.ofNat (a + 1)) = s.mem.get (Value.ofNat (a + 1)) := by
    rw [hm₁, get_set_ne _ (ofNat_ne (by omega : a ≠ a + 1)),
      get_set_ne _ (ofNat_ne hDne'')]
  have htgt₁ : m₁.get (Value.ofNat (D + 1)) = Value.ofNat t := by
    rw [hm₁, get_set_ne _ (ofNat_ne (Ne.symm hD1a)),
      get_set_ne _ (ofNat_ne (by omega : D ≠ D + 1))]
    exact htgt
  have hT₁ : m₁.get (Value.ofNat t) = s.mem.get (Value.ofNat t) := by
    rw [hm₁, get_set_ne _ (ofNat_ne (Ne.symm htne)),
      get_set_ne _ (ofNat_ne (Ne.symm htne'))]
  have hdecJ₁ : decode (s₁.mem.get s₁.c) s₁.c.modClass = Instr.jmp := by
    rw [hc₁]
    show decode (m₁.get (Value.ofNat (a + 1))) _ = _
    rw [hJ₁]
    exact hdecJ
  have hprT₁ : printableCode? (s₁.mem.get (s₁.mem.get s₁.d)) = some wt := by
    rw [hd₁]
    show printableCode? (m₁.get (m₁.get (Value.ofNat (D + 1)))) = _
    rw [htgt₁, hT₁]
    exact hprT
  have hstep2 := step1_jmp (s := s₁) (code := wt) hdecJ₁ hprT₁
  rw [hd₁] at hstep2
  show ∃ s', run? 2 s = some s' ∧ _
  rw [show (2 : Nat) = 1 + 1 from rfl]
  refine ⟨{ s₁ with mem := m₁.set (Value.ofNat t) (Value.ofNat (encrypt wt)), c := (Value.ofNat t).succ, d := (Value.ofNat (D + 1)).succ }, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · rw [run?_add 1 1, run?_one, hstep1, Option.bind_some, run?_one]
    show step1 s₁ = _
    rw [hstep2, htgt₁]
  · show (Value.ofNat t).succ = _
    rw [succ_ofNat]
  · show (Value.ofNat (D + 1)).succ = _
    rw [succ_ofNat]
  · show (m₁.set (Value.ofNat t) (Value.ofNat (encrypt wt))).get (Value.ofNat D) = _
    rw [get_set_ne _ (ofNat_ne htne'), hm₁,
      get_set_ne _ (ofNat_ne (Ne.symm hDne)), get_set_self]
  · show (m₁.set (Value.ofNat t) (Value.ofNat (encrypt wt))).get (Value.ofNat a) = _
    rw [get_set_ne _ (ofNat_ne htne), hm₁, get_set_self]
  · show (m₁.set (Value.ofNat t) (Value.ofNat (encrypt wt))).get (Value.ofNat (a + 1)) = _
    rw [get_set_ne _ (ofNat_ne htne''), hJ₁]
  · intro x hxD hxa hxt
    show (m₁.set (Value.ofNat t) (Value.ofNat (encrypt wt))).get (Value.ofNat x) = _
    rw [get_set_ne _ (ofNat_ne (Ne.symm hxt)), hm₁,
      get_set_ne _ (ofNat_ne (Ne.symm hxa)), get_set_ne _ (ofNat_ne (Ne.symm hxD))]

/-! ## Running a chain

A chain of links laid out at **stride 94**. That stride is forced and
convenient: a re-enterable `crazy` must sit at residue 82 or 86 modulo 94,
so putting the links 94 apart lands every one of them on the same residue,
and one word serves for every `crazy` cell and one for every `jmp`.

Link `i` occupies `A + 94i` (the `crazy`) and `A + 94i + 1` (the `jmp`),
and its jump lands on `A + 94i + 93` so that control resumes at
`A + 94(i+1)`, the next link. The 92 cells in between are never executed.
Data sits after the code: operand `i` at `D + 2i`, jump target `i` at
`D + 2i + 1`. -/

/-- The fold a chain computes: the crazy operation over the operand cells,
which sit at stride two because `d` advances two per link. -/
def chainFold (m : Memory) (D : Nat) (a : Value) : Nat → Value
  | 0 => a
  | j + 1 => Value.crz (chainFold m D a j) (m.get (Value.ofNat (D + 2 * j)))

/-- **A chain of `n` links runs in `2n` steps.** The accumulator folds the
operands, each operand cell keeps its intermediate, each `crazy` cell is
encrypted once, and **every `jmp` cell comes back unchanged**, which is
what lets the chain be entered again. -/
theorem chain_run (n : Nat) {s : State} {A D : Nat} (wc wt : Nat → Nat)
    (hc : s.c = Value.ofNat A) (hd : s.d = Value.ofNat D)
    (hsep : A + 94 * n + 94 ≤ D)
    (hdecC : ∀ i < n, decode (s.mem.get (Value.ofNat (A + 94 * i)))
      (Value.ofNat (A + 94 * i)).modClass = .crazy)
    (hprC : ∀ i < n, printableCode? (s.mem.get (Value.ofNat (A + 94 * i))) = some (wc i))
    (hdecJ : ∀ i < n, decode (s.mem.get (Value.ofNat (A + 94 * i + 1)))
      (Value.ofNat (A + 94 * i + 1)).modClass = .jmp)
    (htgt : ∀ i < n, s.mem.get (Value.ofNat (D + 2 * i + 1))
      = Value.ofNat (A + 94 * i + 93))
    (hprT : ∀ i < n, printableCode? (s.mem.get (Value.ofNat (A + 94 * i + 93)))
      = some (wt i)) :
    ∃ s', run? (2 * n) s = some s'
      ∧ s'.a = chainFold s.mem D s.a n
      ∧ s'.c = Value.ofNat (A + 94 * n)
      ∧ s'.d = Value.ofNat (D + 2 * n)
      ∧ (∀ i < n, s'.mem.get (Value.ofNat (D + 2 * i)) = chainFold s.mem D s.a (i + 1))
      ∧ (∀ i < n, s'.mem.get (Value.ofNat (A + 94 * i)) = Value.ofNat (encrypt (wc i)))
      ∧ (∀ x : Nat, (∀ i < n, x ≠ A + 94 * i) → (∀ i < n, x ≠ D + 2 * i) →
          (∀ i < n, x ≠ A + 94 * i + 93) →
          s'.mem.get (Value.ofNat x) = s.mem.get (Value.ofNat x))
      ∧ s'.input = s.input ∧ s'.output = s.output ∧ s'.outClosed = s.outClosed := by
  induction n with
  | zero =>
    exact ⟨s, rfl, rfl, by simpa using hc, by simpa using hd,
      fun i hi => absurd hi (by omega), fun i hi => absurd hi (by omega),
      fun _ _ _ _ => rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨sn, hrun, hAcc, hC, hD, hOps, hCs, hframe, hin, hout, hoc⟩ :=
      ih (by omega) (fun i hi => hdecC i (by omega)) (fun i hi => hprC i (by omega))
        (fun i hi => hdecJ i (by omega))
        (fun i hi => htgt i (by omega)) (fun i hi => hprT i (by omega))
    -- link n's cells are all untouched by the first n links
    have hu : ∀ x : Nat, (∀ i < n, x ≠ A + 94 * i) → (∀ i < n, x ≠ D + 2 * i) →
        (∀ i < n, x ≠ A + 94 * i + 93) →
        sn.mem.get (Value.ofNat x) = s.mem.get (Value.ofNat x) := hframe
    have hC0 : sn.mem.get (Value.ofNat (A + 94 * n)) = s.mem.get (Value.ofNat (A + 94 * n)) :=
      hu _ (fun i hi => by omega) (fun i hi => by omega) (fun i hi => by omega)
    have hJ0 : sn.mem.get (Value.ofNat (A + 94 * n + 1))
        = s.mem.get (Value.ofNat (A + 94 * n + 1)) :=
      hu _ (fun i hi => by omega) (fun i hi => by omega) (fun i hi => by omega)
    have hT0 : sn.mem.get (Value.ofNat (D + 2 * n + 1))
        = s.mem.get (Value.ofNat (D + 2 * n + 1)) :=
      hu _ (fun i hi => by omega) (fun i hi => by omega) (fun i hi => by omega)
    have hTC : sn.mem.get (Value.ofNat (A + 94 * n + 93))
        = s.mem.get (Value.ofNat (A + 94 * n + 93)) :=
      hu _ (fun i hi => by omega) (fun i hi => by omega) (fun i hi => by omega)
    obtain ⟨s', hr', hacc', hc', hd', hop', hcr', hjm', hfr', hi', ho', hoc'⟩ :=
      chain_link (s := sn) (a := A + 94 * n) (D := D + 2 * n)
        (t := A + 94 * n + 93) (wc := wc n) (wt := wt n)
        hC hD (by rw [hC0]; exact hdecC n (by omega))
        (by rw [hC0]; exact hprC n (by omega))
        (by rw [hJ0]; exact hdecJ n (by omega))
        (by omega) (by omega) (by omega)
        (by rw [hT0]; exact htgt n (by omega))
        (by rw [hTC]; exact hprT n (by omega))
        (by omega) (by omega) (by omega)
    have hfold : Value.crz sn.a (sn.mem.get (Value.ofNat (D + 2 * n)))
        = chainFold s.mem D s.a (n + 1) := by
      rw [hAcc, hu (D + 2 * n) (fun i hi => by omega) (fun i hi => by omega)
        (fun i hi => by omega)]
      rfl
    refine ⟨s', ?_, ?_, ?_, ?_, ?_, ?_, ?_, hi'.trans hin, ho'.trans hout,
      hoc'.trans hoc⟩
    · rw [show 2 * (n + 1) = 2 * n + 2 by omega, run?_add (2 * n) 2, hrun,
        Option.bind_some]
      exact hr'
    · rw [hacc']; exact hfold
    · rw [hc', show A + 94 * n + 93 + 1 = A + 94 * (n + 1) by omega]
    · rw [hd', show D + 2 * n + 2 = D + 2 * (n + 1) by omega]
    · intro i hi
      by_cases hin' : i = n
      · subst hin'; rw [hop']; exact hfold
      · rw [hfr' _ (by omega) (by omega) (by omega)]
        exact hOps i (by omega)
    · intro i hi
      by_cases hin' : i = n
      · subst hin'; exact hcr'
      · rw [hfr' _ (by omega) (by omega) (by omega)]
        exact hCs i (by omega)
    · intro x hx1 hx2 hx3
      rw [hfr' _ (hx2 n (by omega)) (hx1 n (by omega)) (hx3 n (by omega))]
      exact hu x (fun i hi => hx1 i (by omega)) (fun i hi => hx2 i (by omega))
        (fun i hi => hx3 i (by omega))

/-! ## Entering a chain

A chain expects `c` at `A` and `d` at `D`, and a gadget has to arrange
that. `movd` is the only instruction that moves `d`, and a re-enterable one
must sit at residue 60 or 64 modulo 94, while a chain starts at residue 82,
so the two cannot be adjacent. One stable `jmp` bridges them, and the
prologue is two instructions:

* `movd` at `M` reads the pointer cell under `d` and re-aims `d`;
* `jmp` at `M + 1` reads its target and drops control at `A`.

Laid out: the pointer cell holds `D - 2`, the cell at `D - 1` holds
`A - 1`, and afterwards `c = A` and `d = D`, exactly what `chain_run`
wants. The `movd` cell is encrypted, the `jmp` is not. -/

theorem enter_chain {s : State} {M P Q A : Nat} {wm wt : Nat}
    (hc : s.c = Value.ofNat M) (hd : s.d = Value.ofNat P)
    (hdecM : decode (s.mem.get (Value.ofNat M)) (Value.ofNat M).modClass = .movd)
    (hprM : printableCode? (s.mem.get (Value.ofNat M)) = some wm)
    (hptr : s.mem.get (Value.ofNat P) = Value.ofNat Q)
    (hdecJ : decode (s.mem.get (Value.ofNat (M + 1))) (Value.ofNat (M + 1)).modClass = .jmp)
    (htgt : s.mem.get (Value.ofNat (Q + 1)) = Value.ofNat (A - 1))
    (hA : 1 ≤ A)
    (hprT : printableCode? (s.mem.get (Value.ofNat (A - 1))) = some wt)
    (hMne : A - 1 ≠ M) (hQM : Q + 1 ≠ M) :
    ∃ s', run? 2 s = some s'
      ∧ s'.a = s.a
      ∧ s'.c = Value.ofNat A
      ∧ s'.d = Value.ofNat (Q + 2)
      ∧ s'.mem.get (Value.ofNat M) = Value.ofNat (encrypt wm)
      ∧ s'.mem.get (Value.ofNat (A - 1)) = Value.ofNat (encrypt wt)
      ∧ (∀ x : Nat, x ≠ M → x ≠ A - 1 →
          s'.mem.get (Value.ofNat x) = s.mem.get (Value.ofNat x))
      ∧ s'.input = s.input ∧ s'.output = s.output ∧ s'.outClosed = s.outClosed := by
  -- step one: movd
  have hstepM := step1_movd (s := s) (code := wm)
    (by rw [hc]; exact hdecM) (by rw [hc]; exact hprM)
  rw [hc, hd, hptr] at hstepM
  set m₁ := s.mem.set (Value.ofNat M) (Value.ofNat (encrypt wm)) with hm₁
  set s₁ : State := { s with mem := m₁, c := (Value.ofNat M).succ, d := (Value.ofNat Q).succ, maxWidth := if (Value.ofNat Q).width > s.maxWidth then (Value.ofNat Q).width else s.maxWidth, rotWidth := if (Value.ofNat Q).width > s.maxWidth then growRotWidth s.rotWidth (Value.ofNat Q).width else s.rotWidth } with hs₁
  have hc₁ : s₁.c = Value.ofNat (M + 1) := succ_ofNat M
  have hd₁ : s₁.d = Value.ofNat (Q + 1) := succ_ofNat Q
  have hJ₁ : m₁.get (Value.ofNat (M + 1)) = s.mem.get (Value.ofNat (M + 1)) := by
    rw [hm₁, get_set_ne _ (ofNat_ne (by omega : M ≠ M + 1))]
  have hT₁ : m₁.get (Value.ofNat (Q + 1)) = Value.ofNat (A - 1) := by
    rw [hm₁, get_set_ne _ (ofNat_ne (Ne.symm hQM))]
    exact htgt
  have hA₁ : m₁.get (Value.ofNat (A - 1)) = s.mem.get (Value.ofNat (A - 1)) := by
    rw [hm₁, get_set_ne _ (ofNat_ne (fun h => hMne h.symm))]
  have hdecJ₁ : decode (s₁.mem.get s₁.c) s₁.c.modClass = Instr.jmp := by
    rw [hc₁]; show decode (m₁.get (Value.ofNat (M + 1))) _ = _; rw [hJ₁]; exact hdecJ
  have hprT₁ : printableCode? (s₁.mem.get (s₁.mem.get s₁.d)) = some wt := by
    rw [hd₁]
    show printableCode? (m₁.get (m₁.get (Value.ofNat (Q + 1)))) = _
    rw [hT₁, hA₁]; exact hprT
  have hstepJ := step1_jmp (s := s₁) (code := wt) hdecJ₁ hprT₁
  rw [hd₁, hT₁] at hstepJ
  show ∃ s', run? 2 s = some s' ∧ _
  rw [show (2 : Nat) = 1 + 1 from rfl]
  refine ⟨{ s₁ with mem := m₁.set (Value.ofNat (A - 1)) (Value.ofNat (encrypt wt)), c := (Value.ofNat (A - 1)).succ, d := (Value.ofNat (Q + 1)).succ }, ?_, rfl, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · rw [run?_add 1 1, run?_one, hstepM, Option.bind_some, run?_one]
    exact hstepJ
  · show (Value.ofNat (A - 1)).succ = _
    rw [succ_ofNat, show A - 1 + 1 = A by omega]
  · show (Value.ofNat (Q + 1)).succ = _
    rw [succ_ofNat]
  · show (m₁.set (Value.ofNat (A - 1)) (Value.ofNat (encrypt wt))).get (Value.ofNat M) = _
    rw [get_set_ne _ (ofNat_ne hMne), hm₁, get_set_self]
  · show (m₁.set (Value.ofNat (A - 1)) (Value.ofNat (encrypt wt))).get
      (Value.ofNat (A - 1)) = _
    rw [get_set_self]
  · intro x hxM hxA
    show (m₁.set (Value.ofNat (A - 1)) (Value.ofNat (encrypt wt))).get (Value.ofNat x) = _
    rw [get_set_ne _ (ofNat_ne (Ne.symm hxA)), hm₁, get_set_ne _ (ofNat_ne (Ne.symm hxM))]

/-! ## A whole gadget

`enter_chain` followed by `chain_run`: `2 + 2n` steps that position `d`,
fold `n` operands into the accumulator, and leave every `jmp` cell standing.
This is the unit a compiled counter-machine command is built from. -/

theorem chainFold_congr {m m' : Memory} {D : Nat} {a : Value} : ∀ n : Nat,
    (∀ i < n, m.get (Value.ofNat (D + 2 * i)) = m'.get (Value.ofNat (D + 2 * i))) →
    chainFold m D a n = chainFold m' D a n
  | 0, _ => rfl
  | n + 1, h => by
    show Value.crz (chainFold m D a n) (m.get (Value.ofNat (D + 2 * n)))
      = Value.crz (chainFold m' D a n) (m'.get (Value.ofNat (D + 2 * n)))
    rw [chainFold_congr n (fun i hi => h i (by omega)), h n (by omega)]

/-- **A gadget runs.** The prologue re-aims `d`, the chain folds `n`
operands into the accumulator, and the result is left both in the
accumulator and in the last operand cell. -/
theorem gadget_run (n : Nat) {s : State} {M P Q A : Nat} {wm wt₀ : Nat}
    (wc wt : Nat → Nat)
    (hc : s.c = Value.ofNat M) (hd : s.d = Value.ofNat P)
    -- prologue
    (hdecM : decode (s.mem.get (Value.ofNat M)) (Value.ofNat M).modClass = .movd)
    (hprM : printableCode? (s.mem.get (Value.ofNat M)) = some wm)
    (hptr : s.mem.get (Value.ofNat P) = Value.ofNat Q)
    (hdecJ₀ : decode (s.mem.get (Value.ofNat (M + 1))) (Value.ofNat (M + 1)).modClass = .jmp)
    (htgt₀ : s.mem.get (Value.ofNat (Q + 1)) = Value.ofNat (A - 1))
    (hA : 1 ≤ A)
    (hprT₀ : printableCode? (s.mem.get (Value.ofNat (A - 1))) = some wt₀)
    (hMne : A - 1 ≠ M) (hQM : Q + 1 ≠ M)
    -- the chain, stated on the initial memory
    (hsep : A + 94 * n + 94 ≤ Q + 2)
    (hdecC : ∀ i < n, decode (s.mem.get (Value.ofNat (A + 94 * i)))
      (Value.ofNat (A + 94 * i)).modClass = .crazy)
    (hprC : ∀ i < n, printableCode? (s.mem.get (Value.ofNat (A + 94 * i))) = some (wc i))
    (hdecJ : ∀ i < n, decode (s.mem.get (Value.ofNat (A + 94 * i + 1)))
      (Value.ofNat (A + 94 * i + 1)).modClass = .jmp)
    (htgt : ∀ i < n, s.mem.get (Value.ofNat (Q + 2 + 2 * i + 1))
      = Value.ofNat (A + 94 * i + 93))
    (hprT : ∀ i < n, printableCode? (s.mem.get (Value.ofNat (A + 94 * i + 93)))
      = some (wt i))
    -- the gadget's cells avoid the two the prologue writes
    (hMsep : ∀ i < n, M ≠ A + 94 * i ∧ M ≠ A + 94 * i + 1 ∧ M ≠ A + 94 * i + 93
      ∧ M ≠ Q + 2 + 2 * i ∧ M ≠ Q + 2 + 2 * i + 1)
    (hAsep : ∀ i < n, A - 1 ≠ A + 94 * i ∧ A - 1 ≠ A + 94 * i + 1
      ∧ A - 1 ≠ A + 94 * i + 93 ∧ A - 1 ≠ Q + 2 + 2 * i
      ∧ A - 1 ≠ Q + 2 + 2 * i + 1) :
    ∃ s', run? (2 + 2 * n) s = some s'
      ∧ s'.a = chainFold s.mem (Q + 2) s.a n
      ∧ s'.c = Value.ofNat (A + 94 * n)
      ∧ s'.d = Value.ofNat (Q + 2 + 2 * n)
      ∧ (∀ i < n, s'.mem.get (Value.ofNat (Q + 2 + 2 * i))
          = chainFold s.mem (Q + 2) s.a (i + 1))
      ∧ s'.input = s.input ∧ s'.output = s.output ∧ s'.outClosed = s.outClosed := by
  obtain ⟨s₁, hr1, ha1, hc1, hd1, _, _, hfr1, hi1, ho1, hoc1⟩ :=
    enter_chain hc hd hdecM hprM hptr hdecJ₀ htgt₀ hA hprT₀ hMne hQM
  -- transfer the chain's hypotheses across the prologue's frame
  have hC : ∀ i < n, s₁.mem.get (Value.ofNat (A + 94 * i))
      = s.mem.get (Value.ofNat (A + 94 * i)) :=
    fun i hi => hfr1 _ (fun h => (hMsep i hi).1 h.symm) (fun h => (hAsep i hi).1 h.symm)
  have hJ : ∀ i < n, s₁.mem.get (Value.ofNat (A + 94 * i + 1))
      = s.mem.get (Value.ofNat (A + 94 * i + 1)) :=
    fun i hi => hfr1 _ (fun h => (hMsep i hi).2.1 h.symm)
      (fun h => (hAsep i hi).2.1 h.symm)
  have hT : ∀ i < n, s₁.mem.get (Value.ofNat (A + 94 * i + 93))
      = s.mem.get (Value.ofNat (A + 94 * i + 93)) :=
    fun i hi => hfr1 _ (fun h => (hMsep i hi).2.2.1 h.symm)
      (fun h => (hAsep i hi).2.2.1 h.symm)
  have hOp : ∀ i < n, s₁.mem.get (Value.ofNat (Q + 2 + 2 * i))
      = s.mem.get (Value.ofNat (Q + 2 + 2 * i)) :=
    fun i hi => hfr1 _ (fun h => (hMsep i hi).2.2.2.1 h.symm)
      (fun h => (hAsep i hi).2.2.2.1 h.symm)
  have hTg : ∀ i < n, s₁.mem.get (Value.ofNat (Q + 2 + 2 * i + 1))
      = s.mem.get (Value.ofNat (Q + 2 + 2 * i + 1)) :=
    fun i hi => hfr1 _ (fun h => (hMsep i hi).2.2.2.2 h.symm)
      (fun h => (hAsep i hi).2.2.2.2 h.symm)
  obtain ⟨s₂, hr2, ha2, hc2, hd2, hop2, _, _, hi2, ho2, hoc2⟩ :=
    chain_run n wc wt hc1 hd1 hsep
      (fun i hi => by rw [hC i hi]; exact hdecC i hi)
      (fun i hi => by rw [hC i hi]; exact hprC i hi)
      (fun i hi => by rw [hJ i hi]; exact hdecJ i hi)
      (fun i hi => by rw [hTg i hi]; exact htgt i hi)
      (fun i hi => by rw [hT i hi]; exact hprT i hi)
  have hfold : chainFold s₁.mem (Q + 2) s₁.a n = chainFold s.mem (Q + 2) s.a n := by
    rw [ha1]
    exact chainFold_congr n (fun i hi => hOp i hi)
  have hfold' : ∀ k ≤ n, chainFold s₁.mem (Q + 2) s₁.a k = chainFold s.mem (Q + 2) s.a k := by
    intro k hk
    rw [ha1]
    exact chainFold_congr k (fun i hi => hOp i (by omega))
  refine ⟨s₂, ?_, ?_, hc2, hd2, ?_, hi2.trans hi1, ho2.trans ho1, hoc2.trans hoc1⟩
  · rw [run?_add 2 (2 * n), hr1, Option.bind_some]
    exact hr2
  · rw [ha2]; exact hfold
  · intro i hi
    rw [hop2 i hi]
    exact hfold' (i + 1) (by omega)

/-! ## A better register encoding: the non-destructive test

The encoding above (blank `...000`, mark `...111`) makes set, clear and
test one operation each, but the test is *destructive*: a mark reads back
as `...222` and needs a second operation to restore. Since the test is the
loop condition, and so runs on every iteration of every compiled loop, it
is worth asking whether an encoding avoids that. One does.

Take **blank = `...000` and mark = `...222`**. Then the accumulator
`...111` satisfies `crz ...111 b = b` for both, so testing leaves the cell
**exactly as it was**, and the value it leaves in the accumulator is the
cell's own content: `Value.zero` for blank, `Value.eof` for mark. Those are
precisely the two flags `branch_arith` consumes. The test is therefore one
operation, non-destructive, and produces the branch flag with no conversion
at all.

The accumulator `...111` is itself loaded self-restoringly: from a blank
accumulator, one operation against a cell holding `...111` leaves the
accumulator at `...111` and the cell at `...111`. So the whole test is two
links of a chain, both of which restore every cell they touch.

The price is on `set`: no single operation takes `...000` to `...222`, so
setting a mark costs two visits to the cell, hence two gadgets. Clearing is
one (`crz ...222 ...222 = ...111`, then one more to reach `...000`). Paying
on `set` and `dec` to make the loop condition free is the right trade,
because the condition runs once per iteration and the others once per
command. -/

/-- Blank, in the encoding the compiler uses. -/
abbrev cellBlank : Value := Value.zero

/-- Mark, in the encoding the compiler uses. -/
abbrev cellMark : Value := Value.eof

/-- The accumulator that tests a register cell. -/
abbrev testAcc : Value := uniform .t1

/-- **The test is non-destructive on a blank**, and hands back the flag
`Value.zero`. -/
theorem crz_probe_blank : Value.crz testAcc cellBlank = cellBlank := by decide

/-- **The test is non-destructive on a mark**, and hands back the flag
`Value.eof`. -/
theorem crz_probe_mark : Value.crz testAcc cellMark = cellMark := by decide

/-- Loading the test accumulator is itself self-restoring: from a blank
accumulator, one operation against a cell holding `...111` leaves both at
`...111`. -/
theorem crz_load_testAcc : Value.crz cellBlank testAcc = testAcc := by decide

/-- **The register probe.** Two links: load the test accumulator, then read
the cell. Every cell involved comes back unchanged, and the accumulator is
left holding exactly the branch flag for the cell's contents. -/
theorem register_probe {v : Value} (h : v = cellBlank ∨ v = cellMark) :
    Value.crz (Value.crz cellBlank testAcc) v = v
    ∧ (v = cellBlank → Value.crz (Value.crz cellBlank testAcc) v = Value.zero)
    ∧ (v = cellMark → Value.crz (Value.crz cellBlank testAcc) v = Value.eof) := by
  rw [crz_load_testAcc]
  rcases h with h | h <;> subst h
  · exact ⟨crz_probe_blank, fun _ => crz_probe_blank, fun h => absurd h (by decide)⟩
  · exact ⟨crz_probe_mark, fun h => absurd h (by decide), fun _ => crz_probe_mark⟩

/-- The probe feeds `branch_arith` with no conversion: the flag it produces
is already one of the two values the branch pipeline reads. -/
theorem probe_feeds_branch (t₀ t₁ : Value) (h₀ : t₀.Normalized) (h₁ : t₁.Normalized)
    (a : Value) {v : Value} (h : v = cellBlank ∨ v = cellMark) :
    branchChain t₀ t₁ a (Value.crz (Value.crz cellBlank testAcc) v)
      = if v = cellBlank then t₀ else t₁ := by
  obtain ⟨hfix, hb, hm⟩ := register_probe h
  rcases h with h | h <;> subst h
  · rw [if_pos rfl, hb rfl]
    exact (branch_arith t₀ t₁ h₀ h₁ a).1
  · rw [if_neg (by decide), hm rfl]
    exact (branch_arith t₀ t₁ h₀ h₁ a).2

/-! ## The accumulator ladder, and writing a register

Every crazy operation writes its result back over its operand, so a
compiler that keeps constants in memory must ask which constants survive
being used. Three do, and they are exactly the three values the register
encoding already needs.

Write `one` for `...111`. Then

* `crz blank one = one` — a cell holding `one` takes the accumulator from
  `blank` to `one` and is left holding `one`;
* `crz one eof = eof` — a cell holding `eof` takes it from `one` to `eof`
  and is left holding `eof`;
* `crz eof blank = blank` — a cell holding `blank` takes it from `eof` back
  to `blank` and is left holding `blank`.

So the accumulator climbs a **three-cycle** `blank → one → eof → blank`,
one operation per rung, and **no rung consumes its constant**. That is the
same three-cycle as `tau` in the copy algebra, which is not a coincidence:
both are the diagonal of Olmstead's table read as a permutation.

Writing a register cell then falls out, symmetrically through `one`:

* **set** (`blank ↦ mark`): with the accumulator at `blank`, one operation
  takes the cell to `one`; with the accumulator at `eof`, a second takes it
  to `mark`.
* **clear** (`mark ↦ blank`): with the accumulator at `eof`, one operation
  takes the cell to `one`; with the accumulator at `one`, a second takes it
  to `blank`.

Both need two visits because no single operation crosses between `...000`
and `...222` — the column of the table joining them is missing, which is
the same gap that made `crz_two_steps` need two operations. -/

/-- The middle value of the ladder. -/
abbrev cellOne : Value := uniform .t1

theorem ladder_blank_to_one : Value.crz cellBlank cellOne = cellOne := by decide

theorem ladder_one_to_eof : Value.crz cellOne cellMark = cellMark := by decide

theorem ladder_eof_to_blank : Value.crz cellMark cellBlank = cellBlank := by decide

/-- **The ladder is a three-cycle.** Three operations against the three
constants return the accumulator to where it began, and every constant cell
is left exactly as it was. -/
theorem ladder_cycle :
    Value.crz (Value.crz (Value.crz cellBlank cellOne) cellMark) cellBlank = cellBlank := by
  rw [ladder_blank_to_one, ladder_one_to_eof, ladder_eof_to_blank]

/-! ### Writing -/

theorem set_step₁ : Value.crz cellBlank cellBlank = cellOne := by decide

theorem set_step₂ : Value.crz cellMark cellOne = cellMark := by decide

theorem clear_step₁ : Value.crz cellMark cellMark = cellOne := by decide

theorem clear_step₂ : Value.crz cellOne cellOne = cellBlank := by decide

/-- **Set.** Two visits to the cell, the accumulator at `blank` then at
`eof`, take a blank register cell to a mark. -/
theorem register_set :
    Value.crz cellMark (Value.crz cellBlank cellBlank) = cellMark := by
  rw [set_step₁, set_step₂]

/-- **Clear.** Two visits, the accumulator at `eof` then at `one`, take a
marked register cell back to blank. -/
theorem register_clear :
    Value.crz cellOne (Value.crz cellMark cellMark) = cellBlank := by
  rw [clear_step₁, clear_step₂]

/-- Neither direction is possible in one operation: no column of the crazy
table joins `...000` to `...222`, in either direction. This is why writing
a register costs two visits, and it is the same gap that makes
`crz_two_steps` need two. -/
theorem no_single_step_blank_to_mark (α : Trit) : crzTrit α .t0 ≠ .t2 := by
  cases α <;> decide

theorem no_single_step_mark_to_blank (α : Trit) : crzTrit α .t2 ≠ .t0 := by
  cases α <;> decide

/-! ## Registers as a difference of two tapes

The one piece of the design that resisted was `dec`. A unary register with
`n` marks at the front needs its *last* mark cleared, and `d` moves forward
one cell per instruction or jumps to a value already stored in memory. It
cannot step back, and it cannot learn where it is, since no instruction
copies `d` into memory or into the accumulator. Every layout that walks to
the end therefore arrives one cell past the mark it wants.

Representing a register as a **difference of two unary tapes** removes the
problem. Let register `r` be a pair `(p, q)` of tapes with `q ≤ p`, holding
the value `p - q`. Then

* `inc` sets the first blank of `p`,
* `dec` sets the first blank of `q`,
* `r = 0` iff the tapes have equal length,

and **all three are forward walks that set or probe a cell at the boundary
they stop on**. Nothing ever needs clearing, so nothing ever needs stepping
back. The tapes only grow, which costs memory the language has in
unlimited supply and buys the one motion the machine cannot perform.

The zero test is a walk over the two tapes interleaved: since `q ≤ p`, the
walk halts at the first blank of `q`, and the register is zero exactly when
`p` is blank there too. So the three commands share one gadget shape, a
forward walk to a boundary followed by a set or a probe.

What follows is the arithmetic of that representation. The machine-level
gadgets are the remaining work; see
`docs/malbolge-unshackled/completeness-progress.md`. -/

/-- A counter-machine register, as two unary tape lengths. -/
structure TapePair where
  /-- Marks written by `inc`. -/
  p : Nat
  /-- Marks written by `dec`. -/
  q : Nat
deriving DecidableEq, Repr

namespace TapePair

/-- The register's value. -/
def value (x : TapePair) : Nat := x.p - x.q

/-- The invariant a register maintains: `dec` never outruns `inc`. -/
def Wf (x : TapePair) : Prop := x.q ≤ x.p

/-- The all-zero register. -/
def zero : TapePair := ⟨0, 0⟩

theorem zero_wf : zero.Wf := Nat.le_refl 0

theorem value_zero : zero.value = 0 := rfl

/-- `inc` extends the first tape. -/
def inc (x : TapePair) : TapePair := ⟨x.p + 1, x.q⟩

/-- `dec` extends the second. -/
def dec (x : TapePair) : TapePair := ⟨x.p, x.q + 1⟩

@[simp] theorem inc_p (x : TapePair) : x.inc.p = x.p + 1 := rfl
@[simp] theorem inc_q (x : TapePair) : x.inc.q = x.q := rfl
@[simp] theorem dec_p (x : TapePair) : x.dec.p = x.p := rfl
@[simp] theorem dec_q (x : TapePair) : x.dec.q = x.q + 1 := rfl

theorem inc_wf {x : TapePair} (h : x.Wf) : x.inc.Wf := by
  show x.q ≤ x.p + 1
  unfold Wf at h
  omega

/-- `dec` preserves the invariant exactly when the register is nonzero,
which is the side condition the counter machine already imposes: its `dec`
has no rule at zero. -/
theorem dec_wf {x : TapePair} (h : x.Wf) (hnz : x.value ≠ 0) : x.dec.Wf := by
  show x.q + 1 ≤ x.p
  unfold value at hnz
  unfold Wf at h
  omega

theorem value_inc {x : TapePair} (h : x.Wf) : x.inc.value = x.value + 1 := by
  show x.p + 1 - x.q = x.p - x.q + 1
  unfold Wf at h
  omega

theorem value_dec (x : TapePair) : x.dec.value = x.value - 1 := by
  show x.p - (x.q + 1) = x.p - x.q - 1
  omega

theorem value_inc_ne_zero {x : TapePair} (h : x.Wf) : x.inc.value ≠ 0 := by
  rw [value_inc h]
  omega

/-- **The zero test is a length comparison**, which a walk over the two
tapes interleaved decides at the first blank of `q`. -/
theorem value_eq_zero_iff {x : TapePair} (h : x.Wf) : x.value = 0 ↔ x.p = x.q := by
  unfold value Wf at *
  omega

/-- The walk halts on `q` first, so `p` is still readable there. -/
theorem q_le_p {x : TapePair} (h : x.Wf) : x.q ≤ x.p := h

/-- Nothing is ever cleared: both operations only ever extend a tape, which
is what makes them forward walks. -/
theorem inc_monotone (x : TapePair) : x.p ≤ x.inc.p ∧ x.q ≤ x.inc.q :=
  ⟨Nat.le_succ _, Nat.le_refl _⟩

theorem dec_monotone (x : TapePair) : x.p ≤ x.dec.p ∧ x.q ≤ x.dec.q :=
  ⟨Nat.le_refl _, Nat.le_succ _⟩

end TapePair

/-! ## The register file

A whole counter-machine state, in the two-tape representation: one
`TapePair` per register, plus a count of the bytes emitted. `Refines` is
the correspondence to `Counter.CState`, and the three lemmas below say the
representation tracks `up`, `down` and `emitOne` exactly. They are what a
simulation proof will carry as its invariant on the data side. -/

/-- One `TapePair` for every register. -/
def RegFile : Type := Nat → TapePair

namespace RegFile

/-- Every register satisfies the tape invariant. -/
def Wf (f : RegFile) : Prop := ∀ r, (f r).Wf

/-- The values the file denotes. -/
def value (f : RegFile) : Nat → Nat := fun r => (f r).value

def init : RegFile := fun _ => TapePair.zero

theorem init_wf : init.Wf := fun _ => TapePair.zero_wf

theorem value_init : init.value = fun _ => 0 := rfl

/-- `inc r`. -/
def up (f : RegFile) (r : Nat) : RegFile := Function.update f r (f r).inc

/-- `dec r`. -/
def down (f : RegFile) (r : Nat) : RegFile := Function.update f r (f r).dec

theorem up_self (f : RegFile) (r : Nat) : (f.up r) r = (f r).inc :=
  Function.update_self (β := fun _ => TapePair) r (f r).inc f

theorem up_of_ne (f : RegFile) {r k : Nat} (h : k ≠ r) : (f.up r) k = f k :=
  Function.update_of_ne (β := fun _ => TapePair) h (f r).inc f

theorem down_self (f : RegFile) (r : Nat) : (f.down r) r = (f r).dec :=
  Function.update_self (β := fun _ => TapePair) r (f r).dec f

theorem down_of_ne (f : RegFile) {r k : Nat} (h : k ≠ r) : (f.down r) k = f k :=
  Function.update_of_ne (β := fun _ => TapePair) h (f r).dec f

theorem up_wf {f : RegFile} (h : f.Wf) (r : Nat) : (f.up r).Wf := by
  intro k
  by_cases hk : k = r
  · subst hk; rw [up_self]; exact TapePair.inc_wf (h k)
  · rw [up_of_ne f hk]; exact h k

theorem down_wf {f : RegFile} (h : f.Wf) {r : Nat} (hnz : (f r).value ≠ 0) :
    (f.down r).Wf := by
  intro k
  by_cases hk : k = r
  · subst hk; rw [down_self]; exact TapePair.dec_wf (h k) hnz
  · rw [down_of_ne f hk]; exact h k

/-! ### Tracking the counter machine -/

/-- The file refines a counter-machine state when every register denotes
the value that state holds. -/
def Refines (f : RegFile) (out : Nat) (s : Counter.CState) : Prop :=
  f.Wf ∧ (∀ r, (f r).value = s.regs r) ∧ out = s.out

theorem refines_init : Refines init 0 ⟨fun _ => 0, 0⟩ :=
  ⟨init_wf, fun _ => rfl, rfl⟩

/-- `inc` is tracked. -/
theorem refines_up {f : RegFile} {out : Nat} {s : Counter.CState}
    (h : Refines f out s) (r : Nat) : Refines (f.up r) out (s.up r) := by
  obtain ⟨hwf, hval, hout⟩ := h
  refine ⟨up_wf hwf r, fun k => ?_, hout⟩
  by_cases hk : k = r
  · subst hk
    rw [up_self, Counter.CState.up_regs_self, TapePair.value_inc (hwf k), hval k]
  · rw [up_of_ne f hk, Counter.CState.up_regs_of_ne s hk]
    exact hval k

/-- `dec` is tracked, under the nonzero side condition the counter machine
already imposes. -/
theorem refines_down {f : RegFile} {out : Nat} {s : Counter.CState}
    (h : Refines f out s) {r : Nat} (hnz : s.regs r ≠ 0) :
    Refines (f.down r) out (s.down r) := by
  obtain ⟨hwf, hval, hout⟩ := h
  have hnz' : (f r).value ≠ 0 := by rw [hval r]; exact hnz
  refine ⟨down_wf hwf hnz', fun k => ?_, hout⟩
  by_cases hk : k = r
  · subst hk
    rw [down_self, Counter.CState.down_regs_self, TapePair.value_dec (f k), hval k]
  · rw [down_of_ne f hk, Counter.CState.down_regs_of_ne s hk]
    exact hval k

/-- `emit` is tracked. -/
theorem refines_emit {f : RegFile} {out : Nat} {s : Counter.CState}
    (h : Refines f out s) : Refines f (out + 1) s.emitOne := by
  obtain ⟨hwf, hval, hout⟩ := h
  exact ⟨hwf, hval, by rw [hout]; rfl⟩

/-- **The loop condition reads off the tape lengths.** A compiled `loop r b`
tests whether register `r` is zero, and in this representation that is
exactly whether its two tapes are equally long, which is what the walk over
the interleaved pair decides. -/
theorem refines_zero_iff {f : RegFile} {out : Nat} {s : Counter.CState}
    (h : Refines f out s) (r : Nat) : s.regs r = 0 ↔ (f r).p = (f r).q := by
  obtain ⟨hwf, hval, _⟩ := h
  rw [← hval r]
  exact TapePair.value_eq_zero_iff (hwf r)

end RegFile

/-! ## Where the tapes live

The layout. Data begins at `DB`; index `i` of every tape occupies one slot
of `SI` addresses starting at `DB + i * SI`; inside a slot, register `r`
keeps its `p` cell at offset `2r` and its `q` cell at offset `2r + 1`. With
`2R ≤ SI` the slots hold all `R` registers and the addresses are distinct.

Interleaving the two tapes of a register, and all the registers, into one
slot is what makes a walk work: `d` advances a fixed amount per gadget, so
choosing `SI` to be the gadget's length makes one iteration of the walk
step from slot `i` to slot `i + 1` with no address arithmetic at all. Every
cell a gadget needs at index `i` is inside slot `i`, reachable as `d`
sweeps across it.

`RegMem` is the invariant: every cell of every tape holds a mark exactly
while its index is below that tape's length. -/

/-- The address of cell `i` of one tape of register `r`. `q` selects the
second tape. -/
def regAddr (DB SI r : Nat) (q : Bool) (i : Nat) : Nat :=
  DB + (i * SI + (2 * r + (if q then 1 else 0)))

/-- Two slot decompositions with remainders below the stride agree. -/
theorem slot_inj {SI : Nat} {i x i' x' : Nat}
    (hx : x < SI) (hx' : x' < SI) (h : i * SI + x = i' * SI + x') :
    i = i' ∧ x = x' := by
  rcases Nat.lt_trichotomy i i' with hlt | heq | hgt
  · exfalso
    have hle : (i + 1) * SI ≤ i' * SI := Nat.mul_le_mul_right SI hlt
    rw [Nat.succ_mul] at hle
    omega
  · exact ⟨heq, by rw [heq] at h; omega⟩
  · exfalso
    have hle : (i' + 1) * SI ≤ i * SI := Nat.mul_le_mul_right SI hgt
    rw [Nat.succ_mul] at hle
    omega

theorem regAddr_inj {DB SI R : Nat} (hSI : 2 * R ≤ SI)
    {r r' : Nat} (hr : r < R) (hr' : r' < R) {q q' : Bool} {i i' : Nat}
    (h : regAddr DB SI r q i = regAddr DB SI r' q' i') :
    r = r' ∧ q = q' ∧ i = i' := by
  have hb : (if q then 1 else 0) < 2 := by cases q <;> decide
  have hb' : (if q' then 1 else 0) < 2 := by cases q' <;> decide
  have h' : i * SI + (2 * r + (if q then 1 else 0))
      = i' * SI + (2 * r' + (if q' then 1 else 0)) := Nat.add_left_cancel h
  obtain ⟨hi, hx⟩ := slot_inj (by omega) (by omega) h'
  refine ⟨by omega, ?_, hi⟩
  cases q <;> cases q' <;> revert hx <;> simp <;> omega

/-- **The layout invariant.** Cell `i` of a tape holds a mark exactly while
`i` is below that tape's length. -/
def RegMem (DB SI R : Nat) (f : RegFile) (m : Memory) : Prop :=
  ∀ r, r < R → ∀ i,
    (m.get (Value.ofNat (regAddr DB SI r false i))
      = if i < (f r).p then cellMark else cellBlank)
    ∧ (m.get (Value.ofNat (regAddr DB SI r true i))
      = if i < (f r).q then cellMark else cellBlank)

/-- The cell a walk halts on is the first blank of its tape, and `inc`
writes exactly there. -/
theorem regMem_first_blank {DB SI R : Nat} {f : RegFile} {m : Memory}
    (h : RegMem DB SI R f m) {r : Nat} (hr : r < R) :
    m.get (Value.ofNat (regAddr DB SI r false (f r).p)) = cellBlank := by
  rw [(h r hr (f r).p).1, if_neg (by omega)]

theorem regMem_first_blank_q {DB SI R : Nat} {f : RegFile} {m : Memory}
    (h : RegMem DB SI R f m) {r : Nat} (hr : r < R) :
    m.get (Value.ofNat (regAddr DB SI r true (f r).q)) = cellBlank := by
  rw [(h r hr (f r).q).2, if_neg (by omega)]

/-- Everything before it is a mark, which is what the walk steps over. -/
theorem regMem_mark_below {DB SI R : Nat} {f : RegFile} {m : Memory}
    (h : RegMem DB SI R f m) {r : Nat} (hr : r < R) {i : Nat} (hi : i < (f r).p) :
    m.get (Value.ofNat (regAddr DB SI r false i)) = cellMark := by
  rw [(h r hr i).1, if_pos hi]

/-- **`inc` updates the layout.** Writing a mark at the first blank of `p`
turns a memory representing `f` into one representing `f.up r`. -/
theorem regMem_up {DB SI R : Nat} (hSI : 2 * R ≤ SI) {f : RegFile} {m : Memory}
    (h : RegMem DB SI R f m) {r : Nat} (hr : r < R) :
    RegMem DB SI R (f.up r)
      (m.set (Value.ofNat (regAddr DB SI r false (f r).p)) cellMark) := by
  intro r' hr' i
  refine ⟨?_, ?_⟩
  · by_cases hrr : r' = r
    · subst hrr
      by_cases hip : i = (f r').p
      · subst hip
        rw [get_set_self, RegFile.up_self, TapePair.inc_p]
        exact (if_pos (Nat.lt_succ_self _)).symm
      · rw [get_set_ne _ (ofNat_ne (fun hh =>
          hip (regAddr_inj hSI hr hr' hh).2.2.symm)), (h r' hr' i).1, RegFile.up_self]
        simp only [TapePair.inc_p]
        by_cases hlt : i < (f r').p
        · rw [if_pos hlt]
          exact (if_pos (show i < (f r').p + 1 by omega)).symm
        · rw [if_neg hlt]
          exact (if_neg (show ¬ (i < (f r').p + 1) by omega)).symm
    · rw [get_set_ne _ (ofNat_ne (fun hh =>
        hrr (regAddr_inj hSI hr hr' hh).1.symm)), (h r' hr' i).1,
        RegFile.up_of_ne f hrr]
  · rw [get_set_ne _ (ofNat_ne (fun hh =>
      Bool.noConfusion (regAddr_inj hSI hr hr' hh).2.1))]
    by_cases hrr : r' = r
    · subst hrr; rw [(h r' hr' i).2, RegFile.up_self, TapePair.inc_q]
    · rw [(h r' hr' i).2, RegFile.up_of_ne f hrr]

/-- **`dec` updates the layout**, symmetrically, on the second tape. -/
theorem regMem_down {DB SI R : Nat} (hSI : 2 * R ≤ SI) {f : RegFile} {m : Memory}
    (h : RegMem DB SI R f m) {r : Nat} (hr : r < R) :
    RegMem DB SI R (f.down r)
      (m.set (Value.ofNat (regAddr DB SI r true (f r).q)) cellMark) := by
  intro r' hr' i
  refine ⟨?_, ?_⟩
  · rw [get_set_ne _ (ofNat_ne (fun hh =>
      Bool.noConfusion (regAddr_inj hSI hr hr' hh).2.1.symm))]
    by_cases hrr : r' = r
    · subst hrr; rw [(h r' hr' i).1, RegFile.down_self, TapePair.dec_p]
    · rw [(h r' hr' i).1, RegFile.down_of_ne f hrr]
  · by_cases hrr : r' = r
    · subst hrr
      by_cases hiq : i = (f r').q
      · subst hiq
        rw [get_set_self, RegFile.down_self, TapePair.dec_q]
        exact (if_pos (Nat.lt_succ_self _)).symm
      · rw [get_set_ne _ (ofNat_ne (fun hh =>
          hiq (regAddr_inj hSI hr hr' hh).2.2.symm)), (h r' hr' i).2, RegFile.down_self]
        simp only [TapePair.dec_q]
        by_cases hlt : i < (f r').q
        · rw [if_pos hlt]
          exact (if_pos (show i < (f r').q + 1 by omega)).symm
        · rw [if_neg hlt]
          exact (if_neg (show ¬ (i < (f r').q + 1) by omega)).symm
    · rw [get_set_ne _ (ofNat_ne (fun hh =>
        hrr (regAddr_inj hSI hr hr' hh).1.symm)), (h r' hr' i).2,
        RegFile.down_of_ne f hrr]

/-! ## The simulation invariant

Putting the data side together. `Sim` says a Malbolge Unshackled state
represents a counter-machine state: memory lays the tapes out as `RegMem`
says, those tapes denote the counter machine's registers, the bytes emitted
so far are its output count, and the output stream is still open.

The three lemmas below are what a gadget's correctness proof ends with.
Each says: perform the one memory write the command calls for, and the
invariant carries over to the counter machine's next state. They are proved
here, ahead of the gadgets that will invoke them, because they depend only
on the layout and not on how the write is reached. -/

/-- A Malbolge Unshackled state represents a counter-machine state. -/
structure Sim (DB SI R : Nat) (f : RegFile) (σ : Counter.CState) (s : State) : Prop where
  /-- The tapes are laid out as the layout says. -/
  mem : RegMem DB SI R f s.mem
  /-- They denote the counter machine's registers, and the byte count is
  its output. -/
  refines : RegFile.Refines f s.output.size σ
  /-- Emitting is still possible. -/
  open' : s.outClosed = false

theorem sim_init {DB SI R : Nat} {s : State}
    (hmem : RegMem DB SI R RegFile.init s.mem) (hout : s.output.size = 0)
    (hopen : s.outClosed = false) :
    Sim DB SI R RegFile.init ⟨fun _ => 0, 0⟩ s :=
  ⟨hmem, ⟨RegFile.init_wf, fun _ => rfl, hout⟩, hopen⟩

/-- **`inc` preserves the invariant.** Writing a mark at the first blank of
register `r`'s first tape carries `Sim` to the counter machine's `up r`. -/
theorem sim_inc {DB SI R : Nat} (hSI : 2 * R ≤ SI) {f : RegFile}
    {σ : Counter.CState} {s : State} (hs : Sim DB SI R f σ s) {r : Nat} (hr : r < R) :
    Sim DB SI R (f.up r) (σ.up r)
      { s with mem := s.mem.set (Value.ofNat (regAddr DB SI r false (f r).p)) cellMark } :=
  ⟨regMem_up hSI hs.mem hr, RegFile.refines_up hs.refines r, hs.open'⟩

/-- **`dec` preserves the invariant**, under the nonzero side condition the
counter machine already imposes. -/
theorem sim_dec {DB SI R : Nat} (hSI : 2 * R ≤ SI) {f : RegFile}
    {σ : Counter.CState} {s : State} (hs : Sim DB SI R f σ s) {r : Nat} (hr : r < R)
    (hnz : σ.regs r ≠ 0) :
    Sim DB SI R (f.down r) (σ.down r)
      { s with mem := s.mem.set (Value.ofNat (regAddr DB SI r true (f r).q)) cellMark } :=
  ⟨regMem_down hSI hs.mem hr, RegFile.refines_down hs.refines hnz, hs.open'⟩

/-- **`emit` preserves the invariant.** One byte appended, and the stream
stays open, so emits compose. -/
theorem sim_emit {DB SI R : Nat} {f : RegFile} {σ : Counter.CState} {s : State}
    (hs : Sim DB SI R f σ s) {s' : State}
    (hmem : s'.mem = s.mem) (hsize : s'.output.size = s.output.size + 1)
    (hopen : s'.outClosed = false) :
    Sim DB SI R f σ.emitOne s' := by
  refine ⟨by rw [hmem]; exact hs.mem, ?_, hopen⟩
  obtain ⟨hwf, hval, hout⟩ := hs.refines
  exact ⟨hwf, hval, by rw [hsize, hout]; rfl⟩

/-- The invariant survives any write outside the tapes, which is what lets
a gadget scribble on its own code and constants without disturbing the
register file. -/
theorem sim_frame {DB SI R : Nat} {f : RegFile} {σ : Counter.CState} {s s' : State}
    (hs : Sim DB SI R f σ s)
    (hmem : ∀ r, r < R → ∀ (q : Bool) (i : Nat),
      s'.mem.get (Value.ofNat (regAddr DB SI r q i))
        = s.mem.get (Value.ofNat (regAddr DB SI r q i)))
    (hout : s'.output.size = s.output.size) (hopen : s'.outClosed = s.outClosed) :
    Sim DB SI R f σ s' := by
  refine ⟨fun r hr i => ⟨?_, ?_⟩, ?_, by rw [hopen]; exact hs.open'⟩
  · rw [hmem r hr false i]; exact (hs.mem r hr i).1
  · rw [hmem r hr true i]; exact (hs.mem r hr i).2
  · obtain ⟨hwf, hval, ho⟩ := hs.refines
    exact ⟨hwf, hval, by rw [hout]; exact ho⟩

/-- **The loop condition, at the machine level.** A compiled `loop r b`
must decide whether `σ.regs r` is zero, and the invariant turns that into a
question the layout answers: the cell at index `(f r).q` of the first tape
is a mark exactly when the register is nonzero. That cell is the one a walk
over the interleaved pair halts on, and probing it is
`register_probe`. -/
theorem sim_loop_test {DB SI R : Nat} {f : RegFile} {σ : Counter.CState} {s : State}
    (hs : Sim DB SI R f σ s) {r : Nat} (hr : r < R) :
    s.mem.get (Value.ofNat (regAddr DB SI r false (f r).q))
      = (if σ.regs r = 0 then cellBlank else cellMark) := by
  obtain ⟨hwf, hval, _⟩ := hs.refines
  rw [(hs.mem r hr (f r).q).1]
  by_cases hz : σ.regs r = 0
  · rw [if_pos hz, if_neg]
    rw [← hval r] at hz
    rw [TapePair.value_eq_zero_iff (hwf r)] at hz
    omega
  · rw [if_neg hz, if_pos]
    rw [← hval r] at hz
    have := TapePair.value_eq_zero_iff (hwf r) (x := f r)
    unfold TapePair.value at hz
    have hq := hwf r
    unfold TapePair.Wf at hq
    omega

/-! ## Why a flag has to come from a cell

`crz_absorb` shows that a chain of crazy operations against compiled-in
constants can produce a uniform value. It cannot produce one that
*depends* on the accumulator, and that is the sharp reason `branch_arith`
reads its flag from a memory cell rather than computing it, and the reason
the register encoding stores blank and mark as uniform values in the first
place.

The argument is one line once the tritwise structure is in hand. A chain
against fixed constants computes, at each position independently,
`resultᵢ = fᵢ(aᵢ)` for a function `fᵢ` fixed at compile time. So two
accumulators differing at a single position produce results differing at
most at that position. But `...000` and `...222` differ at *every*
position. No chain can send one accumulator to the first and another to
the second unless they already differ everywhere.

So the encoding is forced, not chosen: a branch flag must be read from
something already uniform, which is what `cellBlank` and `cellMark` are,
and what `register_probe` returns.

Credit where due: this sharpening came from langlib-c9, working on the
Turpentine backend, after we had both been loose about what "cannot
aggregate across trit positions" actually rules out. -/

/-- A chain of crazy operations against a fixed list of constants. -/
def crzChain (a : Value) : List Value → Value
  | [] => a
  | k :: ks => crzChain (Value.crz a k) ks

/-- The trit-level chain: what one position does, independently of the
others. -/
def crzChainTrit (t : Trit) : List Trit → Trit
  | [] => t
  | k :: ks => crzChainTrit (crzTrit t k) ks

/-- **A chain acts position by position.** -/
theorem crzChain_trit : ∀ (ks : List Value) (a : Value) (i : Nat),
    (crzChain a ks).trit i = crzChainTrit (a.trit i) (ks.map (fun k => k.trit i))
  | [], a, i => rfl
  | k :: ks, a, i => by
    show (crzChain (Value.crz a k) ks).trit i
      = crzChainTrit (crzTrit (a.trit i) (k.trit i)) (ks.map (fun k => k.trit i))
    rw [crzChain_trit ks (Value.crz a k) i, crz_trit]

/-- **Positions the inputs agree on, the outputs agree on.** A chain
against compiled-in constants cannot move information between trit
positions. -/
theorem crzChain_agree {a a' : Value} {ks : List Value} {j : Nat}
    (h : a.trit j = a'.trit j) : (crzChain a ks).trit j = (crzChain a' ks).trit j := by
  rw [crzChain_trit, crzChain_trit, h]

/-- **No chain computes an accumulator-dependent flag.** If two
accumulators differ at only one position, no chain of crazy operations
against compiled-in constants sends one to `...000` and the other to
`...222`, because those differ at every position. A branch flag therefore
has to be *read* from something already uniform, which is why registers
store blank and mark as `Value.zero` and `Value.eof` and why
`register_probe` is the only zero test in the development. -/
theorem no_accumulator_flag {a a' : Value} (ks : List Value) {i : Nat}
    (hagree : ∀ j, j ≠ i → a.trit j = a'.trit j) :
    ¬ (crzChain a ks = Value.zero ∧ crzChain a' ks = Value.eof) := by
  rintro ⟨h₀, h₂⟩
  -- pick any position other than `i`
  have hne : i + 1 ≠ i := by omega
  have hj := crzChain_agree (ks := ks) (hagree (i + 1) hne)
  rw [h₀, h₂] at hj
  exact Trit.noConfusion hj

/-- The same conclusion stated the way a compiler meets it: the two flag
values differ everywhere, so nothing computed position-by-position from a
single-position difference can tell them apart. -/
theorem flags_differ_everywhere (j : Nat) :
    Value.zero.trit j ≠ Value.eof.trit j := by
  show Trit.t0 ≠ Trit.t2
  decide

/-! ## Two printability conditions that look alike

A `jmp` involves two cells, and only one of them needs a printability side
condition. The distinction is easy to get backwards, so it is worth a
theorem rather than a convention.

**The jumping cell needs none.** `decode` returns `outOfBounds` exactly when
its word is unprintable, so any hypothesis of the form
`decode (mem.get c) … = .jmp` already carries printability with it. That is
why `chain_link`, `chain_run`, `enter_chain` and `gadget_run` ask nothing
about the word at the jumping cell beyond how it decodes.

**The landing cell needs one.** The postal stage reads at `c` *after* the
instruction has run, and a `jmp` has already moved `c` to its target, so it
is the target's word that gets encrypted and the target's word that must be
printable. This is `jmp_cell_stable` seen from the other side: the same
fact that spares the jumping cell puts the burden on the target. Every
`hprT` hypothesis in the gadget lemmas is this one, and none of them is
removable.

Reported by langlib-c9, from the Turpentine backend, where the same pair
shows up as "`wordFor` produces printable words by construction" against
"the cell a jump lands on must be printable". -/

/-- `outOfBounds` is not an opcode: it is how the interpreter reports an
unprintable word, never something `ofOpcode?` produces. -/
theorem ofOpcode?_ne_outOfBounds (q : Nat) : Instr.ofOpcode? q ≠ some .outOfBounds := by
  unfold Instr.ofOpcode?
  split <;> simp

/-- `decode` is `outOfBounds` exactly on unprintable words. -/
theorem decode_outOfBounds_iff {w : Value} {m : Nat} :
    decode w m = .outOfBounds ↔ printableCode? w = none := by
  unfold decode
  cases h : printableCode? w with
  | none => simp
  | some n =>
    simp only [reduceCtorEq, iff_false]
    cases hq : Instr.ofOpcode? ((n + m) % 94) with
    | none => simp
    | some i =>
      have hne := ofOpcode?_ne_outOfBounds ((n + m) % 94)
      rw [hq] at hne
      simp only [Option.getD_some]
      intro hcon
      exact hne (by rw [hcon])

/-- **A cell that decodes to anything but `outOfBounds` is printable.** So a
jumping cell's printability never needs stating: its decode hypothesis
implies it. -/
theorem printable_of_decode {w : Value} {m : Nat} (h : decode w m ≠ .outOfBounds) :
    ∃ code, printableCode? w = some code := by
  cases hp : printableCode? w with
  | none => exact absurd (decode_outOfBounds_iff.mpr hp) h
  | some code => exact ⟨code, rfl⟩

/-- In particular for a `jmp`. -/
theorem printable_of_decode_jmp {w : Value} {m : Nat} (h : decode w m = .jmp) :
    ∃ code, printableCode? w = some code :=
  printable_of_decode (by rw [h]; simp)

/-! ## A cheaper branch than the pipeline

`branch_arith` turns a flag into either of two arbitrary targets in seven
crazy operations, which is what you need when the targets are arbitrary. A
loop does not need that. Its two destinations are fixed at compile time,
and the flag it branches on is already one of exactly two values, so the
successor function does the work for free.

The two flags are `Value.zero` and `Value.eof`, and 3-adic successor sends
them to **different, adjacent, compiler-controlled addresses**: `...000 + 1`
is `1`, while `...222 + 1` wraps to `0`. So writing the flag into a cell
and then `movd`-ing through that cell lands `d` on address 1 or address 0
according to the flag, and a following `jmp` reads whichever target the
compiler put there.

Three instructions, against the pipeline's seven, and nothing is consumed
that the next probe does not rewrite anyway. The catch is that addresses 0
and 1 are where execution begins, so a compiler using this branch must
either place its prologue elsewhere or arrange for those two cells to hold
jump targets by the time any branch runs. langlib-c9 met the same two
addresses from the other side, as "pinned" table entries in the Turpentine
backend; they are not an artefact of a prologue but a consequence of
`eof.succ = 0`. -/

theorem succ_blank : cellBlank.succ = Value.ofNat 1 := by decide

theorem succ_mark : cellMark.succ = Value.ofNat 0 := by decide

/-- **The flag selects between two adjacent addresses.** After a `movd`
through a cell holding the flag, `d` is `1` for a blank and `0` for a mark.
Both are cells the compiler owns, so a following `jmp` reads whichever
target it laid there. -/
theorem flag_selects_address {v : Value} (h : v = cellBlank ∨ v = cellMark) :
    v.succ = Value.ofNat (if v = cellBlank then 1 else 0) := by
  rcases h with h | h <;> subst h
  · rw [if_pos rfl]; exact succ_blank
  · rw [if_neg (by decide)]; exact succ_mark

/-! ## A branch into two natural addresses, in two operations

`flag_selects_address` above branches in three instructions but lands `d`
on address 0 or 1, which is where execution begins. This section pays one
extra `crazy` and buys the two landing sites back: **two crazy operations
against `...111` and the natural `2 * 3 ^ j` send a blank to the address
`2 * 3 ^ j` and a mark to the address `3 ^ j`**, for any `j` the compiler
likes. Both are naturals, both are as far up in memory as the compiler
wants, and the first constant is the same `...111` the ladder and the
register probe already keep.

Why two is the least possible, and why two suffice. One operation cannot
do it: a single column of the crazy table sends the blank flag to `1` or
`2` at every trit position (`no_single_step_blank_to_mark` is the missing
entry), so the blank-side result has a repeating trit of `1` or `2` and is
not a natural at all — the jump would land in the memory fill, which
`restTable_not_printable` says can hang. Two columns composed give seven of
the nine possible trit pairs, including `(0, 0)` at every high position,
which is what keeps both results natural, and `(2, 1)` at position `j`,
which is what makes them differ. `...111` then `2 * 3 ^ j` realises exactly
that choice.

This is not in tension with `no_accumulator_flag`: that theorem says no
chain can compute a *uniform* value depending on the accumulator, and
these two targets are not uniform. Reading a flag is still the only way to
get one.

The two constant cells behave differently, and a gadget author needs both
facts. On the blank path the second cell is left holding exactly what it
held (`flag_branch_blank` is an equation between the operand and the
result), so it is self-restoring; on the mark path both cells are consumed
and must be restocked before the next pass. -/

/-- The value with trit `t` at position `j` and zeros elsewhere. -/
def digitAt (t : Trit) (j : Nat) : Value := ⟨.t0, List.replicate j Trit.t0 ++ [t]⟩

theorem trit_digitAt (t : Trit) (j : Nat) :
    ∀ i, (digitAt t j).trit i = if i = j then t else .t0 := by
  intro i
  show (List.replicate j Trit.t0 ++ [t]).getD i Trit.t0 = _
  induction j generalizing i with
  | zero =>
    cases i with
    | zero => rfl
    | succ k => simp [List.getD]
  | succ j ih =>
    cases i with
    | zero => simp [List.getD]
    | succ k =>
      show (List.replicate j Trit.t0 ++ [t]).getD k Trit.t0 = _
      rw [ih k]
      simp

theorem digitAt_normalized {t : Trit} (h : t ≠ .t0) (j : Nat) :
    (digitAt t j).Normalized := by
  show lastTrit? (List.replicate j Trit.t0 ++ [t]) ≠ some Trit.t0
  rw [lastTrit?_eq_getD (by simp) Trit.t0, getD_lt (by simp),
    List.getElem_append_right (by simp)]
  simpa using h

theorem trits3_two_pow3 : ∀ j, trits3 (2 * 3 ^ j) = List.replicate j Trit.t0 ++ [Trit.t2]
  | 0 => by
    show trits3 2 = [Trit.t2]
    rw [show (2:Nat) = 1 + 1 from rfl, trits3_succ, ofResidue_two (by omega),
      show (1 + 1) / 3 = 0 by omega, trits3_zero]
  | j + 1 => by
    rw [show 2 * 3 ^ (j + 1) = 3 * (2 * 3 ^ j) by
        rw [Nat.pow_succ]; omega,
      trits3_three_mul (Nat.mul_pos (by omega) (Nat.pow_pos (by omega))),
      trits3_two_pow3 j]
    rfl

theorem digitAt_one_eq (j : Nat) : digitAt Trit.t1 j = Value.ofNat (3 ^ j) := by
  rw [ofNat_eq, trits3_pow3]
  rfl

theorem digitAt_two_eq (j : Nat) : digitAt Trit.t2 j = Value.ofNat (2 * 3 ^ j) := by
  rw [ofNat_eq, trits3_two_pow3]
  rfl

theorem crz_mark_one : Value.crz cellMark cellOne = cellMark := by decide

/-- **Two operations send a blank to the address `2 * 3 ^ j`**, leaving the
second constant cell holding exactly what it held before. -/
theorem flag_branch_blank (j : Nat) :
    Value.crz (Value.crz cellBlank cellOne) (digitAt Trit.t2 j) = digitAt Trit.t2 j := by
  rw [ladder_blank_to_one]
  apply ext_of_trits (crz_normalized _ _) (digitAt_normalized (t := Trit.t2) (by decide) j)
    (by rw [crz_lead]; rfl)
  intro i
  rw [crz_trit, trit_digitAt Trit.t2 j i, trit_uniform]
  by_cases h : i = j
  · rw [if_pos h]; rfl
  · rw [if_neg h]; rfl

/-- **And a mark to the address `3 ^ j`.** -/
theorem flag_branch_mark (j : Nat) :
    Value.crz (Value.crz cellMark cellOne) (digitAt Trit.t2 j) = digitAt Trit.t1 j := by
  rw [crz_mark_one]
  apply ext_of_trits (crz_normalized _ _) (digitAt_normalized (t := Trit.t1) (by decide) j)
    (by rw [crz_lead]; rfl)
  intro i
  rw [crz_trit, trit_digitAt Trit.t2 j i, trit_digitAt Trit.t1 j i,
    show cellMark.trit i = Trit.t2 from rfl]
  by_cases h : i = j
  · rw [if_pos h, if_pos h]; rfl
  · rw [if_neg h, if_neg h]; rfl

/-- The address a flag selects: `2 * 3 ^ j` for a blank, `3 ^ j` for a mark. -/
def flagAddr (j : Nat) (v : Value) : Nat := if v = cellBlank then 2 * 3 ^ j else 3 ^ j

theorem flag_branch (j : Nat) {v : Value} (h : v = cellBlank ∨ v = cellMark) :
    Value.crz (Value.crz v cellOne) (digitAt Trit.t2 j)
      = Value.ofNat (flagAddr j v) := by
  rcases h with h | h <;> subst h
  · rw [flag_branch_blank, digitAt_two_eq, flagAddr, if_pos rfl]
  · rw [flag_branch_mark, digitAt_one_eq, flagAddr, if_neg (by decide)]

/-- **The flag-to-address gadget.** Three instructions: two `crazy` cells
turn a flag in the accumulator into a natural address, and one `movd` aims
`d` at the cell holding it, so that a following `jmp` branches. -/
theorem flagAddr_gadget (j : Nat) {s₀ : State} {c₀ d₀ : Nat} (w : Nat → Nat)
    (hflag : s₀.a = cellBlank ∨ s₀.a = cellMark)
    (hc : s₀.c = Value.ofNat c₀) (hd : s₀.d = Value.ofNat d₀)
    (hsep : c₀ + 3 ≤ d₀)
    (hdec : ∀ i < 2, decode (s₀.mem.get (Value.ofNat (c₀ + i)))
      (Value.ofNat (c₀ + i)).modClass = .crazy)
    (hmovd : decode (s₀.mem.get (Value.ofNat (c₀ + 2)))
      (Value.ofNat (c₀ + 2)).modClass = .movd)
    (hprint : ∀ i < 3, printableCode? (s₀.mem.get (Value.ofNat (c₀ + i)))
      = some (w i))
    (hK0 : s₀.mem.get (Value.ofNat d₀) = cellOne)
    (hK1 : s₀.mem.get (Value.ofNat (d₀ + 1)) = digitAt Trit.t2 j)
    (hKp : s₀.mem.get (Value.ofNat (d₀ + 2)) = Value.ofNat d₀) :
    ∃ s', run? 3 s₀ = some s'
      ∧ s'.a = Value.ofNat (flagAddr j s₀.a)
      ∧ s'.c = Value.ofNat (c₀ + 3)
      ∧ s'.d = Value.ofNat (d₀ + 1)
      ∧ s'.mem.get (Value.ofNat (d₀ + 1)) = Value.ofNat (flagAddr j s₀.a)
      ∧ (∀ addr, (∀ i < 3, addr ≠ Value.ofNat (c₀ + i)) →
          (∀ k < 2, addr ≠ Value.ofNat (d₀ + k)) →
          s'.mem.get addr = s₀.mem.get addr)
      ∧ s'.input = s₀.input ∧ s'.output = s₀.output ∧ s'.outClosed = s₀.outClosed := by
  obtain ⟨s₂, hrun2, hA, hC, hD, hDs, hCs, hframe, hin, hout, hoc, hrw, hmw⟩ :=
    crazy_run 2 w hc hd (by omega) (fun i hi => hdec i hi)
      (fun i hi => hprint i (by omega))
  have hfold : crzFold s₀.mem d₀ s₀.a 2 = Value.ofNat (flagAddr j s₀.a) := by
    show Value.crz (Value.crz s₀.a (s₀.mem.get (Value.ofNat (d₀ + 0))))
        (s₀.mem.get (Value.ofNat (d₀ + 1))) = _
    rw [show d₀ + 0 = d₀ from rfl, hK0, hK1]
    exact flag_branch j hflag
  have hcell2 : s₂.mem.get (Value.ofNat (c₀ + 2)) = s₀.mem.get (Value.ofNat (c₀ + 2)) :=
    hframe _ (fun i hi => ofNat_ne (by omega)) (fun k hk => ofNat_ne (by omega))
  have hop2 : s₂.mem.get (Value.ofNat (d₀ + 2)) = Value.ofNat d₀ := by
    rw [hframe _ (fun i hi => ofNat_ne (by omega)) (fun k hk => ofNat_ne (by omega))]
    exact hKp
  have hstep := step1_movd (s := s₂) (code := w 2)
    (by rw [hC, hcell2]; exact hmovd)
    (by rw [hC, hcell2]; exact hprint 2 (by omega))
  rw [hD, hop2, hC] at hstep
  rw [succ_ofNat, succ_ofNat, show c₀ + 2 + 1 = c₀ + 3 by omega] at hstep
  set s₃ : State := { s₂ with mem := s₂.mem.set (Value.ofNat (c₀ + 2)) (Value.ofNat (encrypt (w 2))), c := Value.ofNat (c₀ + 3), d := Value.ofNat (d₀ + 1), maxWidth := if (Value.ofNat d₀).width > s₂.maxWidth then (Value.ofNat d₀).width else s₂.maxWidth, rotWidth := if (Value.ofNat d₀).width > s₂.maxWidth then growRotWidth s₂.rotWidth (Value.ofNat d₀).width else s₂.rotWidth } with hs₃
  have hrun3 : run? 3 s₀ = some s₃ := by
    rw [show (3 : Nat) = 2 + 1 from rfl, run?_add 2 1, hrun2, Option.bind_some,
      run?_one]
    exact hstep
  refine ⟨s₃, hrun3, ?_, rfl, rfl, ?_, ?_, hin, hout, hoc⟩
  · show s₂.a = _
    rw [hA]; exact hfold
  · show (s₂.mem.set (Value.ofNat (c₀ + 2)) (Value.ofNat (encrypt (w 2)))).get
      (Value.ofNat (d₀ + 1)) = _
    rw [get_set_ne _ (ofNat_ne (by omega)), hDs 1 (by omega)]
    exact hfold
  · intro addr hac had
    show (s₂.mem.set (Value.ofNat (c₀ + 2)) (Value.ofNat (encrypt (w 2)))).get addr = _
    rw [get_set_ne _ (Ne.symm (hac 2 (by omega)))]
    exact hframe addr (fun i hi => hac i (by omega)) had

/-! ## The walk

The one thing every command needs and nothing in this file had: iteration
whose length is decided by the data rather than by the compiler. `inc`,
`dec` and the loop condition are all "walk to the boundary of a tape", and
the boundary is wherever the register file says it is.

`walk_iterate` is the induction. One pass costs a fixed `k` steps and
carries the walk from slot `i` to slot `i + 1`, which the layout makes free:
`regAddr`'s slot stride `SI` is the pass length, so `d` advancing one per
instruction arrives at the next slot with no address arithmetic. The number
of passes is the tape length, so the run is `k * n` steps for an `n` the
compiler never knows.

`walk_branch_target` is the exit. Feeding the cell a walk is standing on to
the two-operation branch above aims control at `3 ^ j` while marks remain
and at `2 * 3 ^ j` at the first blank, so a compiler that puts the top of
the walk at one and its exit at the other gets termination at the boundary
for free. Both tapes are covered, since `inc` walks the first and `dec` the
second. -/

/-- **A walk of `n` passes runs.** One pass costs `k` steps and carries the
walk from slot `i` to slot `i + 1`; `n` of them cost `k * n`. The bound `n`
is the *data*: it comes from the register file, not from the compiler. -/
theorem walk_iterate {Iter : Nat → State → Prop} {k n : Nat}
    (hstep : ∀ i s, i < n → Iter i s → ∃ s', run? k s = some s' ∧ Iter (i + 1) s') :
    ∀ m i s, i + m = n → Iter i s → ∃ s', run? (k * m) s = some s' ∧ Iter n s' := by
  intro m
  induction m with
  | zero =>
    intro i s hi h
    refine ⟨s, by rw [Nat.mul_zero]; rfl, ?_⟩
    rw [show n = i by omega]
    exact h
  | succ m ih =>
    intro i s hi h
    obtain ⟨s₁, hr₁, h₁⟩ := hstep i s (by omega) h
    obtain ⟨s', hr', h'⟩ := ih (i + 1) s₁ (by omega) h₁
    refine ⟨s', ?_, h'⟩
    rw [show k * (m + 1) = k + k * m by rw [Nat.mul_succ, Nat.add_comm],
      run?_add k (k * m), hr₁, Option.bind_some]
    exact hr'

/-- The walk from slot `0`, which is where a gadget enters it. -/
theorem walk_run {Iter : Nat → State → Prop} {k n : Nat}
    (hstep : ∀ i s, i < n → Iter i s → ∃ s', run? k s = some s' ∧ Iter (i + 1) s')
    {s : State} (h : Iter 0 s) :
    ∃ s', run? (k * n) s = some s' ∧ Iter n s' :=
  walk_iterate hstep n 0 s (by omega) h

/-- **The walk continues exactly while there are marks.** At slot `i` of
register `r`'s first tape the flag-to-address gadget aims at `3 ^ j` while
`i` is below the tape's length, and at `2 * 3 ^ j` at the first blank. So a
compiler that puts the top of the walk at `3 ^ j` and its exit at
`2 * 3 ^ j` gets a loop that stops at the boundary, with no address
arithmetic anywhere. -/
theorem walk_branch_target {DB SI R : Nat} {f : RegFile} {m : Memory}
    (h : RegMem DB SI R f m) {r : Nat} (hr : r < R) (i j : Nat) :
    flagAddr j (m.get (Value.ofNat (regAddr DB SI r false i)))
      = if i < (f r).p then 3 ^ j else 2 * 3 ^ j := by
  rw [(h r hr i).1]
  by_cases hlt : i < (f r).p
  · rw [if_pos hlt, if_pos hlt, flagAddr, if_neg (by decide)]
  · rw [if_neg hlt, if_neg hlt, flagAddr, if_pos rfl]

/-- The same on the second tape, which is the one `dec` extends. -/
theorem walk_branch_target_q {DB SI R : Nat} {f : RegFile} {m : Memory}
    (h : RegMem DB SI R f m) {r : Nat} (hr : r < R) (i j : Nat) :
    flagAddr j (m.get (Value.ofNat (regAddr DB SI r true i)))
      = if i < (f r).q then 3 ^ j else 2 * 3 ^ j := by
  rw [(h r hr i).2]
  by_cases hlt : i < (f r).q
  · rw [if_pos hlt, if_pos hlt, flagAddr, if_neg (by decide)]
  · rw [if_neg hlt, if_neg hlt, flagAddr, if_pos rfl]

end Unshackled

end Langlib.Computability
