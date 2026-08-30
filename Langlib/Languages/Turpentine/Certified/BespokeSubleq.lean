import Langlib.Languages.Turpentine.Compile.Derived
import Langlib.Languages.Turpentine.Compile.Subleq
import Batteries.Tactic.OpenPrivate

/-!
# The hand-written Turpentine-to-Subleq backend, verified on a fragment

`Langlib/Languages/Turpentine/Compile/Derived.lean` defines `TurpentineCompiler L`, the type
of verified Turpentine compilers, and inhabits it by composing the shared
`compileToURM` pass with a completeness witness. Every inhabitant built that
way is *derived*: no new proof is written, and the program that comes out is
a register machine in disguise.

This file produces a second inhabitant for subleq, `bespokeSubleq`, whose
`compile` runs the hand-written backend in
`Langlib/Languages/Turpentine/Compile/Subleq.lean`. That is the compiler users invoke
with `lake exe turpentine compile --to subleq --bespoke`, and the image it
emits is the one this file's `correct` field is about.

## The covered fragment, and why it is this small

The bespoke backend accepts all of Turpentine. The specification a
`TurpentineCompiler` has to meet does not: `TurpentineHaltsWith p n result`
names a single natural number, the final value of the variable `answer`, on
an empty input stream. A compiled program can only report that number
through its output bytes, so a program in the covered fragment has to print
it, and the proof has to relate the printed bytes to the source value.

The backend prints integers with the `printint` runtime routine, which
builds a decimal numeral by repeated doubling and counts digits with a
quadratic rebuild of powers of ten. Proving that routine correct for
arbitrary integers is a large arithmetic development on top of a
self-modifying calling convention, and it is not attempted here. What is
proved instead is the fragment where the answer leaves the program as a
single byte through `printByte`, plus the degenerate answer-zero program
that prints nothing:

* `var answer: int := k;  printByte(answer);` for `1 ≤ k ≤ 255`;
* `var answer: int;` with an empty body, whose answer is `0`.

Both are recognised syntactically by `shapeOf`, and `compile` returns
`Except.error` on everything else. The fragment is therefore part of the
data, exactly as `TurpentineCompiler`'s doc comment asks, and the theorem is
a true statement about the programs the instance accepts rather than a
promise about the ones it does not.

## The decoding convention

`decodeOutput` reads the output bytes as a big-endian base-256 numeral:

    decodeOutput b = some (b.data.toList.foldl (fun acc x => acc * 256 + x.toNat) 0)

Empty output decodes to `0` and a single byte `b` decodes to `b`, which is
what the two covered shapes need. This is *not* the convention of the
derived compiler, whose `decodeOutput` is `some b.size` because the URM
epilogue prints the answer in unary. The two need not agree: every
`TurpentineCompiler` carries its own decoder, and `agree` equates the
*decoded answers*, not the byte strings. What would be unsound is a decoder
that ignores the output, and this one does not.

## How the proof is organised

`docs/verification.md` prescribes a state relation, per-construct simulation
lemmas, and a composition step. At the size of this fragment the three
collapse into one chain:

1. `stepSub` and `stepOut` are the per-instruction lemmas, wrapping
   `URMSubleq.reaches_sub` and `URMSubleq.reaches_out` so that every memory
   read in an instruction is named rather than recomputed.
2. `M0 … M11` are the twelve machine memories the printing image passes
   through. They play the role of the state relation: the whole invariant is
   "memory is `M i`", which is decidable by `simp` because the image is a
   closed array and every write goes to a known address.
3. `reaches_print` and `reaches_skip` compose the steps with
   `Reaches.trans`, and `eval_of_reaches` turns a chain that ends at a
   negative program counter into a statement about `evalProg`.

The Turpentine side is `haltsWith_progPrint` and `haltsWith_progSkip`, which
read the answer out of the reference semantics for the two shapes.

## What connects the two: the code generator, symbolically evaluated

`backend_skipZero` and `backend_printLit` are the link, and they are proved
rather than assumed: the real
`Langlib.Turpentine.Compile.Subleq.compile` emits exactly `imgSkip` and
`imgPrint k`. So `bespokeSubleq.compile` is the hand-written backend on the
fragment, unchanged, and `compile p = .ok prog` carries `prog = imgOf sh`
without any run-time check.

Getting there took some care. The generator threads a
`Std.HashMap`-carrying state monad through an emitter and then resolves
labels through a second hash map, and `String.hash` is `opaque`, so neither
the kernel nor `decide` can evaluate a single step of it. The proof is
therefore symbolic: `simp` unfolds the emitter with the `StateT.run_*` laws
and reasons about both hash maps through their lemma API, which never
mentions the hash function. It runs in three stages per shape, because one
`simp` over the whole pipeline is too large: `checkProgram`, then
`buildChecked` to an explicit item list, then `assembleItems` to the image.

## Agreement with the derived compiler

`bespokeSubleq_agrees_derived` is `Derived.lean`'s `agree` at this instance and
`derivedSubleq`. Its hypotheses say that both compilers accept the same
program, and for two compilers with disjoint fragments that is impossible to
satisfy, so `bespokeSubleq_agrees_derived_nonvacuous` exhibits a program in both:
`var answer: int;` with an empty body, on which both halt and both report
`0`. The overlap is that narrow because the derived compiler refuses every
I/O statement while this instance needs the answer printed.
-/

-- The code generator's helpers are `private`, so `Batteries`' `open private`
-- is what makes them nameable here. Nothing about the backend changes by
-- naming them; `simp` needs the names to unfold the emitter.
open private emitItem emitData emitI emitL emitC wZ wSc NEXT OUT tmpW varW varRef
  constW constName noteDepth mZero mSub mMov mSet mOut compileExpr compileStmt
  labelAddrs resolveWord offSuffix
  from Langlib.Languages.Turpentine.Compile.Subleq

namespace Langlib.Turpentine.Certified

open Langlib.Common
open Langlib.Computability (SubleqLang)
open Langlib.Subleq
open Langlib.Turpentine (Ty)
open Langlib.Turpentine.Compile.Subleq (Item Word Types buildChecked assembleItems)
open Langlib.Computability.URMSubleq
  (get_ofProg extent_ofProg get_set extent_set reaches_sub reaches_out exec_halt)
open Langlib.Turpentine.Compile.URM (TurpentineHaltsWith answerVar)
open Langlib.Turpentine.Compile (TurpentineCompiler derivedSubleq)

namespace BespokeSubleq

/-! ## The two images

Both are what `Langlib.Turpentine.Compile.Subleq.compile` emits today; the
addresses in them are the ones its assembler resolved. -/

/-- The image for `var answer: int := k; printByte(answer);`.

Code occupies `0 … 35` as twelve instructions, the trap sits at `36`, and
the data cells are `v_answer = 39`, `t_0 = 40`, `Z = 41`, `sc = 42`,
`scn = 43`, `scj = 44`, `w0 = 45`, `w1 = 46`, `w2 = 47`, and the literal
pool cell `km{k} = 48`, which holds `-k`. -/
def imgPrint (k : Int) : Prog :=
  #[40, 40, 3, 48, 40, 6, 42, 42, 9, 40, 42, 12, 39, 39, 15, 42, 39, 18,
    42, 42, 21, 39, 42, 24, 40, 40, 27, 42, 40, 30, 40, -1, 33,
    41, 41, -1,
    -2, -2, 39,
    0, 0, 0, 0, 0, 0, 0, 0, 0, -k]

/-- The image for `var answer: int;` with an empty body: the halt, the trap,
and the nine data cells. `Z` is at address `8`. -/
def imgSkip : Prog := #[8, 8, -1, -2, -2, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-! ## One instruction at a time

The two lemmas below are `reaches_sub` and `reaches_out` with every memory
read given a name, so that a call site states the instruction it is
executing (`A`, `B`, `C`), the values it reads (`vA`, `vB`), and where it
lands, and discharges each as a separate side goal. -/

/-- One subtract-and-branch instruction. -/
theorem stepSub {m : Mem} {pc A B C vA vB : Int} {inp : Input} {out : ByteArray}
    (hpc : 0 ≤ pc) (hext : pc < m.extent)
    (hA : m.get pc = A) (hB : m.get (pc + 1) = B) (hC : m.get (pc + 2) = C)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hvA : m.get A = vA) (hvB : m.get B = vB)
    {m' : Mem} {pc' : Int}
    (hm' : m.set B (vB - vA) = m') (hpc' : (if vB - vA ≤ 0 then C else pc + 3) = pc') :
    Reaches Langlib.Subleq.exec ⟨m, pc, inp, out⟩ ⟨m', pc', inp, out⟩ := by
  have h := reaches_sub m pc inp out hpc hext (by rw [hA]; exact hA0) (by rw [hB]; exact hB0)
  rw [hA, hB, hC, hvA, hvB, hm', hpc'] at h
  exact h

/-- One output instruction: `B` is the `-1` sentinel, so the machine emits
`mem[A] mod 256` and falls through. -/
theorem stepOut {m : Mem} {pc A vA : Int} {inp : Input} {out : ByteArray}
    (hpc : 0 ≤ pc) (hext : pc < m.extent)
    (hA : m.get pc = A) (hB : m.get (pc + 1) = -1)
    (hA0 : 0 ≤ A) (hvA : m.get A = vA) {pc' : Int} (hpc' : pc + 3 = pc') :
    Reaches Langlib.Subleq.exec ⟨m, pc, inp, out⟩ ⟨m, pc', inp, out.push ((vA.emod 256).toNat.toUInt8)⟩ := by
  have h := reaches_out m pc inp out hpc hext (by rw [hA]; exact hA0) hB
  rw [hA, hvA, hpc'] at h
  exact h

/-- Running a chain that ends at a negative program counter: the machine
halts there, so the whole image's run is the chain's output. -/
theorem eval_of_reaches {p : Prog} {m : Mem} {pc : Int} {inp : Input} {out : ByteArray}
    (h : Reaches Langlib.Subleq.exec ⟨Mem.ofProg p, 0, inp, ByteArray.empty⟩ ⟨m, pc, inp, out⟩)
    (hpc : pc < 0) :
    ∃ f, evalProg p inp f = { output := out, exit := Exit.halted } := by
  obtain ⟨f, hf⟩ := Reaches.eval h 1
  refine ⟨f, ?_⟩
  simp only [evalProg]
  rw [show ({ mem := Mem.ofProg p, input := inp } : Langlib.Subleq.State)
      = ⟨Mem.ofProg p, 0, inp, ByteArray.empty⟩ from rfl, hf, exec_halt m pc inp out hpc 0]

/-! ## The twelve memories of the printing image

`M0` is the image as loaded; `M i` is the memory after the `i`-th
instruction that writes. Only three cells are ever written: `t_0` (40),
`v_answer` (39) and `sc` (42), plus the `Z` cell (41) that the halt
instruction subtracts from itself. The code region is never touched, which
is why every read below is decided by unfolding rather than by an
invariant. -/

def M0 (k : Int) : Mem := Mem.ofProg (imgPrint k)
def M1 (k : Int) : Mem := (M0 k).set 40 0
def M2 (k : Int) : Mem := (M1 k).set 40 k
def M3 (k : Int) : Mem := (M2 k).set 42 0
def M4 (k : Int) : Mem := (M3 k).set 42 (-k)
def M5 (k : Int) : Mem := (M4 k).set 39 0
def M6 (k : Int) : Mem := (M5 k).set 39 k
def M7 (k : Int) : Mem := (M6 k).set 42 0
def M8 (k : Int) : Mem := (M7 k).set 42 (-k)
def M9 (k : Int) : Mem := (M8 k).set 40 0
def M10 (k : Int) : Mem := (M9 k).set 40 k
def M11 (k : Int) : Mem := (M10 k).set 41 0

attribute [local simp] M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 imgPrint
  get_set get_ofProg extent_set extent_ofProg

/-- **The printing image simulates its source.** Twelve instructions: two to
build `k` in `t_0`, four to move it into `v_answer`, four to move it back,
one to print it, and the halt. Every instruction's third word is the address
of the next one, so no branch is taken until the halt, and the value of `k`
never decides control flow. -/
theorem reaches_print (k : Int) (inp : Input) (out : ByteArray) :
    Reaches Langlib.Subleq.exec ⟨M0 k, 0, inp, out⟩
      ⟨M11 k, -1, inp, out.push ((k.emod 256).toNat.toUInt8)⟩ := by
  refine Reaches.trans (stepSub (m' := M1 k) (pc' := 3) (m := M0 k) (pc := 0)
      (A := 40) (B := 40) (C := 3) (vA := 0) (vB := 0)
      (by decide) (by simp) (by simp) (by simp) (by simp)
      (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)) ?_
  refine Reaches.trans (stepSub (m' := M2 k) (pc' := 6) (m := M1 k) (pc := 3)
      (A := 48) (B := 40) (C := 6) (vA := -k) (vB := 0)
      (by decide) (by simp) (by simp) (by simp) (by simp)
      (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)) ?_
  refine Reaches.trans (stepSub (m' := M3 k) (pc' := 9) (m := M2 k) (pc := 6)
      (A := 42) (B := 42) (C := 9) (vA := 0) (vB := 0)
      (by decide) (by simp) (by simp) (by simp) (by simp)
      (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)) ?_
  refine Reaches.trans (stepSub (m' := M4 k) (pc' := 12) (m := M3 k) (pc := 9)
      (A := 40) (B := 42) (C := 12) (vA := k) (vB := 0)
      (by decide) (by simp) (by simp) (by simp) (by simp)
      (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)) ?_
  refine Reaches.trans (stepSub (m' := M5 k) (pc' := 15) (m := M4 k) (pc := 12)
      (A := 39) (B := 39) (C := 15) (vA := 0) (vB := 0)
      (by decide) (by simp) (by simp) (by simp) (by simp)
      (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)) ?_
  refine Reaches.trans (stepSub (m' := M6 k) (pc' := 18) (m := M5 k) (pc := 15)
      (A := 42) (B := 39) (C := 18) (vA := -k) (vB := 0)
      (by decide) (by simp) (by simp) (by simp) (by simp)
      (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)) ?_
  refine Reaches.trans (stepSub (m' := M7 k) (pc' := 21) (m := M6 k) (pc := 18)
      (A := 42) (B := 42) (C := 21) (vA := -k) (vB := -k)
      (by decide) (by simp) (by simp) (by simp) (by simp)
      (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)) ?_
  refine Reaches.trans (stepSub (m' := M8 k) (pc' := 24) (m := M7 k) (pc := 21)
      (A := 39) (B := 42) (C := 24) (vA := k) (vB := 0)
      (by decide) (by simp) (by simp) (by simp) (by simp)
      (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)) ?_
  refine Reaches.trans (stepSub (m' := M9 k) (pc' := 27) (m := M8 k) (pc := 24)
      (A := 40) (B := 40) (C := 27) (vA := k) (vB := k)
      (by decide) (by simp) (by simp) (by simp) (by simp)
      (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)) ?_
  refine Reaches.trans (stepSub (m' := M10 k) (pc' := 30) (m := M9 k) (pc := 27)
      (A := 42) (B := 40) (C := 30) (vA := -k) (vB := 0)
      (by decide) (by simp) (by simp) (by simp) (by simp)
      (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)) ?_
  refine Reaches.trans (stepOut (pc' := 33) (m := M10 k) (pc := 30) (A := 40) (vA := k)
      (by decide) (by simp) (by simp) (by simp) (by decide) (by simp) (by simp)) ?_
  exact stepSub (m' := M11 k) (pc' := -1) (m := M10 k) (pc := 33)
    (A := 41) (B := 41) (C := -1) (vA := 0) (vB := 0)
    (by decide) (by simp) (by simp) (by simp) (by simp)
    (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)

/-- **The empty image halts at once.** `Z Z -1` subtracts the zero cell from
itself, which is `<= 0`, so the machine jumps to `-1` and stops. -/
theorem reaches_skip (inp : Input) (out : ByteArray) :
    Reaches Langlib.Subleq.exec ⟨Mem.ofProg imgSkip, 0, inp, out⟩
      ⟨(Mem.ofProg imgSkip).set 8 0, -1, inp, out⟩ :=
  stepSub (m := Mem.ofProg imgSkip) (pc := 0) (A := 8) (B := 8) (C := -1)
    (vA := 0) (vB := 0) (m' := (Mem.ofProg imgSkip).set 8 0) (pc' := -1)
    (by decide) (by simp [imgSkip]) (by simp [imgSkip]) (by simp [imgSkip]) (by simp [imgSkip])
    (by decide) (by decide) (by simp [imgSkip]) (by simp [imgSkip]) (by simp) (by simp)

theorem run_print (k : Int) (inp : Input) :
    ∃ f, evalProg (imgPrint k) inp f =
      { output := ByteArray.empty.push ((k.emod 256).toNat.toUInt8), exit := Exit.halted } :=
  eval_of_reaches (reaches_print k inp ByteArray.empty) (by decide)

theorem run_skip (inp : Input) :
    ∃ f, evalProg imgSkip inp f = { output := ByteArray.empty, exit := Exit.halted } :=
  eval_of_reaches (reaches_skip inp ByteArray.empty) (by decide)

/-! ## The fragment -/

/-- The two program shapes the instance accepts. -/
inductive Shape where
  /-- `var answer: int;` with an empty body. -/
  | skipZero
  /-- `var answer: int := k; printByte(answer);` with `1 ≤ k ≤ 255`. -/
  | printLit (k : Int)
deriving Repr

/-- The canonical program of a shape. -/
def progOf : Shape → Turpentine.Program
  | .skipZero => { decls := [("answer", .int, none)], body := .skip }
  | .printLit k =>
    { decls := [("answer", .int, some (.intLit k))]
      body := .printByte (.var "answer") }

/-- The image the backend is expected to emit for a shape. -/
def imgOf : Shape → Prog
  | .skipZero => imgSkip
  | .printLit k => imgPrint k

/-- Recognise a program of the fragment. Everything else is rejected, which
is how the fragment is stated: as data, not as prose. -/
def shapeOf (p : Turpentine.Program) : Option Shape :=
  match p.decls, p.body with
  | [("answer", Turpentine.Ty.int, none)], Turpentine.Stmt.skip => some .skipZero
  | [("answer", Turpentine.Ty.int, some (Turpentine.Expr.intLit k))],
      Turpentine.Stmt.printByte (Turpentine.Expr.var "answer") =>
    if 1 ≤ k ∧ k ≤ 255 then some (.printLit k) else none
  | _, _ => none

/-- A recognised program is its shape's canonical program. -/
theorem progOf_shapeOf {p : Turpentine.Program} {sh : Shape} (h : shapeOf p = some sh) :
    p = progOf sh := by
  rw [shapeOf] at h
  split at h
  · next hd hb =>
    cases h
    cases p
    simp_all [progOf]
  · next k hd hb =>
    split at h
    · cases h
      cases p
      simp_all [progOf]
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- The `printLit` shape carries a byte-sized literal. -/
theorem printLit_range {p : Turpentine.Program} {k : Int} (h : shapeOf p = some (.printLit k)) :
    1 ≤ k ∧ k ≤ 255 := by
  rw [shapeOf] at h
  split at h
  · exact absurd h (by simp)
  · next k' _ _ =>
    split at h
    · next hr => cases h; exact hr
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-! ## The backend really does emit these images

The code generator threads a `Std.HashMap`-carrying state monad through the
emitter and resolves labels through a second hash map. `String.hash` is
`opaque`, so neither the kernel nor `decide` can evaluate any of it, and the
two lemmas below are proved by symbolic evaluation instead: `simp` unfolds
the emitter with the `StateT.run_*` laws and reasons about the hash maps
through their lemma API, which never mentions the hash function.

`Batteries`' `open private` is what makes the emitter's helpers nameable
from here. The one fact about strings the assembler needs is `km_ne`: a
literal-pool cell is named `km<k>`, and none of the fixed cell names start
with `k`, so the pool entry never collides. -/

/-- A literal-pool cell name never collides with a fixed cell name: it starts
with `k`, and none of the fixed names do. -/
theorem km_ne (s t : String) (h : t.toList.head? ≠ some 'k') : "km" ++ s ≠ t := by
  intro he
  apply h
  rw [← he, String.toList_append]
  simp

private theorem toStringString (s : String) : toString s = s := rfl
private theorem reprZero : Nat.repr 0 = "0" := rfl
private theorem okBind {ε α β : Type _} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl

/-- `compileExpr` matches on `.bin` with an inner match, so Lean generates no
equation for it. These two are the cases the fragment uses, and both hold by
`rfl`. -/
private theorem compileExpr_intLit (types : Types) (n : Int) (d : Nat) :
    compileExpr types (.intLit n) d = (do noteDepth d; mSet (tmpW d) n) := rfl

private theorem compileExpr_var (types : Types) (x : String) (d : Nat) :
    compileExpr types (.var x) d =
      (do noteDepth d; let v ← varRef types x; mMov v (tmpW d)) := rfl

/-! ### The empty program -/

private theorem check_skipZero :
    Turpentine.checkProgram (progOf .skipZero) = .ok (({} : Types).insert "answer" Ty.int) := by
  simp [progOf, Turpentine.checkProgram, Turpentine.checkStmt]
  rfl

/-- The item list the emitter builds for the empty program: five comments,
the halt, the trap, and the nine data cells. -/
private def itemsSkip : Array Item :=
  #[.comment "compiled from Turpentine by Langlib.Turpentine.Compile.Subleq",
    .comment "see docs/subleq/compiler.md",
    .comment "--- variable initialisers ---",
    .comment "--- program body ---",
    .comment "--- halt ---",
    .instr (.ref "Z" 0) (.ref "Z" 0) (.lit (-1)) "jump to a negative address: halt",
    .comment "--- the trap: every Turpentine runtime error lands here ---",
    .label "trap",
    .instr (.lit (-2)) (.lit (-2)) (.here 1) "a forbidden negative address: fail loudly",
    .comment "--- data ---",
    .datum "v_answer" (.lit 0) "variable answer",
    .datum "t_0" (.lit 0) "expression temporary 0",
    .datum "Z" (.lit 0) "the constant zero: never changes",
    .datum "sc" (.lit 0) "macro scratch",
    .datum "scn" (.lit 0) "negation scratch",
    .datum "scj" (.lit 0) "zero-test scratch",
    .datum "w0" (.lit 0) "routine workspace",
    .datum "w1" (.lit 0) "routine workspace",
    .datum "w2" (.lit 0) "routine workspace"]

set_option maxHeartbeats 1000000 in
private theorem build_skipZero :
    Langlib.Turpentine.Compile.Subleq.buildChecked (progOf .skipZero)
      (({} : Types).insert "answer" Ty.int) = .ok itemsSkip := by
  simp [progOf, itemsSkip, buildChecked, compileStmt, varRef, emitI, emitItem, emitC, emitL,
    wZ, NEXT, StateT.run_bind, StateT.run_pure, StateT.run_get, StateT.run_modify,
    toStringString, reprZero]
  rfl

set_option maxHeartbeats 1000000 in
private theorem assemble_skipZero : assembleItems itemsSkip = .ok imgSkip := by
  simp [itemsSkip, imgSkip, assembleItems, labelAddrs, resolveWord, Item.size,
    Std.HashMap.getElem_insert]
  rfl

/-- **The backend emits `imgSkip` for the empty program.** -/
theorem backend_skipZero :
    Langlib.Turpentine.Compile.Subleq.compile (progOf .skipZero) = .ok imgSkip := by
  simp only [Langlib.Turpentine.Compile.Subleq.compile, check_skipZero, Except.mapError,
    okBind, build_skipZero, assemble_skipZero]

/-! ### The printing program -/

private theorem check_printLit (k : Int) :
    Turpentine.checkProgram (progOf (.printLit k))
      = .ok (({} : Types).insert "answer" Ty.int) := by
  simp [progOf, Turpentine.checkProgram, Turpentine.checkStmt, Turpentine.checkExpr,
    Turpentine.inferExpr]
  rfl

/-- The item list for `var answer: int := k; printByte(answer);`: twelve
instructions, the trap, nine data cells, and one literal-pool cell holding
`-k` under the name `km<k>`. -/
private def itemsPrint (k : Int) : Array Item :=
  #[.comment "compiled from Turpentine by Langlib.Turpentine.Compile.Subleq",
    .comment "see docs/subleq/compiler.md",
    .comment "--- variable initialisers ---",
    .instr (.ref "t_0" 0) (.ref "t_0" 0) (.here 1) "t_0 := 0",
    .instr (.ref ("km" ++ k.repr) 0) (.ref "t_0" 0) (.here 1) ("t_0 := " ++ k.repr),
    .instr (.ref "sc" 0) (.ref "sc" 0) (.here 1) "sc := 0",
    .instr (.ref "t_0" 0) (.ref "sc" 0) (.here 1) "sc -= t_0",
    .instr (.ref "v_answer" 0) (.ref "v_answer" 0) (.here 1) "v_answer := 0",
    .instr (.ref "sc" 0) (.ref "v_answer" 0) (.here 1) "v_answer := t_0",
    .comment "--- program body ---",
    .comment "printByte",
    .instr (.ref "sc" 0) (.ref "sc" 0) (.here 1) "sc := 0",
    .instr (.ref "v_answer" 0) (.ref "sc" 0) (.here 1) "sc -= v_answer",
    .instr (.ref "t_0" 0) (.ref "t_0" 0) (.here 1) "t_0 := 0",
    .instr (.ref "sc" 0) (.ref "t_0" 0) (.here 1) "t_0 := v_answer",
    .instr (.ref "t_0" 0) (.lit (-1)) (.here 1) "output the byte in t_0",
    .comment "--- halt ---",
    .instr (.ref "Z" 0) (.ref "Z" 0) (.lit (-1)) "jump to a negative address: halt",
    .comment "--- the trap: every Turpentine runtime error lands here ---",
    .label "trap",
    .instr (.lit (-2)) (.lit (-2)) (.here 1) "a forbidden negative address: fail loudly",
    .comment "--- data ---",
    .datum "v_answer" (.lit 0) "variable answer",
    .datum "t_0" (.lit 0) "expression temporary 0",
    .datum "Z" (.lit 0) "the constant zero: never changes",
    .datum "sc" (.lit 0) "macro scratch",
    .datum "scn" (.lit 0) "negation scratch",
    .datum "scj" (.lit 0) "zero-test scratch",
    .datum "w0" (.lit 0) "routine workspace",
    .datum "w1" (.lit 0) "routine workspace",
    .datum "w2" (.lit 0) "routine workspace",
    .comment "--- literal pool ---",
    .datum ("km" ++ k.repr) (.lit (-k)) ""]

set_option maxHeartbeats 1000000 in
private theorem build_printLit (k : Int) (hk : 0 < k) :
    Langlib.Turpentine.Compile.Subleq.buildChecked (progOf (.printLit k))
      (({} : Types).insert "answer" Ty.int) = .ok (itemsPrint k) := by
  simp [progOf, itemsPrint, buildChecked, compileStmt, compileExpr_intLit, compileExpr_var,
    varRef, mSet, mZero, mMov, mSub, mOut, noteDepth, constW, constName, tmpW, varW,
    emitI, emitItem, emitC, emitL, wZ, wSc, NEXT, OUT, Word.render,
    StateT.run_bind, StateT.run_pure, StateT.run_get, StateT.run_modify,
    toStringString, reprZero, offSuffix, hk, (show ¬ k = 0 by omega)]
  rfl

set_option maxHeartbeats 1000000 in
private theorem assemble_printLit (k : Int) : assembleItems (itemsPrint k) = .ok (imgPrint k) := by
  have h1 : ("km" ++ k.repr) ≠ "trap" := km_ne _ _ (by decide)
  have h2 : ("km" ++ k.repr) ≠ "v_answer" := km_ne _ _ (by decide)
  have h3 : ("km" ++ k.repr) ≠ "t_0" := km_ne _ _ (by decide)
  have h4 : ("km" ++ k.repr) ≠ "Z" := km_ne _ _ (by decide)
  have h5 : ("km" ++ k.repr) ≠ "sc" := km_ne _ _ (by decide)
  have h6 : ("km" ++ k.repr) ≠ "scn" := km_ne _ _ (by decide)
  have h7 : ("km" ++ k.repr) ≠ "scj" := km_ne _ _ (by decide)
  have h8 : ("km" ++ k.repr) ≠ "w0" := km_ne _ _ (by decide)
  have h9 : ("km" ++ k.repr) ≠ "w1" := km_ne _ _ (by decide)
  have h10 : ("km" ++ k.repr) ≠ "w2" := km_ne _ _ (by decide)
  simp [itemsPrint, imgPrint, assembleItems, labelAddrs, resolveWord, Item.size,
    Std.HashMap.getElem_insert, h2, h3, h4, h5,
    h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h6.symm, h7.symm, h8.symm, h9.symm, h10.symm]
  rfl

/-- **The backend emits `imgPrint k` for the printing program.** -/
theorem backend_printLit (k : Int) (hk : 0 < k) :
    Langlib.Turpentine.Compile.Subleq.compile (progOf (.printLit k)) = .ok (imgPrint k) := by
  simp only [Langlib.Turpentine.Compile.Subleq.compile, check_printLit, Except.mapError,
    okBind, build_printLit k hk, assemble_printLit]

/-! ## The reference semantics of the two shapes -/

/-- `var answer: int;` with an empty body halts with `0` in `answer`. -/
theorem haltsWith_progSkip {n result : Nat} (h : TurpentineHaltsWith (progOf .skipZero) n result) :
    result = 0 := by
  obtain ⟨env₀, st, hinit, hex, hans⟩ := h
  have henv : env₀ = (∅ : Std.HashMap String Turpentine.Value).insert "answer" (.int 0) := by
    rw [show Turpentine.initEnv (progOf .skipZero)
      = .ok ((∅ : Std.HashMap String Turpentine.Value).insert "answer" (.int 0)) from rfl] at hinit
    exact (Except.ok.inj hinit).symm
  cases n with
  | zero => simp [Turpentine.exec] at hex
  | succ n =>
    subst henv
    simp only [progOf, Turpentine.exec, Prod.mk.injEq] at hex
    rw [← hex.1] at hans
    simp [answerVar] at hans
    omega

/-- `var answer: int := k; printByte(answer);` halts with `k` in `answer`,
having printed the single byte `k mod 256`. -/
theorem haltsWith_progPrint {k : Int} {n result : Nat}
    (h : TurpentineHaltsWith (progOf (.printLit k)) n result) : (result : Int) = k := by
  obtain ⟨env₀, st, hinit, hex, hans⟩ := h
  have henv : env₀ = (∅ : Std.HashMap String Turpentine.Value).insert "answer" (.int k) := by
    rw [show Turpentine.initEnv (progOf (.printLit k))
      = .ok ((∅ : Std.HashMap String Turpentine.Value).insert "answer" (.int k)) from rfl] at hinit
    exact (Except.ok.inj hinit).symm
  cases n with
  | zero => simp [Turpentine.exec] at hex
  | succ n =>
    subst henv
    simp only [progOf, Turpentine.exec, Turpentine.evalExpr, Std.HashMap.getElem?_insert,
      BEq.rfl, if_true, pure, Except.pure, Prod.mk.injEq] at hex
    rw [← hex.1] at hans
    simp [answerVar] at hans
    omega

/-! ## The instance -/

/-- The answer, read out of the output bytes as a big-endian base-256
numeral. Empty output is `0`; one byte is that byte. -/
def decodeOutput (b : ByteArray) : Option Nat :=
  some (b.data.toList.foldl (fun acc x => acc * 256 + x.toNat) 0)

theorem decodeOutput_empty : decodeOutput ByteArray.empty = some 0 := rfl

theorem decodeOutput_push (x : UInt8) :
    decodeOutput (ByteArray.empty.push x) = some x.toNat := by
  simp [decodeOutput]

/-- **The instance's compiler: the hand-written backend, restricted.** On a
program of the fragment it *is*
`Langlib.Turpentine.Compile.Subleq.compile`, byte for byte; everything else
is refused. -/
def compile (p : Turpentine.Program) : Except String Prog :=
  match shapeOf p with
  | none =>
    .error "outside the verified fragment of the bespoke subleq backend: it covers \
      'var answer: int := k; printByte(answer);' for 1 <= k <= 255 and \
      'var answer: int;' with an empty body"
  | some _ => Langlib.Turpentine.Compile.Subleq.compile p

/-- What `compile` accepting a program tells its caller: it is one of the two
shapes, and the image is the one the simulation above is about. -/
theorem compile_eq {p : Turpentine.Program} {prog : Prog} (h : compile p = .ok prog) :
    ∃ sh, shapeOf p = some sh ∧ prog = imgOf sh := by
  rw [compile] at h
  split at h
  · exact absurd h (by simp)
  · next sh hsh =>
    refine ⟨sh, hsh, ?_⟩
    rw [progOf_shapeOf hsh] at h
    cases sh with
    | skipZero =>
      rw [backend_skipZero] at h
      exact (Except.ok.inj h).symm
    | printLit k =>
      have hk : 0 < k := by have := printLit_range hsh; omega
      rw [backend_printLit k hk] at h
      exact (Except.ok.inj h).symm

/-- The fragment is inhabited, and the smallest member is one the derived
compiler accepts too. -/
theorem compile_progSkip : compile (progOf .skipZero) = .ok imgSkip := backend_skipZero

theorem compile_progPrint (k : Int) (h1 : 1 ≤ k) (h2 : k ≤ 255) :
    compile (progOf (.printLit k)) = .ok (imgPrint k) := by
  have hs : shapeOf (progOf (.printLit k)) = some (.printLit k) := by
    show (if 1 ≤ k ∧ k ≤ 255 then some (Shape.printLit k) else none) = some (.printLit k)
    rw [if_pos ⟨h1, h2⟩]
  rw [compile, hs]
  exact backend_printLit k (by omega)

end BespokeSubleq

/-- **The hand-written backend as a verified compiler.**

A second inhabitant of `TurpentineCompiler SubleqLang`, next to
`derivedSubleq`. Its `compile` is the backend in
`Langlib/Languages/Turpentine/Compile/Subleq.lean`, restricted to the fragment this
file covers and otherwise unchanged; its `decodeOutput` reads the output
bytes as a base-256 numeral; and its `correct` field is the composition of
the reference-semantics lemmas with the twelve-instruction subleq
simulation. -/
def bespokeSubleq : TurpentineCompiler SubleqLang where
  compile := BespokeSubleq.compile
  encodeInput := Input.ofString ""
  decodeOutput := BespokeSubleq.decodeOutput
  correct := by
    intro p prog result n hc hp
    obtain ⟨sh, hsh, hprog⟩ := BespokeSubleq.compile_eq hc
    subst hprog
    rw [BespokeSubleq.progOf_shapeOf hsh] at hp
    cases sh with
    | skipZero =>
      obtain ⟨f, hf⟩ := BespokeSubleq.run_skip (Input.ofString "")
      refine ⟨f, ?_, ?_⟩
      · show (Langlib.Subleq.evalProg _ _ f).exit = _
        rw [show BespokeSubleq.imgOf .skipZero = BespokeSubleq.imgSkip from rfl, hf]
      · show BespokeSubleq.decodeOutput (Langlib.Subleq.evalProg _ _ f).output = _
        rw [show BespokeSubleq.imgOf .skipZero = BespokeSubleq.imgSkip from rfl, hf]
        rw [BespokeSubleq.haltsWith_progSkip hp]
        exact BespokeSubleq.decodeOutput_empty
    | printLit k =>
      obtain ⟨hk1, hk2⟩ := BespokeSubleq.printLit_range hsh
      have hres : (result : Int) = k := BespokeSubleq.haltsWith_progPrint hp
      obtain ⟨f, hf⟩ := BespokeSubleq.run_print k (Input.ofString "")
      refine ⟨f, ?_, ?_⟩
      · show (Langlib.Subleq.evalProg _ _ f).exit = _
        rw [show BespokeSubleq.imgOf (.printLit k) = BespokeSubleq.imgPrint k from rfl, hf]
      · show BespokeSubleq.decodeOutput (Langlib.Subleq.evalProg _ _ f).output = _
        rw [show BespokeSubleq.imgOf (.printLit k) = BespokeSubleq.imgPrint k from rfl, hf]
        rw [BespokeSubleq.decodeOutput_push,
          show k.emod 256 = k from Int.emod_eq_of_lt (by omega) (by omega)]
        simp only [Option.some.injEq]
        simp [Nat.toUInt8, UInt8.toNat, UInt8.ofNat]
        omega

/-- **The corollary the exercise is for.** `agree` was proved once in
`Derived.lean` against the specification `TurpentineHaltsWith`; instantiating
it at `bespokeSubleq` and `derivedSubleq` turns "the derived compiler is an
oracle for the hand-written one" from a testing practice into a theorem.

The two compiled programs are entirely different images and their decoders
are different functions, and neither fact enters the statement: what agrees
is the answer each run reports. -/
theorem bespokeSubleq_agrees_derived
    (p : Turpentine.Program) (prog₁ prog₂ : Langlib.Subleq.Prog) (result n : Nat)
    (h₁ : bespokeSubleq.compile p = .ok prog₁)
    (h₂ : derivedSubleq.compile p = .ok prog₂)
    (hp : TurpentineHaltsWith p n result) :
    ∃ m₁ m₂,
      (ProgLang.run (L := SubleqLang) prog₁ bespokeSubleq.encodeInput m₁).exit = Exit.halted ∧
      (ProgLang.run (L := SubleqLang) prog₂ derivedSubleq.encodeInput m₂).exit = Exit.halted ∧
      bespokeSubleq.decodeOutput
          (ProgLang.run (L := SubleqLang) prog₁ bespokeSubleq.encodeInput m₁).output =
        derivedSubleq.decodeOutput
          (ProgLang.run (L := SubleqLang) prog₂ derivedSubleq.encodeInput m₂).output :=
  CertifiedCompiler.agree bespokeSubleq derivedSubleq p prog₁ prog₂ result n h₁ h₂ hp

/-- **The corollary is not vacuous**, which is worth checking, because a
hypothesis of the form "both compilers accept `p`" is easy to state and, for
two compilers with disjoint fragments, impossible to satisfy.

`var answer: int;` with an empty body is in both fragments, and the two
agree on it. The overlap is exactly this narrow because the derived compiler
refuses every I/O statement (a URM has no output, so its answer is register
0 at halt) while this instance needs the answer printed. Widening it means
either verifying `printint` here or teaching the URM pass to compile
`printByte`. -/
theorem bespokeSubleq_agrees_derived_nonvacuous :
    ∃ (prog₁ prog₂ : Langlib.Subleq.Prog) (m₁ m₂ : Nat),
      bespokeSubleq.compile (BespokeSubleq.progOf .skipZero) = .ok prog₁ ∧
      derivedSubleq.compile (BespokeSubleq.progOf .skipZero) = .ok prog₂ ∧
      (ProgLang.run (L := SubleqLang) prog₁ bespokeSubleq.encodeInput m₁).exit = Exit.halted ∧
      (ProgLang.run (L := SubleqLang) prog₂ derivedSubleq.encodeInput m₂).exit = Exit.halted ∧
      bespokeSubleq.decodeOutput
          (ProgLang.run (L := SubleqLang) prog₁ bespokeSubleq.encodeInput m₁).output =
        derivedSubleq.decodeOutput
          (ProgLang.run (L := SubleqLang) prog₂ derivedSubleq.encodeInput m₂).output := by
  obtain ⟨prog₂, h₂⟩ :
      ∃ prog, derivedSubleq.compile (BespokeSubleq.progOf .skipZero) = .ok prog := ⟨_, rfl⟩
  have h₁ : bespokeSubleq.compile (BespokeSubleq.progOf .skipZero) =
      .ok BespokeSubleq.imgSkip := BespokeSubleq.compile_progSkip
  have hp : TurpentineHaltsWith (BespokeSubleq.progOf .skipZero) 1 0 := by
    refine ⟨(∅ : Std.HashMap String Turpentine.Value).insert "answer" (.int 0),
      { env := (∅ : Std.HashMap String Turpentine.Value).insert "answer" (.int 0),
        input := Input.ofString "" }, rfl, ?_, ?_⟩
    · simp [BespokeSubleq.progOf, Turpentine.exec]
    · simp [answerVar]
  obtain ⟨m₁, m₂, e₁, e₂, e₃⟩ :=
    bespokeSubleq_agrees_derived _ _ prog₂ 0 1 h₁ h₂ hp
  exact ⟨_, prog₂, m₁, m₂, h₁, h₂, e₁, e₂, e₃⟩

end Langlib.Turpentine.Certified
